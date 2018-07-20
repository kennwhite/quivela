#lang rosette

; Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
; 
; Licensed under the Apache License, Version 2.0 (the "License").
; You may not use this file except in compliance with the License.
; A copy of the License is located at
; 
;     http://www.apache.org/licenses/LICENSE-2.0
; 
; or in the "license" file accompanying this file. This file is distributed 
; on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either 
; express or implied. See the License for the specific language governing 
; permissions and limitations under the License.

(require rosette/lib/match
         "lang.rkt" "print.rkt" "adversary.rkt" "indistinguishable.rkt" "log.rkt")
(require graph)

(provide update-fuel)

;; This module computes an upper bound on the fuel required by all methods in a
;; given program. If this computation is sound, then the results of the rosette
;; backend for this fuel parameter should be sound as well.

;; We compute this upper bound in two passes: first we collect the
;; cost of non-call expressions in a method body along with the calls
;; to other methods
(struct method-fuel-data (direct-cost method-calls) #:transparent)

;; A path identifies a method definition (syntactically)
;; A path is a list of PathElems
(struct PathElem () #:transparent)
(struct MethodName PathElem (name) #:transparent)

;; Top-level ENew expressions
(struct TopLevelNew PathElem (idx) #:transparent)

;; An field initialization of an ENew expression
(struct LocalInit PathElem (name) #:transparent)

;; We don't know which method exactly this call represents
(struct Unknown PathElem (name) #:transparent)

;; Collect all method calls occurring in an expression as a list of paths. This
;; is used to account for fuel cost of method calls in a second pass.
(define (collect-method-calls e immuts path)
  (let ([rec (lambda (e) (collect-method-calls e immuts path))])
    (match e
      [(EVar _) empty]
      [(EConst _) empty]
      [(ETuple es) (apply append (map rec es))]
      [(ECVar obj name idx) (append (rec obj) (rec idx))]
      [(ENew locals body) (apply append (rec body)
                                 (map (lambda (in) (rec (Init-val in)))
                                      locals))]
      [(EMethod _ _ _) empty]
      [(EAssign lhs rhs)
       (let ([rhs-calls (rec rhs)])
         (match lhs
           [(EVar x) rhs-calls]
           [(ECVar obj name idx) (append rhs-calls (rec obj)
                                         (rec idx))]
           [_ empty]))]
      [(ESeq e1 e2)
       (append (rec e1) (rec e2))]
      [(ECall obj name args)
       (apply append
              (rec obj)
              (match obj
                [(EVar x)
                 (debug "Call using variable ~v with immuts ~v~%" x immuts)
                 (if (member x immuts)
                     (list (append path (list (LocalInit x) (MethodName name))))
                     (list (list (Unknown name))))]
                [(EConst (Nil))
                 (if (equal? (Is_Builtin_Arity name) -1)
                     ;; FIXME: check if method exists in object, otherwise look for global method
                     (list (append path (list (MethodName name))))
                     empty)]
                [_ (Unknown name)])
              (map rec args))]
      [(EITE cnd thn els) (append (map rec (list cnd thn els)))]
      [(ENop) empty]
      [_ (error 'collect-method-calls "Unhandled expression: ~v" e)])))

(define (init-fuel-cost in)
  (max 1 (compute-direct-fuel (Init-val in))))

;; Computes the maximum fuel needed by all non-call expressions in e.
(define (compute-direct-fuel e)
  (match e
    [(EVar _) 1]
    [(EConst _) 1]
    [(ETuple es) (+ 1 (apply max (map compute-direct-fuel es)))]
    [(ESeq e1 e2) (+ 1 (max (compute-direct-fuel e1)
                            (compute-direct-fuel e2)))]
    [(ECVar obj name idx) (+ 1 (max (compute-direct-fuel obj)
                                    (compute-direct-fuel idx)))]
    [(ENew locals body) (+ 1 (apply max (compute-direct-fuel body)
                                    (map init-fuel-cost locals)))]
    [(EMethod _ _ _) 1]
    [(EAssign lhs rhs)
     (match lhs
       [(EVar x) (+ 1 (compute-direct-fuel rhs))]
       [(ECVar obj name idx)
        (+ 1 (apply max (map compute-direct-fuel (list rhs obj idx))))]
       [_ 1])]
    [(ECall obj name args)
     (+ 1 (apply max (compute-direct-fuel obj)
                 (map compute-direct-fuel args)))]
    [(EITE cnd thn els)
     (+ 1
        (max (compute-direct-fuel cnd) (compute-direct-fuel thn)
             (compute-direct-fuel els)))]
    [(ENop) 1]
    [_ (error 'compute-direct-fuel "unknown expression ~v" e)]))

;; Compute a map from paths in e to method-fuel-data structures
(define (compute-fuel-in-obj e fuel-map immuts path)
  (match e
    [(EMethod name args method-body)
     (hash-set! fuel-map (append path (list (MethodName name)))
                (method-fuel-data (compute-direct-fuel method-body)
                                  (collect-method-calls method-body
                                                        immuts
                                                        path)))]
    [(ESeq e1 e2)
     (compute-fuel-in-obj e1 fuel-map immuts path)
     (compute-fuel-in-obj e2 fuel-map immuts path)]
    [_ (error 'compute-fuel-in-obj "Unhandled expression ~v")]))

(define (collect-immuts inits)
  (map Init-name (filter Init-immutable? inits)))

(define (compute-obj-fuel e fuel-map immuts path)
  (match e
    [(ENew locals body)
     (let ([new-immuts (append immuts (collect-immuts locals))]) ;; FIXME: handle shadowing properly
       (map (lambda (loc)
              (compute-obj-fuel (Init-val loc) fuel-map new-immuts
                                (append path (list (LocalInit (Init-name loc))))))
            locals)
       (compute-fuel-in-obj body fuel-map new-immuts path))]
    ;; this pass only computes fuel information of methods, we assume there are no method
    ;; definitions inside other types of expressions
    [(EMethod _ _ _)
     (compute-fuel-in-obj e fuel-map immuts path)]
    [(ESeq e1 e2)
     (compute-obj-fuel e1 fuel-map immuts path)
     (compute-obj-fuel e2 fuel-map immuts path)]
    [_ empty]))

;; To ensure that there is no recursion (or mutual recursion), we convert the fuel-map to
;; a graph, then obtain a topological sorting, and insert update the fuel with the costs of
;; the functions lower in the call stack:
(define (fuel-map-to-call-graph fuel-map)
  (let ([graph (unweighted-graph/directed empty)])
    (hash-map fuel-map
     (lambda (meth fuel-data)
       (match fuel-data
         [(method-fuel-data _ calls)
          (map (lambda (call)
                 (when (Unknown? call)
                   (error 'fuel-map-to-call-graph
                          "function calls to unknown destinations not yet implemented"))
                 (log-debug "Adding egde: ~v -> ~v~n" meth call)
                 (add-directed-edge! graph meth call))
               calls)])))
    graph))

(define parameter-fuel 10)

;; Computes the total fuel cost in fuel-map by computing replacing method calls
;; with their fuel costs. Does not change fuel-map, and returns result as a new
;; map.
(define (add-method-call-fuel fuel-map)
  (let* ([graph (fuel-map-to-call-graph fuel-map)]
         [topsort (reverse (tsort graph))]
         [new-map (make-hash)])
    (map
     (lambda (meth)
       (if (hash-has-key? fuel-map meth)
           (match-let ([(method-fuel-data direct-cost calls) (hash-ref fuel-map meth)])
             (hash-set! new-map meth direct-cost)
             (map
              (lambda (call)
                (unless (hash-has-key? new-map call)
                  (error 'finalize-fuel-map "Cycle in call graph, can't compute fuel map: ~v" call))
                (hash-update! new-map meth
                              (lambda (cost) (+ cost (hash-ref new-map call)))))
              calls))
           ;; In this case, this method is a parameter about which we have some assumptions
           ;; It should be sound not to explore all possible expressions here since
           ;; we should only reason about it using assumptions.
           ;; TODO: figure out the exact conditions under which this is sound
           (hash-set! new-map meth parameter-fuel)))
     topsort)
    new-map))

(define (print-graph g)
  (map (lambda (edge) (display (format "~v -> ~v~n" (first edge) (second edge)))) (get-edges g)))

;; Computes the maximum fuel requirement of executing any method in expr or ctx0
(define (compute-fuel-req ctx0 expr)
  (unless (ENew? expr)
    (error 'compute-fuel-req "Computing fuel requirements only supported for top-level ENew expressions"))
  (let ([fuel-map (make-hash)])
    (compute-obj-fuel ctx0 fuel-map empty empty)
    (compute-obj-fuel expr fuel-map empty (list (TopLevelNew 0)))
    (let ([final-map (add-method-call-fuel fuel-map)])
      (apply max (hash-values final-map)))))

(define (update-fuel ctx0 lhs rhs)
  (define (handler excpn)
    (warn "Could not determine fuel cost statically, results might be unsound")
    (set-fuel! 20)
    #f)
  (with-handlers ([exn:fail? handler])
    (let ([fuel (max (compute-fuel-req ctx0 lhs) (compute-fuel-req ctx0 rhs))])
      (set-fuel! fuel)
      (info "Setting fuel parameter to ~v" fuel))))
