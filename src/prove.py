# Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
# 
# Licensed under the Apache License, Version 2.0 (the "License").
# You may not use this file except in compliance with the License.
# A copy of the License is located at
# 
#     http://www.apache.org/licenses/LICENSE-2.0
# 
# or in the "license" file accompanying this file. This file is distributed 
# on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either 
# express or implied. See the License for the specific language governing 
# permissions and limitations under the License.

import logging
import os
import sys
from typing import Optional, Tuple

from frontend.program import Program
from frontend.dafny import DafnyRuntime
from frontend.rosette import RosetteRuntime
from frontend.config import Config


def prove(prog: str, keep=False, path: Optional[str]=None, backend_cls=DafnyRuntime) -> Tuple[bool, str]:
    p = Program(prog)

    backend = backend_cls(p)
    backend.collapse_top_level_exprs = False
    backend.output_path = os.path.dirname(os.path.realpath(__file__)) if keep else None
    if path is not None:
        backend.add_path(path)

    backend.compile(False)

    success, out, fname = backend.run(verbose=True)

    return success, fname


def main():
    Config.parse_args()
    args = Config.get_args()

    runtime = RosetteRuntime if args.backend == "rosette" else DafnyRuntime

    if args.verbose:
        logging.basicConfig(level=logging.INFO)

    if args.program == "-":
        sbl = sys.stdin.read()
        print("---")
    elif os.path.exists(args.program):
        with open(args.program) as f:
            sbl = f.read()
    else:
        sbl = args.program
    
    succ, fname = prove(sbl, keep=args.keep_file, path=args.path, backend_cls=runtime)

    if succ:
        print("Success!")
    else:
        print("FAILED!")
    
    if args.keep_file:
        print("  Script: " + fname)
    
    if args.verbose:
        with open(fname) as f:
            print("")
            print("Script:")
            print(f.read())
    
    sys.exit(0 if succ else 1)


if __name__ == "__main__":
    main()
