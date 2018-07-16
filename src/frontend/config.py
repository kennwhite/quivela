from argparse import ArgumentParser

class Config():

    args = None

    @staticmethod
    def get_args():
        """Return command-line arguments"""
        return Config.args

    @staticmethod
    def set_args(args):
        Config.args = args

    @staticmethod
    def parse_args(args=None):
        ap = ArgumentParser()
        ap.add_argument("program", help="either (a) a path to a UC file, (b) a verbatim UC program, or (c) - to read from stdin")
        ap.add_argument("-k", "--keep-file", help="keep the backend output file", action="store_true")
        ap.add_argument("-e", "--expect", help="expectation for the final result")
        ap.add_argument("-v", "--verbose", help="print backend output", action="store_true")
        ap.add_argument("-b", "--backend", choices=["dafny", "rosette"], help="logical backend to use", default="dafny")
        ap.add_argument("--path", help="additional path to search for logical backend binaries (racket/dafny)")
        ap.add_argument("--no-precompile", help="don't precompile constant expressions (dafny)",
                        action="store_true")
        ap.add_argument("--consistency-checks", help="insert assertions to verify correctness of optimizations (dafny)", action="store_true")
        Config.args = ap.parse_args(args=args)

    @staticmethod
    def init_args():
        """Initialize command line argument structure to defaults (used to run tests)"""
        Config.parse_args(args=["unused.sbl"])
