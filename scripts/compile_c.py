#!/usr/bin/env python3
"""Compile one C file through CompCert's frontend and the Lean compiler."""

import argparse
from pathlib import Path
import sys

from prototype import CompileError, REPO, compile_source


class PreprocessorOption(argparse.Action):
    def __call__(self, parser, namespace, value, option_string=None):
        setattr(namespace, self.dest, [*getattr(namespace, self.dest), value])
        namespace.preprocessor = [*namespace.preprocessor, option_string + value]


def parse_args(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    parser.set_defaults(preprocessor=[])
    parser.add_argument("source", type=Path)
    parser.add_argument("-o", dest="output", type=Path)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument("-S", dest="assembly", action="store_true")
    modes.add_argument("-c", dest="object", action="store_true")
    parser.add_argument("-I", dest="include", action=PreprocessorOption, default=[])
    parser.add_argument("-D", dest="define", action=PreprocessorOption, default=[])
    parser.add_argument("-U", dest="undefine", action=PreprocessorOption, default=[])
    parser.add_argument("-L", dest="library_path", action="append", default=[])
    parser.add_argument("-l", dest="library", action="append", default=[])
    parser.add_argument("-O", choices=["0"], default="0")
    parser.add_argument("--compcert-root", type=Path, default=REPO.parent / "CompCert")
    parser.add_argument("--keep-temps", action="store_true")
    options = parser.parse_args(argv)
    if options.output is None:
        options.output = Path(options.source.stem + (".s" if options.assembly else ".o")) if options.assembly or options.object else Path("a.out")
    return options


def main():
    try:
        options = parse_args()
        folder = compile_source(options)
        if options.keep_temps:
            print(f"Artifacts: {folder}")
        return 0
    except (CompileError, OSError) as error:
        print(f"compile_c: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
