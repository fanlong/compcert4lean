#!/usr/bin/env python3
"""Compile and link C, assembly, objects and libraries through Lean (x86-64)."""

import argparse
from pathlib import Path
import sys

from prototype import CompileError, REPO, compile_source


class PreprocessorOption(argparse.Action):
    def __call__(self, parser, namespace, value, option_string=None):
        setattr(namespace, self.dest, [*getattr(namespace, self.dest), value])
        namespace.preprocessor = [*namespace.preprocessor, option_string + value]


class OrderedInput(argparse.Action):
    def __call__(self, parser, namespace, value, option_string=None):
        item = ("input", value) if option_string == "--input" else (
            "argument", value if option_string == "--link-arg" else option_string + value)
        namespace.inputs = [*namespace.inputs, item]


LANGUAGE_OPTIONS = ["longdouble", "struct-passing", "vararg-calls", "unprototyped",
                    "packed-structs", "unstructured-switch", "inline-asm"]


def parse_args(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    parser.set_defaults(preprocessor=[], inputs=[], language=[])
    parser.add_argument("--input", action=OrderedInput, help=argparse.SUPPRESS)
    parser.add_argument("--link-arg", action=OrderedInput, help=argparse.SUPPRESS)
    parser.add_argument("-o", dest="output", type=Path)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument("-S", dest="assembly", action="store_true")
    modes.add_argument("-c", dest="object", action="store_true")
    parser.add_argument("-I", dest="include", action=PreprocessorOption, default=[])
    parser.add_argument("-D", dest="define", action=PreprocessorOption, default=[])
    parser.add_argument("-U", dest="undefine", action=PreprocessorOption, default=[])
    parser.add_argument("-L", action=OrderedInput)
    parser.add_argument("-l", action=OrderedInput)
    parser.add_argument("-O", choices=["0", "1", "2", "3"], default="0")
    parser.add_argument("-std", choices=["c99", "c11", "c18"], default="c99")
    parser.add_argument("-shared", action="store_true")
    parser.add_argument("-r", dest="relocatable", action="store_true")
    parser.add_argument("-fpic", "-fPIC", dest="pic", action="store_true")
    parser.add_argument("-fno-pic", "-fno-PIC", dest="pic", action="store_false")
    parser.add_argument("-fcommon", dest="common", action="store_true")
    parser.add_argument("-fno-common", dest="common", action="store_false")
    parser.set_defaults(pic=False, common=False)
    for option in ["all", "none", *LANGUAGE_OPTIONS,
                   *("no-" + name for name in LANGUAGE_OPTIONS)]:
        parser.add_argument("-f" + option, dest="language", action="append_const", const="-f" + option)
    parser.add_argument("--compcert-root", type=Path, default=REPO.parent / "CompCert")
    parser.add_argument("--keep-temps", action="store_true")
    parser.add_argument("--compile-timeout", type=float, default=300)
    parser.add_argument("--link-timeout", type=float, default=300)
    normalized = []
    arguments = iter(sys.argv[1:] if argv is None else argv)
    for argument in arguments:
        if argument == "--":
            normalized.extend("--input=" + value for value in arguments)
        elif argument == "-O":
            normalized.append("-O2")
        elif argument.startswith("-Wl,"):
            normalized.append("--link-arg=" + argument)
        elif argument.startswith("-"):
            normalized.append(argument)
            if argument in {"-o", "-I", "-D", "-U", "-L", "-l", "-std", "--compcert-root",
                            "--compile-timeout", "--link-timeout"}:
                value = next(arguments, None)
                if value is None:
                    parser.error(f"{argument} requires a value")
                normalized.append(value)
        else:
            normalized.append("--input=" + argument)
    options = parser.parse_args(normalized)
    options.optimization = "O0" if options.O == "0" else "O2"
    sources = [Path(value) for kind, value in options.inputs if kind == "input"]
    if not sources:
        parser.error("at least one input file is required")
    options.source = sources[0]
    if options.compile_timeout <= 0 or options.link_timeout <= 0:
        parser.error("timeouts must be positive")
    if sum([options.shared, options.relocatable, options.assembly or options.object]) > 1:
        parser.error("-shared, -r and -c/-S are mutually exclusive")
    if options.output is not None and len(sources) > 1 and (options.assembly or options.object):
        parser.error("-o with multiple inputs is ambiguous in -c/-S mode")
    if options.output is None and not (options.assembly or options.object):
        options.output = Path("a.out")
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
