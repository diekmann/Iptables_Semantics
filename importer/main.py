#!/usr/bin/env python3
import sys
import argparse
from os.path import basename

from lib.util import *
from lib.parse import parse_firewall
from lib.serialize import *

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('input', metavar='INPUT', type=str, help="Input file containing the output produced by `iptables -Ln'")
    parser.add_argument('output', metavar='OUTPUT', type=str, help="Output file where the generated code will be written to")
    parser.add_argument('--type', '-t', dest='typ', metavar='TYPE', type=str, default='hol', choices=['hol', 'ml', 'scala'], help="Output type (choices: hol, ml, scala; default: hol)")
    parser.add_argument('--module', '-m', dest='module', metavar='NAME', type=str, default=None, help="Module name (if unspecified, guessed from output file name)")
    parser.add_argument('--import', '-i', dest='import_module', metavar='NAME', type=str, default=None, help="Module name to import from (if none, nothing is imported)")
    args = parser.parse_args()

    if args.module is None:
        args.module = basename(args.output).split(".")[0]
        warn("Unspecified module name, guessing `{}'".format(args.module))

    if args.import_module is None:
        warn("No import module is specified")

    mapping = {
        'hol': HOL,
        'ml': ML,
        'scala': Scala
    }

    if args.typ in mapping:
        serializer = mapping[args.typ](args.module, args.import_module)
        if not (args.typ == 'ml'):
            warn("Using experimental serializer")
    else:
        error("Unknown type", fatal = True)

    result = parse_firewall(args.input).serialize(serializer)

    with open(args.output, 'w') as fd:
        fd.write(serializer.header())
        fd.write(result)
        fd.write(serializer.footer())
