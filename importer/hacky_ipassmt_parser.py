#!/usr/bin/env python3
import sys
import argparse
import re
from lib.relib import *

#secondary?
p = re.compile(r'^\s+inet (?P<iprng>'+reIPv4Netmask+r')(:? brd '+reIPv4+r')? scope global (?P<iface>'+reIFACE+r')$')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('input', metavar='INPUT', type=str, help="Input file containing the output produced by `ip addr'")
    args = parser.parse_args()


    result = []

    with open(args.input, 'r') as fd:
        for line in fd:
            line = line.rstrip('\n')
            m = p.match(line)
            if m is not None:
                print(line)
                #print("`{}'".format(m.group('iprng')))
                #print(m.group('iface'))
                ip_parts, netlen = m.group('iprng').split('/')
                ip1, ip2, ip3, ip4 = ip_parts.split('.')
                result.append("(Iface ''{}'', [(ipv4addr_of_dotdecimal ({},{},{},{}), {})])".format(m.group('iface'), ip1, ip2, ip3, ip4, netlen))
    
    print("[{}]".format(",\n".join(result)))
            
