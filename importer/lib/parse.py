import sys
import re
import collections

from lib.relib import *
from lib.util import notice, error
from lib.firewall import *

class ParseError(Exception):
    pass

def parse_std_chain_hdr(line):
    """Parses the header of a default chain"""

    reChainHdr = re.compile(r"""^Chain (\w+) \(policy ((?:ACCEPT|DROP))\)$""")
    m = re.match(reChainHdr, line)
    if not m: raise ParseError

    return (m.group(1), m.group(2))

def parse_custom_chain_hdr(line):
    """Parses the header of a custom chain"""

    reChainHdr = re.compile(r"""^Chain ([\w\-~]+) \(\d+ references\)$""")
    m = re.match(reChainHdr, line)
    if not m:
        print("parse_custom_chain_hdr: invalid header: `%s'" % line)
        raise ParseError

    return m.group(1)

def check_chain_hdrdesc(line):
    """Checks the 'table header' of a chain"""

    line = line.strip()
    r = re.compile(r"""^target (\ +) prot opt source (\ +) destination""")
    m = re.match(r, line)
    if not m: raise ParseError

    return m

def parse_ip(ip):
    r = re.compile(r"""^
        (?P<not>!)?                 # NOT
        (?P<ip>"""+reIPv4+r""")  # ip
        (?:/(?P<bitmask>\d\d?))?
        $""", re.X)
    m = re.match(r, ip)

    if not m or not m.group('ip'): raise ParseError
    
    parts = m.group('ip').split('.')
    if len(parts) != 4: raise ParseError

    if m.group('bitmask'):
        bitmask = int(m.group('bitmask'))
    else:
        bitmask = None

    invert = bool(m.group('not'))

    return IP(parts, bitmask, invert)

def parse_proto(proto):
    mapping = {
        'tcp': Known_Proto.tcp,
        'udp': Known_Proto.udp,
        'all': Known_Proto.all
    }

    return mapping[proto] if proto in mapping else Unknown_Proto(proto)

def parse_action(action):
    if action is None:
        return Std_Action.empty

    if ' ' in action: raise ParseError

    mapping = {
        'ACCEPT': Std_Action.accept,
        'DROP': Std_Action.drop,
        'LOG': Std_Action.log,
        'REJECT': Std_Action.reject,
        'QUEUE': Std_Action.unknown,
        'RETURN': Std_Action.ret
    }

    # could as well be a call to a custom chain, but we don't know yet
    return mapping[action] if action in mapping else Custom_Action(action)

def parse_rule(line):
    """Parses a single rule"""
    if line == "" or line == '\n':
        return None
    
    r = re.compile(r"""^
        (?P<action>[\w\-~]+)?        #action, may be empty
        \ *                     #spaces 
        (?P<proto>(?:\w\w\w\w?)|(?:\d\d)|(?:\d))    # 3-4 char proto, tcp,udp,esp,sctp,... or some strange number
        \ ? \ ? \ ? \ -- \ \ ?
        (?P<ipsrc>!?"""+reIPv4Netmask+r""")  # ip src including /xx An ip address might be negated with a !
        \ +
        (?P<ipdst>!?"""+reIPv4Netmask+r""")
        (?P<extra>\ [\w \*\!\./:%,\[\]\-"]+)?   # any extra options, please strip leading whitespaces
        $""", re.X)
    m = re.match(r, line)
    if not m:
        raise ParseError
    
    extra = m.group('extra')
    if extra:
        extra = m.group('extra').strip()
        if extra is "":
            extra = None

    action = parse_action(m.group('action'))
    proto = parse_proto(m.group('proto'))
    ipsrc = parse_ip(m.group('ipsrc'))
    ipdst = parse_ip(m.group('ipdst'))
    
    return Rule(action, proto, ipsrc, ipdst, extra)

def parse_rules(fd):
    """Parses a list of rules until an empty line is reached"""

    result = []
    while True:
        line = fd.readline()
        line = line.strip()
        if not line:
            break
        try:
            rule = parse_rule(line)
        except (ParseError, AssertionError):
            error("Parsing rule `{0}' failed".format(line))
            raise
        result.append(rule)
    return result

def parse_std_chain(fd, name):
    """Parses a single complete standard chain; namely INPUT, OUTPUT, FORWARD"""

    line = fd.readline()
    (name0, policy) = parse_std_chain_hdr(line)

    assert name == name0
    
    line = fd.readline()
    check_chain_hdrdesc(line)
    
    rules = parse_rules(fd)
    return (policy, rules)

def parse_custom_chain(fd):
    """Parses a single complete custom chain; returns None if the input file is exhausted"""

    line = fd.readline()
    line = line.strip()
    if not line:
        return None

    chain = parse_custom_chain_hdr(line)
    assert chain != ""
    
    line = fd.readline()
    check_chain_hdrdesc(line)
    
    rules = parse_rules(fd)
    return (chain, rules)

def parse_firewall(filename):
    std_chains = collections.OrderedDict()
    custom_chains = collections.OrderedDict()
    
    with open(filename, 'r') as fd:
        for chain in Firewall.std_chain_names:
            (policy, rules) = parse_std_chain(fd, chain)
            std_chains[chain] = Std_Chain(policy = parse_action(policy), rules = rules)

        while True:
            res = parse_custom_chain(fd)
            if not res:
                break
            (chain, rules) = res
            custom_chains[chain] = rules

    firewall = Firewall(std_chains = std_chains, custom_chains = custom_chains)
    count = sum([len(chain.rules) for chain in std_chains.values()]) + sum([len(chain) for chain in custom_chains.values()])

    notice("Parsed {0} rules".format(count))

    return firewall
