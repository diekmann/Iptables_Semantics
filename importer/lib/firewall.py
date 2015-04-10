from collections import namedtuple
from enum import Enum

from lib.serialize import HOL
from lib.util import trace

Rule = namedtuple("Rule", ["action", "proto", "ipsrc", "ipdst", "extra"]) # possible additional attrs: "sports", "dports"
Std_Chain = namedtuple("Std_Chain", ["policy", "rules"])

class Ports(object):
    def __init__(self, ports):
        assert type(ports) is list
        for (start,end) in ports:
            assert type(start) is int
            assert type(end) is int
            assert start <= end
            assert start >= 0
            assert end >= 0
        self.ports = ports

    def raw_serialize(self, serializer):
        ports = [serializer.tup(serializer.word(start), serializer.word(end)) for (start,end) in self.ports]
        return serializer.list(ports, newline=False)

class SPorts(Ports):
    def serialize(self, serializer):
        return serializer.constr("Match", serializer.constr("Src_Ports", self.raw_serialize(serializer)))

class DPorts(Ports):
    def serialize(self, serializer):
        return serializer.constr("Match", serializer.constr("Dst_Ports", self.raw_serialize(serializer)))

class Src_Or_Dst(Enum):
    src = 1
    dst = 2

    def serialize(self):
        table = {
            Src_Or_Dst.src: "Src",
            Src_Or_Dst.dst: "Dst"
        }

        return table[self]


class IP:
    def __init__(self, parts, bitmask, invert):
        assert len(parts) is 4
        assert type(bitmask) is int or bitmask is None, "type of bitmask expected int or None, got %r" % bitmask
        assert type(invert) is bool
        self.parts = parts
        self.bitmask = bitmask
        self.invert = invert

    def serialize(self, src_or_dest, serializer):
        raw = serializer.ipv4(*self.parts)
        
        if self.bitmask is not None:
            addr = serializer.constr("Ip4AddrNetmask", raw, serializer.nat(self.bitmask))
        else:
            addr = serializer.constr("Ip4Addr", raw)

        expr = serializer.constr("Match", serializer.constr(src_or_dest.serialize(), addr))

        if self.invert:
            expr = serializer.constr("MatchNot", expr)

        return expr


class Proto:
    def serialize(self, serializer):
        return serializer.constr("Match", self.raw_serialize(serializer))

class Known_Proto(Proto, Enum):
    tcp = 1
    udp = 2
    all = 3

    def raw_serialize(self, serializer):
        table = {
            Known_Proto.tcp: "Proto TCP",
            Known_Proto.udp: "Proto UDP",
            Known_Proto.all: "ProtoAny"
        }

        return serializer.constr("Prot", table[self])

class Unknown_Proto(Proto):
    def __init__(self, proto):
        assert type(proto) == str
        self.proto = proto

    def raw_serialize(self, serializer):
        return serializer.constr("Extra", serializer.string("Prot {0}".format(self.proto)))


class Action:
    def serialize(self, chain_names, serializer):
        pass

class Std_Action(Action, Enum):
    accept = 1
    drop = 2
    log = 3
    reject = 4
    ret = 5
    empty = 6
    unknown = 7

    def serialize(self, chain_names, serializer):
        table = {
            Std_Action.accept: "Accept",
            Std_Action.drop: "Drop",
            Std_Action.log: "Log",
            Std_Action.reject: "Reject",
            Std_Action.ret: "Return",
            Std_Action.empty: "Empty",
            Std_Action.unknown: "Unknown"
        }
        action = table[self]
        return serializer.action(action)

class Custom_Action(Action):
    def __init__(self, action):
        assert type(action) == str
        self.action = action

    def serialize(self, chain_names, serializer):
        if self.action in chain_names:
            return serializer.constr("Call", serializer.string(self.action))
        else:
            return "Unknown"


class Rule(object):
    def __init__(self, action, proto, ipsrc, ipdst, extra):
        assert isinstance(action, Action)
        assert isinstance(proto, Proto)
        assert isinstance(ipsrc, IP)
        assert isinstance(ipdst, IP)
        self.action = action
        self.proto = proto
        self.ipsrc = ipsrc
        self.ipdst = ipdst
        self.extra = extra

    def __combine_MatchAnd(self, serializer, ls):
        ls = [l for l in ls if l is not None]
        if len(ls) == 0:
            return "MatchAny"
        elif len(ls) == 1:
            return ls[0]
        elif len(ls) == 2:
            return serializer.constr("MatchAnd", ls[0], ls[1])
        else:
            return serializer.constr("MatchAnd", ls[0], self.__combine_MatchAnd(serializer, ls[1:]))
            

    def serialize(self, chain_names, serializer):
        action = self.action.serialize(chain_names, serializer)
        proto = self.proto.serialize(serializer)
        ipsrc = self.ipsrc.serialize(Src_Or_Dst.src, serializer)
        ipdst = self.ipdst.serialize(Src_Or_Dst.dst, serializer)
        
        sports = None
        if hasattr(self, 'sports'):
            assert isinstance(self.sports, SPorts)
            sports = self.sports.serialize(serializer)

        dports = None
        if hasattr(self, 'dports'):
            assert isinstance(self.dports, DPorts)
            dports = self.dports.serialize(serializer)
        
        if self.extra is None or self.extra == "":
            extra = "MatchAny" #TODO: is setting to None better code?
        else:
            extra = serializer.constr("Match", serializer.constr("Extra", serializer.string(self.extra)))

        raw = self.__combine_MatchAnd(serializer, [ipsrc, ipdst, proto, sports, dports, extra])

        return serializer.constr("Rule", raw, action)


class Firewall(object):
    std_chain_names = ['INPUT', 'FORWARD', 'OUTPUT']

    def __init__(self, std_chains, custom_chains):
        self.std_chains = std_chains
        self.custom_chains = custom_chains

    def __serialize_action(self, action, serializer):
        return action.serialize(self.custom_chains.keys(), serializer)

    def __serialize_rule(self, rule, serializer):
        return rule.serialize(self.custom_chains.keys(), serializer)

    def serialize(self, serializer):
        chain_names = self.custom_chains.keys()
        chains = []

        for name, chain in self.custom_chains.items():
            rules = [rule.serialize(chain_names, serializer) for rule in chain]
            chains.append((serializer.string(name), serializer.list(rules)))

        for name, chain in self.std_chains.items():
            rules = [rule.serialize(chain_names, serializer) for rule in chain.rules]
            rules.append(serializer.constr("Rule", "MatchAny", chain.policy.serialize(chain_names, serializer)))
            chains.append((serializer.string(name), serializer.list(rules)))

        return serializer.definition("firewall_chains", serializer.map(chains))
