import sys
import re
import collections
        
from lib.firewall import *

import unittest


"""Unit test"""
class TestParse(unittest.TestCase):

    def setUp(self):
        ip = IP([1,2,3,4], None, False)
        self.dummy_rule = Rule(Std_Action.accept, Known_Proto.tcp, ip, ip, "")
    
    def test_parse_extra1(self):
        from lib.parse import parse_extra
        self.dummy_rule.extra = """foobar dpts:1:65535 state NEW tcp dpt:22flags: 0x17/0x02 multiport dports 22,80,873 foobar"""
        resultrule = parse_extra(self.dummy_rule)
        
        self.assertEqual(resultrule.action, self.dummy_rule.action)
        self.assertEqual(resultrule.proto, self.dummy_rule.proto)
        self.assertEqual(resultrule.ipsrc, self.dummy_rule.ipsrc)
        self.assertEqual(resultrule.ipdst, self.dummy_rule.ipdst)
        self.assertEqual(resultrule.extra, """foobar  state NEW tcp flags: 0x17/0x02  foobar""")
        self.assertEqual(resultrule.dports, [(22,22), (1,65535), (22,22), (80,80), (873,873)])
        
    def test_parse_extra2(self):
        from lib.parse import parse_extra
        self.dummy_rule.extra = """foobar dpts:1:65535 state NEW tcp dpt:22flags: 0x17/0x02 multiport dports 53,123,1000:2000,234,777:888 foobar"""
        resultrule = parse_extra(self.dummy_rule)
        
        self.assertEqual(resultrule.action, self.dummy_rule.action)
        self.assertEqual(resultrule.proto, self.dummy_rule.proto)
        self.assertEqual(resultrule.ipsrc, self.dummy_rule.ipsrc)
        self.assertEqual(resultrule.ipdst, self.dummy_rule.ipdst)
        self.assertEqual(resultrule.extra, """foobar  state NEW tcp flags: 0x17/0x02  foobar""")
        self.assertEqual(resultrule.dports, [(22,22), (1,65535), (53,53), (123,123), (1000,2000), (234,234), (777,888)])

if __name__ == '__main__':
    unittest.main()
