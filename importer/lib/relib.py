import re
import unittest

reIPv4 = r"""(?:(?:25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9]?)\.){3}(?:25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9]?)"""
reIPv6 = r"""(?:[0-9a-f]{1,4}::?){0,7}(?:[0-9a-f]{1,4})?"""
reMAC = r"""(?:[0-9a-f]{2}:?){6}"""

reIPv4Bitmask = r"""(?:/\d\d?)?"""

reIPv4Netmask = reIPv4+reIPv4Bitmask


"""
  match - match object
  s - string
"""
def nonmatching_rest(match, s):
    (start, end) = match.span()
    return s[0:start] + s[end:]

"""
  finds all occurences of regex and also returns remaining string
  regex - compiled regular expression (re.compile)
  s - string to match on
  returns: tulpe of matches (list) and unmatched (string)
"""
def search_remove_all(regex, s):
    match = []
    m = regex.search(s)
    while m is not None:
        match.append(m.group())
        s = nonmatching_rest(m, s)
        m = regex.search(s)
    
    if match == []:
        return None
    return (match, s)


"""Unit test"""
class TestReLib(unittest.TestCase):
    def test_nonmatching_rest(self):
        p = re.compile('\d+')
        s = "this string has one (1) number"
        m = p.search(s)
        self.assertEqual(nonmatching_rest(m, s), "this string has one () number")
        
        s = "this string 456 has two (123) numbers"
        m = p.search(s)
        self.assertEqual(nonmatching_rest(m, s), "this string  has two (123) numbers")
        
        #re.match instead of re.search always matches on the complete string and does not make much sense in conjucntion with nonmatching_rest
        p = re.compile('.*\d+.*')
        m = p.match(s)
        self.assertEqual(nonmatching_rest(m, s), "")
        
        p = re.compile('(?:.*)(string \d+)(?:.*)')
        m = p.match(s)
        self.assertEqual(nonmatching_rest(m, s), "")
    
    def test_search_remove_all(self):
        p = re.compile('\d+')
        self.assertEqual(search_remove_all(p, "this string has no numbers"), None)
        
        self.assertEqual(search_remove_all(p, "this string 213 has two 123 numbers"), (['213', '123'], 'this string  has two  numbers'))
        
        p = re.compile(r'(?:dpt:\d+)')
        
    def test_extract_dpt(self):
        rule = """foobar state NEW tcp dpt:22flags: 0x17/0x02"""
        p = re.compile('dpt:(?P<port>\d+)')
        m = p.search(rule)
        self.assertTrue(m is not None)
        #the named match is just the number
        self.assertEqual(m.group('port'), '22')
        #the complete match is removed
        self.assertEqual(nonmatching_rest(m, rule), """foobar state NEW tcp flags: 0x17/0x02""")

if __name__ == '__main__':
    unittest.main()
