Haskell Tool
============

FFFUU -- Fancy Formal Firewall Universal Understander

![FFFUU logo](http://i.imgur.com/qc4dNKl.png "FFFUU")

## Installation

Build uses `cabal` and supports the GHC 7.8.x and 7.10.x series.
To get started, use the following commands:

```
$ cabal update
$ cabal sandbox init
$ cabal install --only-dependencies
$ cabal build
```

With the last command, `cabal` produces a binary which can be invoked like this:

```
$ ./dist/build/fffuu/fffuu --help
```


## Example

Try this:

```
./dist/build/fffuu/fffuu --ipassmt ipassmt_tumi8 --rs ../thy/Examples/TUM_Net_Firewall/iptables-save-2015-05-15_15-23-41_cheating
```


We only support packet filtering, i.e. no packet modification. 
Consequently, we only officially support the `filter` table. 
If you like to live dangerously, you can try different tables. 
The tool will do a runtime check if everything in the requested table is supported. 
For example, spoofing protection can be done in the `raw` table. 
Try this: 

```
/dist/build/fffuu/fffuu --table raw --chain PREROUTING --ipassmt ipassmt_sqrl --rs ../thy/Examples/SQRL_Shorewall/2015_aug_iptables-save-spoofing-protection
```

## FAQ

Q: The tool doesn't show anything for my firewall.

A: Our tool loads the `filter` table and the `FORWARD` chain by default. If you have a host-based firewall, you may probably want to load the `INPUT` chain.

