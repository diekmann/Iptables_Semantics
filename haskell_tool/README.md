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

```
FFFUU -- Fancy Formal Firewall Universal Understander

Usage: fffuu [--ipassmt STRING] [--table STRING] [--chain STRING] --rs STRING

Available options:
  -h,--help                Show this help text
  --ipassmt STRING         Optional path to an IP assignment file. If not
                           specified, it only loads `lo = [127.0.0.0/8]`.
  --table STRING           The table to load for analysis. Default: `filter`.
                           Note: This tool does not support pcket modification,
                           so loading tables such as `nat` will most likeley
                           fail.
  --chain STRING           The chain to start the analysis. Default: `FORWARD`.
                           Use `INPUT` for a host-based firewall.
  --rs STRING              Path to the `iptables-save` output.
```

## Usage

Load the output of `iptables-save` into our tool. 
The tool will dump lots of information about your ruleset. 

```
./dist/build/fffuu/fffuu --rs /path/to/iptables-save.txt
```


To improve the analysis, you can provide an IP assignment file. 
This optional file describes which source ip ranges are expected on a certain interfaces. 
For example: 

```
lo = [127.0.0.0/8]
```


## Example

Try this:

```
./dist/build/fffuu/fffuu --rs ../thy/Examples/Parser_Test/data/iptables-save
```
This example file is a nonsense config we use to stress the parser.

Example: 
[Input](../thy/Examples/Parser_Test/data/iptables-save) / [Output (pastebin)](http://pastebin.com/u89npf1g)

---------------------------------------


Try this:

```
./dist/build/fffuu/fffuu --ipassmt ipassmt_tumi8 --rs ../thy/Examples/TUM_Net_Firewall/iptables-save-2015-05-15_15-23-41_cheating
```

This will generate lots of output.

---------------------------------------


We only support packet filtering, i.e. no packet modification. 
Consequently, we only officially support the `filter` table. 
If you like to live dangerously, you can try different tables. 
The tool will do a runtime check if everything in the requested table is supported. 
For example, spoofing protection can be done in the `raw` table. 
Try this: 

```
./dist/build/fffuu/fffuu --table raw --chain PREROUTING --ipassmt ipassmt_sqrl --rs ../thy/Examples/SQRL_Shorewall/2015_aug_iptables-save-spoofing-protection
```

## FAQ

Q: The tool doesn't show anything for my firewall.

A: Our tool loads the `filter` table and the `FORWARD` chain by default. If you have a host-based firewall, you may probably want to load the `INPUT` chain.

