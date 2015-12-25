Haskell Tool
============


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
$ ./dist/build/iptables/iptables
```


## Example

Try this:

```
./dist/build/iptables/iptables -a ipassmt_tumi8 ../thy/Examples/TUM_Net_Firewall/iptables-save-2015-05-15_15-23-41_cheating
```
