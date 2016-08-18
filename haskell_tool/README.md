Haskell Tool
============

FFFUU -- Fancy Formal Firewall Universal Understander

![FFFUU logo](http://i.imgur.com/qc4dNKl.png "FFFUU")


[![Build Status](https://travis-ci.org/diekmann/Iptables_Semantics.svg)](https://travis-ci.org/diekmann/Iptables_Semantics)

## Precompiled Binaries

A pre-compiled binary of `fffuu` for IPv4 and `fffuu6` for IPv6 can be obtained from [Bintray](https://bintray.com/fffuu/binaries/nightly/nightly/view). 
A new binary is created on every push to master.


---------------------------------------

If you have trust issues with binaries, you can confine `fffuu` with AppArmor.
`fffuu` only requires read access to the data you want to analyze (and nothing more).
For example, given you saved `fffuu` to `/home/diekmann/Downloads`, you can put [my apparmor profile](apparmor_home.diekmann.Downloads.fffuu) to `/etc/apparmor.d/home.diekmann.Downloads.fffuu` and enforce it.
Tested on Ubuntu 14.04.

## Building from Source

Build uses `cabal` and supports the GHC 7.8.x, 7.10.x, and 8.0.1 series.
Stack support is available.
To get started, use the following commands:

```
$ cabal update
$ cabal sandbox init
$ cabal install --only-dependencies --enable-tests
$ cabal build
```

With the last command, `cabal` produces a binary which can be invoked like this:

```
$ ./dist/build/fffuu/fffuu --help
```

```
FFFUU -- Fancy Formal Firewall Universal Understander

Usage: fffuu [--verbose] [--ipassmt STRING] [--table STRING] [--chain STRING]
             [--service_matrix_sport INTEGER] [--service_matrix_dport INTEGER]
             STRING

Available options:
  -h,--help                Show this help text
  --verbose                Show verbose debug output (for example, of the
                           parser).
  --ipassmt STRING         Optional path to an IP assignment file. If not
                           specified, it only loads `lo = [127.0.0.0/8]`.
  --table STRING           The table to load for analysis. Default: `filter`.
                           Note: This tool does not support packet modification,
                           so loading tables such as `nat` will most likeley
                           fail.
  --chain STRING           The chain to start the analysis. Default: `FORWARD`.
                           Use `INPUT` for a host-based firewall.
  --service_matrix_sport INTEGER
                           Source port for the service matrix. If not specified,
                           the randomly chosen source port 10000 is used. TODO:
                           maybe use an ephemeral port ;-).
  --service_matrix_dport INTEGER
                           Destination port for the service matrix. If not
                           specified, SSH and HTTP (22 and 80) will be used.
                           Argument may be repeated multiple times.
  -h,--help                Show this help text
  STRING                   Required: Path to `iptables-save` output. This is the
                           input for this tool.
```

## Usage

Load the output of `iptables-save` into our tool. 
The tool will dump lots of information about your ruleset. 

```
./dist/build/fffuu/fffuu /path/to/iptables-save.txt
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
./dist/build/fffuu/fffuu ../thy/Iptables_Semantics/Examples/Parser_Test/data/iptables-save --verbose
```
This example file is a nonsense config we use to stress the parser.

Example: 
[Input](../thy/Iptables_Semantics/Examples/Parser_Test/data/iptables-save) / [Output](test/Suites/GoldenFiles/parser_test)

---------------------------------------


Try this:

```
./dist/build/fffuu/fffuu --ipassmt ipassmt_tumi8 ../thy/Iptables_Semantics/Examples/TUM_Net_Firewall/iptables-save-2015-05-15_15-23-41_cheating
```

This will generate lots of output.

If you visualize the service matrix for ssh with your favorite graph visualization tool, you will see something similar to [this (png on imgur)](http://imgur.com/cKPOyAQ). `fffuu` gives you the minimal graph representation. Yes, the access matrix is really that complicated. This is the intrinsic complexity of this firewall, just check the 5k rules by hand ;-)

---------------------------------------


We only support packet filtering, i.e. no packet modification. 
Consequently, we only officially support the `filter` table. 
If you like to live dangerously, you can try different tables. 
The tool will do a runtime check if everything in the requested table is supported. 
For example, spoofing protection can be done in the `raw` table. 
Try this: 

```
./dist/build/fffuu/fffuu --table raw --chain PREROUTING --ipassmt ipassmt_sqrl ../thy/Iptables_Semantics/Examples/SQRL_Shorewall/2015_aug_iptables-save-spoofing-protection
```

[Output](test/Suites/GoldenFiles/sqrl_2015_aug_iptables-save-spoofing-protection) (featuring the `--verbose` flag)


### Small Example

The `fffuu` tool is really useful for network firewalls (e.g. on your perimeter router). Here is a contrived example (compiled from many real-world rule sets):
```
*filter
:INPUT DROP [0:0]
:FORWARD DROP [0:0]
:OUTPUT DROP [0:0]
:DOS_PROTECT - [0:0]
:GOOD~STUFF - [0:0]
-A FORWARD -j DOS_PROTECT
-A FORWARD -j GOOD~STUFF
-A FORWARD -p tcp -m multiport ! --dports 80,443,6667,6697 -m hashlimit --hashlimit-above 10/sec --hashlimit-burst 20 --hashlimit-mode srcip --hashlimit-name aflood --hashlimit-srcmask 8 -j LOG
-A FORWARD ! -i lo -s 127.0.0.0/8 -j DROP
-A FORWARD -i inteneral -s 131.159.21.0/24 -j ACCEPT
-A FORWARD -s 131.159.15.240/28 -d 131.159.21.0/24 -j DROP
-A FORWARD -p tcp -d 131.159.15.240/28 -j ACCEPT
-A FORWARD -i dmz -p tcp -s 131.159.15.240/28 -j ACCEPT
-A GOOD~STUFF -i lo -j ACCEPT
-A GOOD~STUFF -m state --state ESTABLISHED -j ACCEPT
-A GOOD~STUFF -p icmp -m state --state RELATED -j ACCEPT
-A DOS_PROTECT -i eth1 -p icmp -m icmp --icmp-type 8 -m limit --limit 1/sec -j RETURN
-A DOS_PROTECT -i eth1 -p icmp -m icmp --icmp-type 8 -j DROP
COMMIT
```

What does the ruleset do? The service matrix looks as follows:

```
a |-> {131.159.21.0 .. 131.159.21.255}
b |-> {131.159.15.240 .. 131.159.15.255}
c |-> {127.0.0.0 .. 127.255.255.255}
d |-> {0.0.0.0 .. 126.255.255.255} u {128.0.0.0 .. 131.159.15.239} u {131.159.16.0 .. 131.159.20.255} u {131.159.22.0 .. 255.255.255.255}

(a,a)
(a,b)
(a,c)
(a,d)
(b,b)
(b,c)
(b,d)
(c,a)
(c,b)
(c,c)
(c,d)
(d,b)
```

Let’s visualize this:
![fffuu dmz example hosted on imgur](https://i.imgur.com/Pqudris.png “hosted on imgur”)

Ignore the 127.0.0.0/8 range at the bottom. We can see that the firewall implements the textbook DMZ architecture: Internet (cloud) on the top, internal machines on the left, servers (DMZ) on the right. Yay!

### Longer Example
We will analyze the ruleset of a NAS. 
The NAS runs a host-based firewall, so we are interested in the `INPUT` chain. 
Here is the ruleset:

```
*filter
:INPUT ACCEPT [0:0]
:FORWARD ACCEPT [0:0]
:OUTPUT ACCEPT [1745:334865]
:DEFAULT_INPUT - [0:0]
:DOS_PROTECT - [0:0]
-A INPUT -j DOS_PROTECT
-A INPUT -j DEFAULT_INPUT
-A DEFAULT_INPUT -i lo -j ACCEPT
-A DEFAULT_INPUT -m state --state RELATED,ESTABLISHED -j ACCEPT
-A DEFAULT_INPUT -p tcp -m tcp --dport 22 -j ACCEPT
-A DEFAULT_INPUT -p tcp -m multiport --dports 873,3260,3261,3262,3240:3259,21,548,111,892,2049,443,80,3493,3306 -j DROP
-A DEFAULT_INPUT -p tcp -m multiport --dports 22,23 -j DROP
-A DEFAULT_INPUT -p udp -m multiport --dports 68,67,123,514,19999,5353,161,111,892,2049 -j DROP
-A DEFAULT_INPUT -s 192.168.0.0/16 -j ACCEPT
-A DEFAULT_INPUT -j DROP
-A DEFAULT_INPUT -i eth0 -j DROP
-A DOS_PROTECT -i eth1 -p icmp -m icmp --icmp-type 8 -m limit --limit 1/sec -j RETURN
-A DOS_PROTECT -i eth1 -p icmp -m icmp --icmp-type 8 -j DROP
-A DOS_PROTECT -i eth1 -p tcp -m tcp --tcp-flags FIN,SYN,RST,ACK RST -m limit --limit 1/sec -j RETURN
-A DOS_PROTECT -i eth1 -p tcp -m tcp --tcp-flags FIN,SYN,RST,ACK RST -j DROP
-A DOS_PROTECT -i eth1 -p tcp -m tcp --tcp-flags FIN,SYN,RST,ACK SYN -m limit --limit 10000/sec --limit-burst 100 -j RETURN
-A DOS_PROTECT -i eth1 -p tcp -m tcp --tcp-flags FIN,SYN,RST,ACK SYN -j DROP
-A DOS_PROTECT -i eth0 -p icmp -m icmp --icmp-type 8 -m limit --limit 1/sec -j RETURN
-A DOS_PROTECT -i eth0 -p icmp -m icmp --icmp-type 8 -j DROP
-A DOS_PROTECT -i eth0 -p tcp -m tcp --tcp-flags FIN,SYN,RST,ACK RST -m limit --limit 1/sec -j RETURN
-A DOS_PROTECT -i eth0 -p tcp -m tcp --tcp-flags FIN,SYN,RST,ACK RST -j DROP
-A DOS_PROTECT -i eth0 -p tcp -m tcp --tcp-flags FIN,SYN,RST,ACK SYN -m limit --limit 10000/sec --limit-burst 100 -j RETURN
-A DOS_PROTECT -i eth0 -p tcp -m tcp --tcp-flags FIN,SYN,RST,ACK SYN -j DROP
COMMIT
```

The NAS has the following interesting services:

  * ssh - TCP port 22. For management purposes, was enabled for an update, should be blocked now.
  * http - TCP port 80. Should be blocked, there should not be any service listening.
  * http - TCP port 8080. The management web interface. Should only be accessible from the local LAN.

We run the following:

```
./dist/build/fffuu/fffuu --chain INPUT --service_matrix_dport 22 --service_matrix_dport 8080 --service_matrix_dport 80 ../thy/Iptables_Semantics/Examples/Synology_Diskstation_DS414/iptables-save_jun_2015_cleanup
```

[Output](test/Suites/GoldenFiles/synology_iptables-save_jun_2015_cleanup) (featuring the `--verbose` flag)


We did not specify an `ipassmt`.
The tool tells us: 
```
WARNING: no IP assignment specified, loading a generic file
```
This means, the tool only assumes that `lo` corresponds to `127.0.0.0/8`, but nothing more. 
But the ruleset also matches on `eth0` and `eth1`. 
The tool has no information about these interfaces, it will do a sound overapproximation. 
The result will be sound, but chances are, that the tool assumes that the firewall permits too much. 
Note: Assuming that the firewall (in doubts) permits too much is the conservative approach when verifying that the firewall actually *blocks* the right things.
If you want better results, provide the valid source IP address ranges for the interfaces. 
In this example, we are fine. 
If you do heavy matching on `-i` in your ruleset, you may want to specify an `ipassmt` to improve accuracy of the results.


To simplify the ruleset, `fffuu` abstracts over all match conditions which are not essential for our analysis. 
It does an overapproximation, that means, it answers the question "*which packets might be potentially allowed by the firewall?*". 
Here is the simplified, abstracted ruleset (in *pseudo* iptables -L -n format): 
```
ACCEPT     all  --  0.0.0.0/0            0.0.0.0/0    in: lo   
ACCEPT     tcp  --  0.0.0.0/0            0.0.0.0/0    dports: 22
DROP       tcp  --  0.0.0.0/0            0.0.0.0/0    dports: 873
DROP       tcp  --  0.0.0.0/0            0.0.0.0/0    dports: 3240:3262
DROP       tcp  --  0.0.0.0/0            0.0.0.0/0    dports: 21
DROP       tcp  --  0.0.0.0/0            0.0.0.0/0    dports: 548
DROP       tcp  --  0.0.0.0/0            0.0.0.0/0    dports: 111
DROP       tcp  --  0.0.0.0/0            0.0.0.0/0    dports: 892
DROP       tcp  --  0.0.0.0/0            0.0.0.0/0    dports: 2049
DROP       tcp  --  0.0.0.0/0            0.0.0.0/0    dports: 443
DROP       tcp  --  0.0.0.0/0            0.0.0.0/0    dports: 80
DROP       tcp  --  0.0.0.0/0            0.0.0.0/0    dports: 3493
DROP       tcp  --  0.0.0.0/0            0.0.0.0/0    dports: 3306
DROP       tcp  --  0.0.0.0/0            0.0.0.0/0    dports: 22:23
DROP       udp  --  0.0.0.0/0            0.0.0.0/0    dports: 67:68
DROP       udp  --  0.0.0.0/0            0.0.0.0/0    dports: 123
DROP       udp  --  0.0.0.0/0            0.0.0.0/0    dports: 514
DROP       udp  --  0.0.0.0/0            0.0.0.0/0    dports: 19999
DROP       udp  --  0.0.0.0/0            0.0.0.0/0    dports: 5353
DROP       udp  --  0.0.0.0/0            0.0.0.0/0    dports: 161
DROP       udp  --  0.0.0.0/0            0.0.0.0/0    dports: 111
DROP       udp  --  0.0.0.0/0            0.0.0.0/0    dports: 892
DROP       udp  --  0.0.0.0/0            0.0.0.0/0    dports: 2049
ACCEPT     all  --  192.168.0.0/16       0.0.0.0/0    
DROP       all  --  0.0.0.0/0            0.0.0.0/0    
```

We can see that `fffuu` has split the `multiport` matches into individual rules and that the ruleset has been unfolded into one linear ruleset (the user-defined `DEFAULT_INPUT` and `DOS_PROTECT` chains are gone). 
This makes internal processing simpler; it does not change the behavior. 
Now about the 'overapproximation':
The original ruleset did a lot of rate limiting and drops packets which exceed the limit. 
To answer the question about *potentially* allowed packets, we must assume that the rate limiting will not drop us (i.e. our packets make it through the `DOS_PROTECT` chain without being dropped). 
We can see that the simplified ruleset has completely eliminated the rate limiting. 
Finally, let's look at the last rules of the simplified ruleset. 
The last rule (drop all) corresponds to the butlast rule of the `DEFAULT_INPUT` chain. 
This rule can be called a default policy. 
Since it matches all packets, `fffuu` stopped processing at this point.
Note that the last rule of `DEFAULT_INPUT` (drop all from eth0) and everything after that has been deleted.


Let's get to the interesting services on our NAS. 
`fffuu` will print three service matrices for TCP destination ports 22, 8080, and 80. 
As source port, the random, not-so-ephemeral source port 10000 was selected by `fffuu`. 
As we can see, the ruleset does not match on sports (source ports), so any value is fine here.
Here are the service matrices:

```
=========== TCP port 10000->22 =========
a |-> {0.0.0.0 .. 255.255.255.255}

(a,a)
```

This one is for ssh. 
It reads as follows. First, the nodes are defined. The nodes are grouped IP ranges. 
Here, we only have one node. This one node corresponds to the complete IPv4 address range `{0.0.0.0 .. 255.255.255.255}`. 
This means, all IP addresses are treated equally for ssh. 
Our policy wants them all to be dropped. 
Let's see.
Nodes are given unique names. Here, it is `a`.
Next, the edges are defined. 
Each pair `(a,b)` in the edges means that the IP range which corresponds to `a` can access `b`. 
Here we have `(a,a)`. 
This means everyone can access everyone. 
Wait what? We want ssh to be blocked. 
Though it is blocked in the `multiport` rule, this rule is shadowed by the third rule of `DEFAULT_INPUT` which allows ssh. 
This was an artifact of the previous system update.
Flaw found and scheduled for fixing ;-)


By the way, the service 'matrix' is actually a graph and graphviz can visualize these things. **TODO:** export to graphviz automatically.



Let's look at the next service matrix.

```
=========== TCP port 10000->8080 =========
a |-> {127.0.0.0 .. 127.255.255.255} u {192.168.0.0 .. 192.168.255.255}
b |-> {0.0.0.0 .. 126.255.255.255} u {128.0.0.0 .. 192.167.255.255} u {192.169.0.0 .. 255.255.255.255}

(a,a)
(a,b)
```
This one is for the webinterface at port 8080. 
Now we have two nodes, which means the firewall distinguishes two different classes of IP addresses. 
The first class of IP address (called `a`) consists of all localhost IPs and the local 192.168.0.0/24 range. 
We only wanted the webinterface reachable from the local 192.168.0.0/24 range. 
The first rule of `DEFAULT_INPUT` additionally accepts everything from `lo`, so this should be fine.
The second node (called `b`) is the rest of the IPv4 address space. We want this to be dropped. 
Let's look at the edges.
As we can see in the first vertex `(a,a)`: Only the good `lo` + local LAN range can reach the machine (which is itself located in the `a` range). 
The second edge `(a,b)` basically tells: The NAS itself can freely access any IP (which is fine).


Let's look at the third matrix.
```
=========== TCP port 10000->80 =========
a |-> {0.0.0.0 .. 126.255.255.255} u {128.0.0.0 .. 255.255.255.255}
b |-> {127.0.0.0 .. 127.255.255.255}

(b,a)
(b,b)
```

This one is for port 80, which should be dropped.
Exercise to the reader: Read the service matrix. 
Indeed, port 80 is blocked (except for packets from `lo`).





## FAQ

Q: The tool doesn't show anything for my firewall.

A: Our tool loads the `filter` table and the `FORWARD` chain by default. If you have a host-based firewall, you may probably want to load the `INPUT` chain.
