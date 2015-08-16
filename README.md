# Iptables_Semantics

A formal semantics of the Linux netfilter iptables firewall.
Written in the [Isabelle](https://isabelle.in.tum.de/) interactive proof assistant.

It features
  * A real-world model of IPv4 addresses as 32bit machine words
  * Executable code
  * Support for all common actions in the iptables filter table: ACCEPT, DROP, REJECT, LOG, calling to user-defined chains, RETURN, GOTO to terminal chains, the empty action
  * Support for ALL primitive match conditions (by abstracting over unknown match conditions)
  * Translation to a simplified firewall model
  * Certification of spoofing protection 
  * ...

### Usage

Checkout:
This repository depends on the [seL4](https://github.com/seL4/l4v/) libraries (for the bitmagic operations on IPv4 addresses).
After cloning this repository, you need to initialized this submodule.
```
$ git submodule init
$ git submodule update
```

---

Checking all proofs:

```
$ isabelle build -v -d . -o document=pdf Iptables_Semantics_Examples
```

---

To develop, we suggest to load the Bitmagic theory as heap-image:
```
$ isabelle jedit -d . -l Bitmagic
```

Check the Examples directory to get started

### Academic Publications

  * Cornelius Diekmann, Lukas Schwaighofer, and Georg Carle. Certifying spoofing-protection of firewalls. In 11th International Conference on Network and Service Management, CNSM, Barcelona, Spain, November 2015. [pdf to appear soon]
  * Cornelius Diekmann, Lars Hupel, and Georg Carle. Semantics-Preserving Simplification of Real-World Firewall Rule Sets. In 20th International Symposium on Formal Methods, June 2015. [[preprint]](http://www.net.in.tum.de/fileadmin/bibtex/publications/papers/fm15_Semantics-Preserving_Simplification_of_Real-World_Firewall_Rule_Sets.pdf), [[springer | paywall]](http://link.springer.com/chapter/10.1007%2F978-3-319-19249-9_13)

The raw data of the iptables rulesets from the Examples is stored in [this](https://github.com/diekmann/net-network) repositoy.




