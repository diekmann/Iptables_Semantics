#!/bin/bash

iptables -F
iptables -X
iptables -Z
iptables -t nat -F
iptables -t nat -X
iptables -t nat -Z
iptables -t mangle -F
iptables -t mangle -X
iptables -t mangle -Z
iptables -t raw -F
iptables -t raw -X
iptables -t raw -Z
iptables -P INPUT ACCEPT
iptables -P OUTPUT ACCEPT
iptables -P FORWARD ACCEPT
modprobe -r iptable_raw
modprobe -r iptable_mangle
modprobe -r iptable_nat
