#!/bin/sh
# source: http://networking.ringofsaturn.com/Unix/iptables.php

IPT=`which iptables`

#flush all tables
$IPT -F

# if named additional tables already exist, delete them
$IPT -X DUMP
$IPT -X STATEFUL

# create DUMP table
$IPT -N DUMP > /dev/null
$IPT -A DUMP -p tcp -j LOG
$IPT -A DUMP -p udp -j LOG
$IPT -A DUMP -p tcp -j REJECT --reject-with tcp-reset
$IPT -A DUMP -p udp -j REJECT --reject-with icmp-port-unreachable
$IPT -A DUMP -j DROP

# create STATEFUL table
$IPT -N STATEFUL > /dev/null
$IPT -F STATEFUL
$IPT -I STATEFUL -m state --state ESTABLISHED,RELATED -j ACCEPT
$IPT -A STATEFUL -m state --state NEW -j ACCEPT
$IPT -A STATEFUL -j DUMP


# loopback rules
$IPT -A INPUT -i lo -j ACCEPT
$IPT -A OUTPUT -o lo -j ACCEPT

# drop reserved addresses incoming (these are reserved addresses
# but may change soon
$IPT -A INPUT -i eth0 -s 0.0.0.0/8 -j DUMP
$IPT -A INPUT -i eth0 -s 10.0.0.0/8 -j DUMP
$IPT -A INPUT -i eth0 -s 127.0.0.0/8 -j DUMP
$IPT -A INPUT -i eth0 -s 169.254.0.0/16 -j DUMP
$IPT -A INPUT -i eth0 -s 172.16.0.0/12 -j DUMP
# I want this normal BOGON for internal use
# $IPT -A INPUT -i eth0 -s 192.168.0.0/16 -j DUMP
$IPT -A INPUT -i eth0 -s 224.0.0.0/3 -j DUMP
$IPT -A INPUT -i eth0 -s 240.0.0.0/8 -j DUMP

#set iptables to allow everything from my work network
$IPT -A INPUT -i eth1 -p all -s 160.86.0.0/16 -j ACCEPT
$IPT -A INPUT -i eth1 -p all -j DROP

# allow certain inbound ICMP types (ping, traceroute..)
$IPT -A INPUT -i eth0 -p icmp --icmp-type destination-unreachable -j ACCEPT
$IPT -A INPUT -i eth0 -p icmp --icmp-type time-exceeded -j ACCEPT
$IPT -A INPUT -i eth0 -p icmp --icmp-type echo-reply -j ACCEPT
$IPT -A INPUT -i eth0 -p icmp --icmp-type echo-request -j ACCEPT

# Drop all packets to port 111
$IPT -A INPUT -p tcp --dport 111 -j DROP

# kill off identd quick 
$IPT -A INPUT -p tcp -i eth0 --dport 113 -j REJECT --reject-with tcp-reset

# sfs
$IPT -A INPUT -p tcp -i eth0 --dport 4  -j ACCEPT
# ftp
$IPT -A INPUT -p tcp -i eth0 --dport 20 -j ACCEPT
$IPT -A INPUT -p tcp -i eth0 --dport 21 -j ACCEPT
$IPT -A INPUT -p udp -i eth0 --dport 20 -j ACCEPT
$IPT -A INPUT -p udp -i eth0 --dport 21 -j ACCEPT
# ssh
$IPT -A INPUT -p tcp -i eth0 --dport 22 -j ACCEPT
$IPT -A INPUT -p udp -i eth0 --dport 22 -j ACCEPT
# www
$IPT -A INPUT -p tcp -i eth0 --dport 80 -j ACCEPT
$IPT -A INPUT -p udp -i eth0 --dport 80 -j ACCEPT
# https
$IPT -A INPUT -p tcp -i eth0 --dport 443 -j ACCEPT
$IPT -A INPUT -p udp -i eth0 --dport 443 -j ACCEPT

# Don't log route packets coming from routers - too much logging
$IPT -A INPUT -p udp -i eth0 --dport 520 -j REJECT

# Don't log smb/windows sharing packets - too much logging
$IPT -A INPUT -p tcp -i eth0 --dport 137:139 -j REJECT
$IPT -A INPUT -p udp -i eth0 --dport 137:139 -j REJECT

# Send INPUT packets through the STATEFUL table
$IPT -I INPUT -j STATEFUL

# Send tail of INPUT packets to the DUMP table
$IPT -A INPUT -j DUMP
