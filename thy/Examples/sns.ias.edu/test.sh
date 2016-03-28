#!/bin/bash
## Iptables example ruleset

## James Stephens (jns@ias.edu)
## http://www.sns.ias.edu/~jns/

## ============================================================
#
# Load appropriate modules.
modprobe ip_tables
modprobe ip_conntrack
modprobe ip_conntrack_ftp

# These lines are here in case rules are already in place and the script is ever rerun on the fly.
# We want to remove all rules and pre-exisiting user defined chains and zero the counters
# before we implement new rules.
iptables -F
iptables -X
iptables -Z

# Set up a default DROP policy for the built-in chains.
# If we modify and re-run the script mid-session then (because we have a default DROP
# policy), what happens is that there is a small time period when packets are denied until
# the new rules are back in place. There is no period, however small, when packets we
# don't want are allowed.
iptables -P INPUT DROP
iptables -P FORWARD DROP
iptables -P OUTPUT DROP

## ===========================================================
## Some definitions:

IFACE="wlan0"
IPADDR="131.159.207.206"
NAMESERVER_1="131.159.254.1"
NAMESERVER_2="131.159.254.2"
BROADCAST="131.159.207.255"
LOOPBACK="127.0.0.0/8"
CLASS_A="10.0.0.0/8"
CLASS_B="172.16.0.0/12"
CLASS_C="192.168.0.0/16"
CLASS_D_MULTICAST="224.0.0.0/4"
CLASS_E_RESERVED_NET="240.0.0.0/5"
P_PORTS="0:1023"
UP_PORTS="1024:65535"
TR_SRC_PORTS="32769:65535"
TR_DEST_PORTS="33434:33523"

## ============================================================
## Kernel flags
# To dynamically change kernel parameters and variables on the fly you need
# CONFIG_SYSCTL defined in your kernel. I would advise the following:

# Disable response to ping.
/bin/echo "1" > /proc/sys/net/ipv4/icmp_echo_ignore_all

# Disable response to broadcasts.
# You don't want yourself becoming a Smurf amplifier.
/bin/echo "1" > /proc/sys/net/ipv4/icmp_echo_ignore_broadcasts

# Don't accept source routed packets. Attackers can use source routing to generate
# traffic pretending to be from inside your network, but which is routed back along
# the path from which it came, namely outside, so attackers can compromise your
# network. Source routing is rarely used for legitimate purposes.
/bin/echo "0" > /proc/sys/net/ipv4/conf/all/accept_source_route

# Disable ICMP redirect acceptance. ICMP redirects can be used to alter your routing
# tables, possibly to a bad end.
/bin/echo "0" > /proc/sys/net/ipv4/conf/all/accept_redirects

# Enable bad error message protection.
/bin/echo "1" > /proc/sys/net/ipv4/icmp_ignore_bogus_error_responses

# Turn on reverse path filtering. This helps make sure that packets use
# legitimate source addresses, by automatically rejecting incoming packets
# if the routing table entry for their source address doesn't match the network
# interface they're arriving on. This has security advantages because it prevents
# so-called IP spoofing, however it can pose problems if you use asymmetric routing
# (packets from you to a host take a different path than packets from that host to you)
# or if you operate a non-routing host which has several IP addresses on different
# interfaces. (Note - If you turn on IP forwarding, you will also get this).
for interface in /proc/sys/net/ipv4/conf/*/rp_filter; do
   /bin/echo "1" > ${interface}
done

# Log spoofed packets, source routed packets, redirect packets.
/bin/echo "1" > /proc/sys/net/ipv4/conf/all/log_martians

# Make sure that IP forwarding is turned off. We only want this for a multi-homed host.
/bin/echo "0" > /proc/sys/net/ipv4/ip_forward

# Note: With connection tracking, all fragments are reassembled before being
# passed to the packet-filtering code so there is no ip_always_defrag switch as there
# was in the 2.2 kernel.

## ============================================================
# RULES

## LOOPBACK
# Allow unlimited traffic on the loopback interface.
iptables -A INPUT  -i lo -j ACCEPT
iptables -A OUTPUT -o lo -j ACCEPT

## SYN-FLOODING PROTECTION
# This rule maximises the rate of incoming connections. In order to do this we divert tcp
# packets with the SYN bit set off to a user-defined chain. Up to limit-burst connections
# can arrive in 1/limit seconds ..... in this case 4 connections in one second. After this, one
# of the burst is regained every second and connections are allowed again. The default limit
# is 3/hour. The default limit burst is 5.
#
iptables -N syn-flood
iptables -A INPUT -i $IFACE -p tcp --syn -j syn-flood
iptables -A syn-flood -m limit --limit 1/s --limit-burst 4 -j RETURN
iptables -A syn-flood -j DROP

## Make sure NEW tcp connections are SYN packets
iptables -A INPUT -i $IFACE -p tcp ! --syn -m state --state NEW -j DROP

## FRAGMENTS
# I have to say that fragments scare me more than anything.
# Sending lots of non-first fragments was what allowed Jolt2  to effectively "drown"
# Firewall-1. Fragments can be overlapped, and the subsequent interpretation of such
# fragments is very OS-dependent (see this paper for details).
# I am not going to trust any fragments.
# Log fragments just to see if we get any, and deny them too.
iptables -A INPUT -i $IFACE -f -j LOG --log-prefix "IPTABLES FRAGMENTS: "
iptables -A INPUT -i $IFACE -f -j DROP

## SPOOFING
# Most of this anti-spoofing stuff is theoretically not really necessary with the flags we
# have set in the kernel above ........... but you never know there isn't a bug somewhere in
# your IP stack.
#
# Refuse spoofed packets pretending to be from your IP address.
iptables -A INPUT  -i $IFACE -s $IPADDR -j DROP
# Refuse packets claiming to be from a Class A private network.
iptables -A INPUT  -i $IFACE -s $CLASS_A -j DROP
# Refuse packets claiming to be from a Class B private network.
iptables -A INPUT  -i $IFACE -s $CLASS_B -j DROP
# Refuse packets claiming to be from a Class C private network.
iptables -A INPUT  -i $IFACE -s $CLASS_C -j DROP
# Refuse Class D multicast addresses. Multicast is illegal as a source address.
iptables -A INPUT -i $IFACE -s $CLASS_D_MULTICAST -j DROP
# Refuse Class E reserved IP addresses.
iptables -A INPUT -i $IFACE -s $CLASS_E_RESERVED_NET -j DROP
# Refuse packets claiming to be to the loopback interface.
# Refusing packets claiming to be to the loopback interface protects against
# source quench, whereby a machine can be told to slow itself down by an icmp source
# quench to the loopback.
iptables -A INPUT  -i $IFACE -d $LOOPBACK -j DROP
# Refuse broadcast address packets.
iptables -A INPUT -i $IFACE -d $BROADCAST -j DROP

## DNS
# NOTE: DNS uses tcp for zone transfers, for transfers greater than 512 bytes (possible, but unusual), and on certain
# platforms like AIX (I am told), so you might have to add a copy of this rule for tcp if you need it
# Allow UDP packets in for DNS client from nameservers.
iptables -A INPUT -i $IFACE -p udp -s $NAMESERVER_1 --sport 53 -m state --state ESTABLISHED -j ACCEPT
iptables -A INPUT -i $IFACE -p udp -s $NAMESERVER_2 --sport 53 -m state --state ESTABLISHED -j ACCEPT
# Allow UDP packets to DNS servers from client.
iptables -A OUTPUT -o $IFACE -p udp -d $NAMESERVER_1 --dport 53 -m state --state NEW,ESTABLISHED -j ACCEPT
iptables -A OUTPUT -o $IFACE -p udp -d $NAMESERVER_2 --dport 53 -m state --state NEW,ESTABLISHED -j ACCEPT

## SSH
# Allow ssh outbound.
iptables -A INPUT  -i $IFACE -p tcp --sport 22 -m state --state ESTABLISHED -j ACCEPT
iptables -A OUTPUT -o $IFACE -p tcp --dport 22 -m state --state NEW,ESTABLISHED -j ACCEPT

## WWW
# Allow www outbound to 80.
iptables -A INPUT  -i $IFACE -p tcp --sport 80 -m state --state ESTABLISHED -j ACCEPT
iptables -A OUTPUT -o $IFACE -p tcp --dport 80 -m state --state NEW,ESTABLISHED -j ACCEPT
# Allow www outbound to 443.
iptables -A INPUT  -i $IFACE -p tcp --sport 443 -m state --state ESTABLISHED -j ACCEPT
iptables -A OUTPUT -o $IFACE -p tcp --dport 443 -m state --state NEW,ESTABLISHED -j ACCEPT

## TELNET
# Allow telnet outbound.
iptables -A INPUT  -i $IFACE -p tcp --sport 23 -m state --state ESTABLISHED -j ACCEPT
iptables -A OUTPUT -o $IFACE -p tcp --dport 23 -m state --state NEW,ESTABLISHED -j ACCEPT

## FTP
# Allow ftp outbound.
iptables -A INPUT  -i $IFACE -p tcp --sport 21 -m state --state ESTABLISHED -j ACCEPT
iptables -A OUTPUT -o $IFACE -p tcp --dport 21 -m state --state NEW,ESTABLISHED -j ACCEPT
# Now for the connection tracking part of ftp. This is discussed more completely in my section
# on connection tracking to be found here.
# 1) Active ftp.
# This involves a connection INbound from port 20 on the remote machine, to a local port
# passed over the ftp channel via a PORT command. The ip_conntrack_ftp module recognizes
# the connection as RELATED to the original outgoing connection to port 21 so we don't
# need NEW as a state match.
iptables -A INPUT  -i $IFACE -p tcp --sport 20 -m state --state ESTABLISHED,RELATED -j ACCEPT
iptables -A OUTPUT -o $IFACE -p tcp --dport 20 -m state --state ESTABLISHED -j ACCEPT
# 2) Passive ftp.
# This involves a connection outbound from a port >1023 on the local machine, to a port >1023
# on the remote machine previously passed over the ftp channel via a PORT command. The
# ip_conntrack_ftp module recognizes the connection as RELATED to the original outgoing
# connection to port 21 so we don't need NEW as a state match.
iptables -A INPUT  -i $IFACE -p tcp --sport $UP_PORTS --dport $UP_PORTS \
  -m state --state ESTABLISHED -j ACCEPT
iptables -A OUTPUT -o $IFACE -p tcp --sport $UP_PORTS --dport $UP_PORTS \
  -m state --state ESTABLISHED,RELATED -j ACCEPT

## SMTP
# Allow smtp outbound.
iptables -A INPUT  -i $IFACE -p tcp --sport 25 -m state --state ESTABLISHED -j ACCEPT
iptables -A OUTPUT -o $IFACE -p tcp --dport 25 -m state --state NEW,ESTABLISHED -j ACCEPT

## AUTH server
# Reject ident probes with a tcp reset.
# I need to do this for a broken mailhost that won't accept my mail if I just drop its ident probe.
iptables -A INPUT -i $IFACE -p tcp --dport 113 -j REJECT --reject-with tcp-reset

## TRACEROUTE
# Outgoing traceroute anywhere.
# The reply to a traceroute is an icmp time-exceeded which is dealt with by the next rule.
iptables -A OUTPUT -o $IFACE -p udp --sport $TR_SRC_PORTS --dport $TR_DEST_PORTS \
  -m state --state NEW -j ACCEPT

# ICMP
# We accept icmp in if it is "related" to other connections (e.g a time exceeded (11)
# from a traceroute) or it is part of an "established" connection (e.g. an echo reply (0)
# from an echo-request (8)).
iptables -A INPUT      -i $IFACE -p icmp -m state --state ESTABLISHED,RELATED -j ACCEPT
# We always allow icmp out.
iptables -A OUTPUT -o $IFACE -p icmp -m state --state NEW,ESTABLISHED,RELATED -j ACCEPT

## LOGGING
# You don't have to split up your logging like I do below, but I prefer to do it this way
# because I can then grep for things in the logs more easily. One thing you probably want
# to do is rate-limit the logging. I didn't do that here because it is probably best not too
# when you first set things up ................. you actually really want to see everything going to
# the logs to work out what isn't working and why. You cam implement logging with
# "-m limit --limit 6/h --limit-burst 5" (or similar) before the -j LOG in each case.
#
# Any udp not already allowed is logged and then dropped.
iptables -A INPUT  -i $IFACE -p udp -j LOG --log-prefix "IPTABLES UDP-IN: "
iptables -A INPUT  -i $IFACE -p udp -j DROP
iptables -A OUTPUT -o $IFACE -p udp -j LOG --log-prefix "IPTABLES UDP-OUT: "
iptables -A OUTPUT -o $IFACE -p udp -j DROP
# Any icmp not already allowed is logged and then dropped.
iptables -A INPUT  -i $IFACE -p icmp -j LOG --log-prefix "IPTABLES ICMP-IN: "
iptables -A INPUT  -i $IFACE -p icmp -j DROP
iptables -A OUTPUT -o $IFACE -p icmp -j LOG --log-prefix "IPTABLES ICMP-OUT: "
iptables -A OUTPUT -o $IFACE -p icmp -j DROP
# Any tcp not already allowed is logged and then dropped.
iptables -A INPUT  -i $IFACE -p tcp -j LOG --log-prefix "IPTABLES TCP-IN: "
iptables -A INPUT  -i $IFACE -p tcp -j DROP
iptables -A OUTPUT -o $IFACE -p tcp -j LOG --log-prefix "IPTABLES TCP-OUT: "
iptables -A OUTPUT -o $IFACE -p tcp -j DROP
# Anything else not already allowed is logged and then dropped.
# It will be dropped by the default policy anyway ........ but let's be paranoid.
iptables -A INPUT  -i $IFACE -j LOG --log-prefix "IPTABLES PROTOCOL-X-IN: "
iptables -A INPUT  -i $IFACE -j DROP
iptables -A OUTPUT -o $IFACE -j LOG --log-prefix "IPTABLES PROTOCOL-X-OUT: "
iptables -A OUTPUT -o $IFACE -j DROP

# THE END 
