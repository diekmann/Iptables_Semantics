#!/usr/bin/python

from mininet.net import Mininet
from mininet.topo import Topo
from mininet.link import TCLink
from mininet.cli import CLI
from mininet.util import quietRun
from mininet.log import setLogLevel, info, output, debug, error
from mininet.term import makeTerms
from mininet.node import Host, OVSBridge, OVSSwitch
from mininet.util import waitListening

from random import randint
from sys import exit, stdin, argv
from re import findall
from time import sleep
import os

def pne(s):
	if not s.strip() == "":
		if not "\n" in s:
			s = s + "\n"
		print(s)

def qcall(o,a,*args):
	info('config {}: {}\n'.format(o, args))
	orv = a(*args)
	rv = orv
	if not rv.strip() == "":
		if not "\n" in rv:
			rv = rv + "\n"
		error('{} in {} failed: {}'.format(args, o, rv))
	return orv

class IFCHlp:
	def ifc(self):
		self.intf('s1-lan').setIP("10.0.1.1", 24)
		#qcall(self,self.cmd,'ip a add 10.0.1.1/24  dev s1-lan')
		self.intf('s1-wan').setIP("10.0.2.4", 24)
		#qcall(self,self.cmd,'ip a add 10.0.2.4/24  dev s1-wan')


class StaticSwitch(OVSSwitch,IFCHlp): # Bridge is closest to what we want. It quacks like it.
	batch = False
	@classmethod
	def addSelf(cls, name, topo):
		return topo.addSwitch(name, ip=None, cls=StaticSwitch)
	#def start(self, *_parm, **_parms):
	#	print "StaticSwitch.start"
	#	return OVSSwitch.start(self, *_parm, **_parms)
	# batchStartup ist called second, so I'll use that
	@classmethod
	def batchStartup(cls, switches, *_parm, **_parms):
		rv = OVSSwitch.batchStartup(switches, *_parm, **_parms)
		for s in switches:
			s.poststart()
		return rv
	def poststart(self):
		self.ifc()
		flows = [
			"priority=8,hard_timeout=0,idle_timeout=0,dl_type=0x800,nw_proto=1,nw_dst=10.0.2.1/32,action=mod_dl_dst:0:0:0:0:0:2,output:2",
			"priority=7,hard_timeout=0,idle_timeout=0,in_port=1,dl_type=0x800,nw_proto=6,nw_dst=10.0.2.1/32,tp_src=1024/0xfc00,tp_dst=80,action=mod_dl_dst:0:0:0:0:0:2,output:2",
			"priority=7,hard_timeout=0,idle_timeout=0,in_port=1,dl_type=0x800,nw_proto=6,nw_dst=10.0.2.1/32,tp_src=2048/0xf800,tp_dst=80,action=mod_dl_dst:0:0:0:0:0:2,output:2",
			"priority=7,hard_timeout=0,idle_timeout=0,in_port=1,dl_type=0x800,nw_proto=6,nw_dst=10.0.2.1/32,tp_src=4096/0xf000,tp_dst=80,action=mod_dl_dst:0:0:0:0:0:2,output:2",
			"priority=7,hard_timeout=0,idle_timeout=0,in_port=1,dl_type=0x800,nw_proto=6,nw_dst=10.0.2.1/32,tp_src=8192/0xe000,tp_dst=80,action=mod_dl_dst:0:0:0:0:0:2,output:2",
			"priority=7,hard_timeout=0,idle_timeout=0,in_port=1,dl_type=0x800,nw_proto=6,nw_dst=10.0.2.1/32,tp_src=16384/0xc000,tp_dst=80,action=mod_dl_dst:0:0:0:0:0:2,output:2",
			"priority=7,hard_timeout=0,idle_timeout=0,in_port=1,dl_type=0x800,nw_proto=6,nw_dst=10.0.2.1/32,tp_src=32768/0x8000,tp_dst=80,action=mod_dl_dst:0:0:0:0:0:2,output:2",
			"priority=6,hard_timeout=0,idle_timeout=0,dl_type=0x800,nw_dst=10.0.2.1/32,action=drop",
			"priority=5,hard_timeout=0,idle_timeout=0,dl_type=0x800,nw_proto=1,nw_dst=10.0.1.2/32,action=mod_dl_dst:0:0:0:0:0:1,output:1",
			"priority=4,hard_timeout=0,idle_timeout=0,in_port=2,dl_type=0x800,nw_proto=6,nw_dst=10.0.1.2/32,tp_src=80,tp_dst=1024/0xfc00,action=mod_dl_dst:0:0:0:0:0:1,output:1",
			"priority=4,hard_timeout=0,idle_timeout=0,in_port=2,dl_type=0x800,nw_proto=6,nw_dst=10.0.1.2/32,tp_src=80,tp_dst=2048/0xf800,action=mod_dl_dst:0:0:0:0:0:1,output:1",
			"priority=4,hard_timeout=0,idle_timeout=0,in_port=2,dl_type=0x800,nw_proto=6,nw_dst=10.0.1.2/32,tp_src=80,tp_dst=4096/0xf000,action=mod_dl_dst:0:0:0:0:0:1,output:1",
			"priority=4,hard_timeout=0,idle_timeout=0,in_port=2,dl_type=0x800,nw_proto=6,nw_dst=10.0.1.2/32,tp_src=80,tp_dst=8192/0xe000,action=mod_dl_dst:0:0:0:0:0:1,output:1",
			"priority=4,hard_timeout=0,idle_timeout=0,in_port=2,dl_type=0x800,nw_proto=6,nw_dst=10.0.1.2/32,tp_src=80,tp_dst=16384/0xc000,action=mod_dl_dst:0:0:0:0:0:1,output:1",
			"priority=4,hard_timeout=0,idle_timeout=0,in_port=2,dl_type=0x800,nw_proto=6,nw_dst=10.0.1.2/32,tp_src=80,tp_dst=32768/0x8000,action=mod_dl_dst:0:0:0:0:0:1,output:1",
			"priority=3,hard_timeout=0,idle_timeout=0,dl_type=0x800,nw_dst=10.0.1.2/32,action=drop",
			"priority=2,hard_timeout=0,idle_timeout=0,dl_type=0x800,nw_proto=1,action=mod_dl_dst:0:0:0:0:0:2,output:2",
			"priority=1,hard_timeout=0,idle_timeout=0,in_port=1,dl_type=0x800,nw_proto=6,tp_src=1024/0xfc00,tp_dst=80,action=mod_dl_dst:0:0:0:0:0:2,output:2",
			"priority=1,hard_timeout=0,idle_timeout=0,in_port=1,dl_type=0x800,nw_proto=6,tp_src=2048/0xf800,tp_dst=80,action=mod_dl_dst:0:0:0:0:0:2,output:2",
			"priority=1,hard_timeout=0,idle_timeout=0,in_port=1,dl_type=0x800,nw_proto=6,tp_src=4096/0xf000,tp_dst=80,action=mod_dl_dst:0:0:0:0:0:2,output:2",
			"priority=1,hard_timeout=0,idle_timeout=0,in_port=1,dl_type=0x800,nw_proto=6,tp_src=8192/0xe000,tp_dst=80,action=mod_dl_dst:0:0:0:0:0:2,output:2",
			"priority=1,hard_timeout=0,idle_timeout=0,in_port=1,dl_type=0x800,nw_proto=6,tp_src=16384/0xc000,tp_dst=80,action=mod_dl_dst:0:0:0:0:0:2,output:2",
			"priority=1,hard_timeout=0,idle_timeout=0,in_port=1,dl_type=0x800,nw_proto=6,tp_src=32768/0x8000,tp_dst=80,action=mod_dl_dst:0:0:0:0:0:2,output:2",
			"priority=0,hard_timeout=0,idle_timeout=0,dl_type=0x800,action=drop",
			#"priority=0,hard_timeout=0,idle_timeout=0,arp,action=output:LOCAL",
			#"priority=0,hard_timeout=0,idle_timeout=0,arp,action=goto_table=105",
			#"'table=105,dl_type=0x0806, nw_dst=10.10.10.1, actions=move:NXM_OF_ETH_SRC[]->NXM_OF_ETH_DST[], mod_dl_src:00:00:5E:00:02:01, load:0x2->NXM_OF_ARP_OP[], move:NXM_NX_ARP_SHA[]->NXM_NX_ARP_THA[], move:NXM_OF_ARP_SPA[]->NXM_OF_ARP_TPA[], load:0x00005e000201->NXM_NX_ARP_SHA[], load:0x0a0a0a01->NXM_OF_ARP_SPA[], in_port'",
			#"'table=105,dl_type=0x0806, nw_dst=10.10.20.1, actions=move:NXM_OF_ETH_SRC[]->NXM_OF_ETH_DST[],  mod_dl_src:00:00:5E:00:02:02, load:0x2->NXM_OF_ARP_OP[], move:NXM_NX_ARP_SHA[]->NXM_NX_ARP_THA[], move:NXM_OF_ARP_SPA[]->NXM_OF_ARP_TPA[], load:0x00005e000202->NXM_NX_ARP_SHA[], load:0xa0a1401->NXM_OF_ARP_SPA[], in_port'",
			#"'table=105,dl_type=0x0806, nw_dst=172.16.1.1, actions=move:NXM_OF_ETH_SRC[]->NXM_OF_ETH_DST[],  mod_dl_src:00:00:5E:00:02:03, load:0x2->NXM_OF_ARP_OP[], move:NXM_NX_ARP_SHA[]->NXM_NX_ARP_THA[], move:NXM_OF_ARP_SPA[]->NXM_OF_ARP_TPA[], load:0x00005e000203->NXM_NX_ARP_SHA[], load:0xac100101->NXM_OF_ARP_SPA[], in_port'",
			#"'table=105,dl_type=0x0806, nw_dst=172.16.1.10, actions=move:NXM_OF_ETH_SRC[]->NXM_OF_ETH_DST[], mod_dl_src:00:00:5E:00:02:03, load:0x2->NXM_OF_ARP_OP[], move:NXM_NX_ARP_SHA[]->NXM_NX_ARP_THA[], move:NXM_OF_ARP_SPA[]->NXM_OF_ARP_TPA[], load:0x00005e000203->NXM_NX_ARP_SHA[], load:0xac10010a->NXM_OF_ARP_SPA[], in_port'",
			#"'table=105,priority=0,action=output:1,2'",
		]
		#qcall(self, self.vsctl, "set bridge", self, "protocols=OpenFlow13")
		for f in flows:
			qcall(self,self.dpctl,"add-flow", f)
			#qcall(self,self.dpctl,"add-flow -OOpenFlow13", f)

class DRtr(Host,IFCHlp):
	@classmethod
	def addSelf(cls, name, topo):
		return topo.addHost(name, ip=None, cls=DRtr)
	def config(self, *_parm, **_params):
		rv = Host.config(self, *_parm, **_params)
		qcall(self,self.cmd,'iptables -P INPUT ACCEPT')
		qcall(self,self.cmd,'iptables -P OUTPUT ACCEPT')
		qcall(self,self.cmd,'iptables -P FORWARD DROP')
		qcall(self,self.cmd,'iptables -A FORWARD -p icmp -j ACCEPT')
		qcall(self,self.cmd,'iptables -A FORWARD -i s1-lan -o s1-wan -p tcp --sport 1024:65535 --dport 80 -j ACCEPT')
		qcall(self,self.cmd,'iptables -A FORWARD -i s1-wan -o s1-lan -p tcp --sport 80 --dport 1024:65535 -j ACCEPT')
		#qcall(self,self.cmd,'iptables -A FORWARD -i s1-lan -o s1-wan -p tcp --sport 49152:65535 --dport 80 -j ACCEPT')
		#qcall(self,self.cmd,'iptables -A FORWARD -i s1-wan -o s1-lan -p tcp --sport 80 --dport 49152:65535 -j ACCEPT')
		self.ifc()
		qcall(self,self.cmd,'ip route add default via 10.0.2.1 dev s1-wan')
		self.cmd('sysctl -w net.ipv4.ip_forward=1')
		return rv
	def terminate(self):
		self.cmd('sysctl net.ipv4.ip_forward=0')
		Host.terminate(self)

class DTopo(Topo):
	"""Topology for Test:
	   client - router - internet (actually, it's just a single box...)"""
	def __init__(self, scls):
		self.scls = scls
		return Topo.__init__(self)
	def build(self):
		client = self.addHost('h1', ip='10.0.1.2/24', defaultRoute='via 10.0.1.1')
		nhost = self.addHost('n1', ip='10.0.2.1/24', defaultRoute='via 10.0.2.4')
		switch = self.scls.addSelf('s1', topo=self)
		csl  = self.addLink(client, switch, intfName2='s1-lan')
		nhsl = self.addLink(nhost,  switch,  intfName2='s1-wan')

def dump(ofile, strng):
	with open(ofile, "w") as fo:
		fo.write(strng.replace("\r\n","\n"))

def tcpreachtest(net, client, server, port=80, timeout=2.5):
	output("TCP {}: {} -> {}: ".format(port, client, server))
	rand = "{}".format(randint(0,18446744073709551615))
	server.sendCmd("socat EXEC:'echo {}' TCP4-LISTEN:{},reuseaddr".format(rand,port))
	sleep(.1) # I doubt there is a way of knowing whether it is listening.
	cliout = client.cmd("socat TCP:{}:{},connect-timeout={} -".format(server.IP(), port, timeout))
	server.sendInt()
	servout = server.waitOutput()
	result = cliout.strip() == rand
	output("{}\n".format("success" if result else "fail"))
	debug("tcp test: socat server: {}".format(servout.strip()))
	debug("tcp test: socat client: {}".format(cliout.strip()))
	debug("tcp test:     expected: {}".format(rand))
	return result

def tcpreachtests(net, hosts, ports=[80], timeout=2.5):
	if type(ports) is not list:
		ports = [ports]
	for port in ports:
		for h1 in hosts:
			for h2 in hosts:
				if h1 == h2:
					continue
				tcpreachtest(net, h1, h2, port, timeout)

def makearpentries(host, hosts):
	# add all arp entries for host to hosts.
	for intf in host.intfList():
		if intf.MAC() and intf.IP(): # will also sort out loopback
			for host in hosts:
				host.cmd("arp -s {} {}".format(intf.IP(), intf.MAC())) # will fail with Netwok unreachable at given times. Easier to ignore than fix.

def standalone():
	if "info" in argv:
		setLogLevel( 'info' )
	scls=None
	if "of" in argv:
		scls = StaticSwitch 
	elif "lr" in argv:
		scls = DRtr
	else:
		print("Supply either of (for OpenFlow) or lr (for a Linux Router)")
		exit(-1)
	topo = DTopo(scls=scls)
	net = Mininet(topo=topo,autoSetMacs=True)
	net.start()
	sw, h1, h2 = net.get('s1', 'h1', 'n1')
	if "noarp" not in argv:
		makearpentries(sw, [h1, h2])
	#print(sw.cmd("netstat -tulpen"))
	if "dump" in argv:
		if "lr" in argv:
			dump('iptables-save', sw.cmd('iptables-save'))
			dump('ip-route', sw.cmd('ip route'))
			dump('collectedmacs', sw.cmd('collectmacs.sh'))
		elif "of" in argv:
			print("of/dump TODO")
	if "test" in argv:
		sese = [h1,h2]
		net.ping(sese)
		tcpreachtests(net,sese,ports=[80,22])
	if "cli" in argv:
		CLI(net)
	net.stop()

if __name__ == '__main__':
	standalone()

topos = { 
	'lr': ( lambda: DTopo(scls=DRtr) ), 
	'of': ( lambda: DTopo(scls=StaticSwitch) ),
}
