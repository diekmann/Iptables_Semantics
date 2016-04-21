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
from mininet.clean import cleanup

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
	ifco = {}
	def __init__(self, *args, **kwargs):
		self.ifco = kwargs.get('ifco')
		if self.ifco is None:
			self.ifco = {}
	def ifc(self):
		for i in self.ifco:
			debug("Host {} interface {} IP to {}\n".format(self, i, self.ifco[i]))
			#debug("{}\n".format(self.intfs))
			self.intf(i).setIP(self.ifco[i])

mainflows = [
	"priority=8,hard_timeout=0,idle_timeout=0,in_port=1,dl_type=0x800,nw_proto=1,nw_dst=10.0.2.0/24,action=output:2",
	"priority=7,hard_timeout=0,idle_timeout=0,in_port=1,dl_type=0x800,nw_proto=6,nw_dst=10.0.2.0/24,tp_src=1024/0xfc00,tp_dst=80,action=output:2",
	"priority=7,hard_timeout=0,idle_timeout=0,in_port=1,dl_type=0x800,nw_proto=6,nw_dst=10.0.2.0/24,tp_src=2048/0xf800,tp_dst=80,action=output:2",
	"priority=7,hard_timeout=0,idle_timeout=0,in_port=1,dl_type=0x800,nw_proto=6,nw_dst=10.0.2.0/24,tp_src=4096/0xf000,tp_dst=80,action=output:2",
	"priority=7,hard_timeout=0,idle_timeout=0,in_port=1,dl_type=0x800,nw_proto=6,nw_dst=10.0.2.0/24,tp_src=8192/0xe000,tp_dst=80,action=output:2",
	"priority=7,hard_timeout=0,idle_timeout=0,in_port=1,dl_type=0x800,nw_proto=6,nw_dst=10.0.2.0/24,tp_src=16384/0xc000,tp_dst=80,action=output:2",
	"priority=7,hard_timeout=0,idle_timeout=0,in_port=1,dl_type=0x800,nw_proto=6,nw_dst=10.0.2.0/24,tp_src=32768/0x8000,tp_dst=80,action=output:2",
	"priority=6,hard_timeout=0,idle_timeout=0,in_port=1,dl_type=0x800,nw_dst=10.0.2.0/24,action=drop",
	"priority=5,hard_timeout=0,idle_timeout=0,in_port=2,dl_type=0x800,nw_proto=1,nw_dst=10.0.1.0/24,action=output:1",
	"priority=4,hard_timeout=0,idle_timeout=0,in_port=2,dl_type=0x800,nw_proto=6,nw_dst=10.0.1.0/24,tp_src=80,tp_dst=1024/0xfc00,action=output:1",
	"priority=4,hard_timeout=0,idle_timeout=0,in_port=2,dl_type=0x800,nw_proto=6,nw_dst=10.0.1.0/24,tp_src=80,tp_dst=2048/0xf800,action=output:1",
	"priority=4,hard_timeout=0,idle_timeout=0,in_port=2,dl_type=0x800,nw_proto=6,nw_dst=10.0.1.0/24,tp_src=80,tp_dst=4096/0xf000,action=output:1",
	"priority=4,hard_timeout=0,idle_timeout=0,in_port=2,dl_type=0x800,nw_proto=6,nw_dst=10.0.1.0/24,tp_src=80,tp_dst=8192/0xe000,action=output:1",
	"priority=4,hard_timeout=0,idle_timeout=0,in_port=2,dl_type=0x800,nw_proto=6,nw_dst=10.0.1.0/24,tp_src=80,tp_dst=16384/0xc000,action=output:1",
	"priority=4,hard_timeout=0,idle_timeout=0,in_port=2,dl_type=0x800,nw_proto=6,nw_dst=10.0.1.0/24,tp_src=80,tp_dst=32768/0x8000,action=output:1",
	"priority=3,hard_timeout=0,idle_timeout=0,in_port=2,dl_type=0x800,nw_dst=10.0.1.0/24,action=drop",
	"priority=2,hard_timeout=0,idle_timeout=0,in_port=1,dl_type=0x800,nw_proto=1,action=output:2",
	"priority=1,hard_timeout=0,idle_timeout=0,in_port=1,dl_type=0x800,nw_proto=6,tp_src=1024/0xfc00,tp_dst=80,action=output:2",
	"priority=1,hard_timeout=0,idle_timeout=0,in_port=1,dl_type=0x800,nw_proto=6,tp_src=2048/0xf800,tp_dst=80,action=output:2",
	"priority=1,hard_timeout=0,idle_timeout=0,in_port=1,dl_type=0x800,nw_proto=6,tp_src=4096/0xf000,tp_dst=80,action=output:2",
	"priority=1,hard_timeout=0,idle_timeout=0,in_port=1,dl_type=0x800,nw_proto=6,tp_src=8192/0xe000,tp_dst=80,action=output:2",
	"priority=1,hard_timeout=0,idle_timeout=0,in_port=1,dl_type=0x800,nw_proto=6,tp_src=16384/0xc000,tp_dst=80,action=output:2",
	"priority=1,hard_timeout=0,idle_timeout=0,in_port=1,dl_type=0x800,nw_proto=6,tp_src=32768/0x8000,tp_dst=80,action=output:2",
	"priority=0,hard_timeout=0,idle_timeout=0,in_port=1,dl_type=0x800,action=drop",
]

floodflow3 = [
	"priority=0,in_port=1,action=output:2,3",
	"priority=0,in_port=2,action=output:1,3",
	"priority=0,in_port=3,action=output:1,2",
]


class StaticSwitch(OVSSwitch): # closest to what we want. It quacks like it.
	flowentries=[]
	ofversion=None
	def __init__(self, name, *args, **kwargs):
		self.flowentries = kwargs['flowentries']
		self.ofversion = kwargs.get('ofversion')
		OVSSwitch.__init__(self, name, *args, **kwargs)
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
		vopt = ""
		if self.ofversion:
			vopt = " -O" + self.ofversion
			qcall(self, self.vsctl, "set bridge", self, "protocols=" + self.ofversion)
		for f in self.flowentries:
			qcall(self,self.dpctl,"add-flow" + vopt, f)

class MSwitch(StaticSwitch, IFCHlp):
	def __init__(self, *args, **kwargs):
		IFCHlp.__init__(self, *args, **kwargs)
		return StaticSwitch.__init__(self, *args, **kwargs)
	def poststart(self):
		self.ifc()
		StaticSwitch.poststart(self)

class ICHost(Host,IFCHlp):
	aroutes = []
	def __init__(self, *args, **kwargs):
		self.aroutes = kwargs.get('routes')
		if self.aroutes is None:
			self.aroutes = []
		dr = kwargs.get('defaultRoute')
		rv = Host.__init__(self, *args, **kwargs)
		IFCHlp.__init__(self, *args, **kwargs)
		if dr is not None:
			self.aroutes += ['default ' + dr]
		#output("{}: {}\n".format(self, self.aroutes))
		return rv
	def config(self, *_parm, **_parms): #*_parm aschinken
		rv = Host.config(self, *_parm, **_parms)
		self.ifc()
		# ifc might have destroyed the default route, so reset it.
		#print("{}:\n{}".format(self, self.cmd("ip route")))
		for r in self.aroutes:
			dd = ''
			if 'default' in r:
				dd = 'ip route del default; '
			self.cmd(dd + 'ip route add', r) # this sometimes reports RTNETLINK answers: No such process but succeeds. uh?
		#print("{}:\n{}".format(self, self.cmd("ip route")))
		self.cmd('sysctl -w net.ipv4.ip_forward=1') # why would you not want this?
		return rv

class DRtr(ICHost):
	def config(self, *_parm, **_params):
		rv = ICHost.config(self, *_parm, **_params)
		qcall(self,self.cmd,'iptables -P INPUT ACCEPT')
		qcall(self,self.cmd,'iptables -P OUTPUT ACCEPT')
		qcall(self,self.cmd,'iptables -P FORWARD DROP')
		qcall(self,self.cmd,'iptables -A FORWARD -p icmp -j ACCEPT')
		qcall(self,self.cmd,'iptables -A FORWARD -i s1-lan -o s1-wan -p tcp --sport 1024:65535 --dport 80 -j ACCEPT')
		qcall(self,self.cmd,'iptables -A FORWARD -i s1-wan -o s1-lan -p tcp --sport 80 --dport 1024:65535 -j ACCEPT')
		#qcall(self,self.cmd,'iptables -A FORWARD -i s1-lan -o s1-wan -p tcp --sport 49152:65535 --dport 80 -j ACCEPT')
		#qcall(self,self.cmd,'iptables -A FORWARD -i s1-wan -o s1-lan -p tcp --sport 80 --dport 49152:65535 -j ACCEPT')
		return rv
	def terminate(self):
		self.cmd('sysctl net.ipv4.ip_forward=0')
		Host.terminate(self)

class DTopo(Topo):
	"""Topology for Test:
	   (client,client) - router - internet (actually, it's just two boxes...)"""
	def __init__(self, typ):
		self.typ = typ
		return Topo.__init__(self)
	def build(self):
		if self.typ is not "lr" and self.typ is not "of":
			raise ValueError("Unknown topology type: " + typ)
		net = "/24"
		dr = 'via 10.0.1.1'
		if self.typ is "of":
			net = "/16" 
			dr = 'via 10.0.2.1'
		client1 = self.addHost('h1', ip='10.0.1.2'+net, defaultRoute=dr)
		client2 = self.addHost('h2', ip='10.0.1.3'+net, defaultRoute=dr)
		ls = self.addSwitch('s2', ip=None, cls=StaticSwitch, flowentries=floodflow3)
		nhost1 = self.addHost('n1', ip='10.10.0.2'+net, defaultRoute='via 10.1.0.1', cls=ICHost, ifco={'n1-dl':'10.0.2.1'+net, 'n1-ul':'10.1.0.2/24'}, routes=['10.0.0.0/16 via 10.0.2.4'])
		nhost2 = self.addHost('n2', ip='10.1.0.1'+net, cls=ICHost, routes=['10.0.0.0/16 via 10.1.0.2'])
		s1c = {'s1-wan': "10.0.2.4"+net, 's1-lan': "10.0.1.1"+net}
		switch = None
		if self.typ is "of":
			switch = self.addSwitch('s1', ip=None, cls=MSwitch, flowentries=mainflows, ifco=s1c)
		elif self.typ is "lr":
			switch = self.addHost('s1', ip=None, cls=DRtr, ifco=s1c, defaultRoute='via 10.0.2.1')
		self.addLink(ls, switch, intfName2='s1-lan')
		self.addLink(nhost1, switch, intfName1='n1-dl', intfName2='s1-wan')
		self.addLink(nhost1, nhost2, intfName1='n1-ul')
		self.addLink(client1, ls)
		self.addLink(client2, ls)

def dump(ofile, strng):
	with open(ofile, "w") as fo:
		fo.write(strng.replace("\r\n","\n"))

def tcpreachtest(client, server, port=80, timeout=2.5):
	output("TCP {}: {} -> {}: ".format(port, client, server))
	rand = "{}".format(randint(0,18446744073709551615))
	server.sendCmd("socat EXEC:'echo {}' TCP4-LISTEN:{},reuseaddr".format(rand,port))
	sleep(.1) # I doubt there is a way of knowing whether it is listening.
	cliout = client.cmd("socat TCP:{}:{},connect-timeout={} -".format(server.IP(), port, timeout))
	sleep(.1)
	server.sendInt()
	sleep(.1)
	servout = server.waitOutput()
	result = cliout.strip() == rand
	output("{}\n".format("success" if result else "fail"))
	debug("tcp test: socat server: {}\n".format(servout.strip()))
	debug("tcp test: socat client: {}\n".format(cliout.strip()))
	debug("tcp test:     expected: {}\n".format(rand))
	return result

def tcpreachtests(hosts, ports=[80], timeout=2.5):
	if type(ports) is not list:
		ports = [ports]
	for port in ports:
		for h1 in hosts:
			for h2 in hosts:
				if h1 == h2:
					continue
				tcpreachtest(h1, h2, port, timeout)

def makearpentries(host, hosts):
	# add all arp entries for host to hosts.
	for intf in host.intfList():
		if intf.MAC() and intf.IP(): # will also sort out loopback
			for host in hosts:
				info("inserting arp table entry {} {} at {} (no output is good output): {}\n".format(intf.IP(), intf.MAC(), host, \
					host.cmd("arp -s {} {}".format(intf.IP(), intf.MAC())).strip())) # will fail with Netwok unreachable at given times. Easier to ignore than fix.

def standalone():
	if "info" in argv:
		setLogLevel( 'info' )
	if "debug" in argv:
		setLogLevel( 'debug' )
	topo = None
	if "of" in argv:
		topo = DTopo(typ="of")
	elif "lr" in argv:
		topo = DTopo(typ="lr")
	if topo is None:
		print("Supply either of (for OpenFlow) or lr (for a Linux Router)")
		exit(-1)
	net = Mininet(topo=topo)
	net.start()
	sw, h1, h2, h3, h4 = net.get('s1', 'h1', 'h2', 'n1', 'n2')
	if "fixarp" in argv:
		makearpentries(sw, [h1, h2, h3])
	#print(sw.cmd("netstat -tulpen"))
	if "dump" in argv:
		if "lr" in argv:
			dump('iptables-save', sw.cmd('iptables-save'))
			dump('ip-route', sw.cmd('ip route'))
			#dump('collectedmacs', sw.cmd('collectmacs.sh'))
		elif "of" in argv:
			print(sw.dpctl('dump-flows'))
	if "test" in argv:
		sese = [h1,h2,h3,h4]
		net.ping(sese)
		tcpreachtests(sese,ports=[80,22])
	if "cli" in argv:
		CLI(net)
	net.stop()

if __name__ == '__main__':
	try:
		standalone()
	except KeyboardInterrupt:
		cleanup()
		print ""

topos = { 
	'lr': ( lambda: DTopo(typ="lr") ), 
	'of': ( lambda: DTopo(typ="of") ),
}
