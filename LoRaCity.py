#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
 An updated version of LoRaSim 0.2.1 and LoRaFREE to simulate collisions in confirmable
 LoRaWAN with multiple base stations.
 Author: Luis María Campos de la Morena luismaria.campos@uclm.es
"""

"""
 DESCRIPTION:
    distnodes
        distance between nodes to simulate
    basestation
        distance between basestation to simulate
    avgsend
        average sending interval in seconds
    collision
        0   simplified check. Two packets collide when they arrive at the same time, on the same frequency and SF
        1   considers the capture effect
        2   consider the Non-orthognality SFs effect and capture effect
    simtime
        total running time in milliseconds
    randomseed
        random seed
 OUTPUT
    The result of every simulation run will be appended to a file named results.dat
"""

import simpy
import random
import numpy as np
import math
import sys
import matplotlib.pyplot as plt
import os
import geopandas as gpd
import geopy.distance
from shapely.geometry import Point
from shapely.ops import nearest_points
from matplotlib.patches import Rectangle
from PyQt5.QtWidgets import (QApplication, QComboBox, QDialog, QDialogButtonBox, QFormLayout, QGroupBox, QLabel, QLineEdit, QVBoxLayout)
from PyQt5.QtCore import Qt
# turn on/off graphics
graphics = 1

sf7 = np.array([7,-123,-120,-117.0])
sf8 = np.array([8,-126,-123,-120.0])
sf9 = np.array([9,-129,-126,-123.0])
sf10 = np.array([10,-132,-129,-126.0])
sf11 = np.array([11,-134.53,-131.52,-128.51])
sf12 = np.array([12,-137,-134,-131.0])

sensi = np.array([sf7,sf8,sf9,sf10,sf11,sf12])

IS7 = np.array([1,-8,-9,-9,-9,-9])
IS8 = np.array([-11,1,-11,-12,-13,-13])
IS9 = np.array([-15,-13,1,-13,-14,-15])
IS10 = np.array([-19,-18,-17,1,-17,-18])
IS11 = np.array([-22,-22,-21,-20,1,-20])
IS12 = np.array([-25,-25,-25,-24,-23,1])

IsoThresholds = np.array([IS7,IS8,IS9,IS10,IS11,IS12])

# Bandwidth
Bandwidth = 500
# Coding Rate
CodingRate = 1
# packet size per SFs
PcktLength_SF = [20,20,20,20,20,20]
LorawanHeader = 0 #7 Don't use LoRaWAN
# last time the gateway acked a package
nearstACK1p = [0,0,0] # 3 channels with 1% duty cycle
nearstACK10p = 0 # one channel with 10% duty cycle
AckMessLen = 0

#
# packet error model assumming independent Bernoulli
#
from scipy.stats import norm
def ber_reynders(eb_no, sf):
    """Given the energy per bit to noise ratio (in db), compute the bit error for the SF"""
    return norm.sf(math.log(sf, 12)/math.sqrt(2)*eb_no)

def ber_reynders_snr(snr, sf, bw, cr):
    """Compute the bit error given the SNR (db) and SF"""
    Temp = [4.0/5,4.0/6,4.0/7,4.0/8]
    CR = Temp[cr-1]
    BW = bw*1000.0
    eb_no =  snr - 10*math.log10(BW/2**sf) - 10*math.log10(sf) - 10*math.log10(CR) + 10*math.log10(BW)
    return ber_reynders(eb_no, sf)

def per(sf,bw,cr,rssi,pl):
    snr = rssi  +174 - 10*math.log10(bw) - 6
    return 1 - (1 - ber_reynders_snr(snr, sf, bw, cr))**(pl*8)

#
# check for collisions at base station
# Note: called before a packet (or rather node) is inserted into the list
def checkcollision(packet):
    col = 0
    if packet.lost:
        return 0
    
    processing = sum(1 for p in packetsAtBS[packet.bs].values() if p.processed == 1)
    if (processing > maxBSReceives):
        print("too long:", len(packetsAtBS[packet.bs]))
        packet.processed = 0
    else:
        packet.processed = 1

    # Verifica colisões com pacotes existentes
    if packetsAtBS[packet.bs]:
        for other_id, other in packetsAtBS[packet.bs].items():
            if other_id != packet.nodeid:
                if(full_collision == 1 or full_collision == 2):
                    if frequencyCollision(packet, other.packet[packet.bs]) \
                    and timingCollision(packet, other.packet[packet.bs]):
                        # Verificar colisão no domínio de potência
                        if (full_collision == 1):
                            c = powerCollision_1(packet, other.packet[packet.bs])
                        else:
                            c = powerCollision_2(packet, other.packet[packet.bs])
                        # Marcar pacotes colididos
                        for p in c:
                            p.collided = 1
                            if p == packet:
                                col = 1
                else:
                    # Colisão simples
                    if frequencyCollision(packet, other.packet[packet.bs]) \
                    and sfCollision(packet, other.packet[packet.bs]):
                        packet.collided = 1
                        other.packet[packet.bs].collided = 1
                        col = 1
    return col

# check if the gateway can ack this packet at any of the receive windows
# based on the duy cycle
def checkACK(packet):
    global  nearstACK1p
    global  nearstACK10p
    # check ack in the first window
    chanlindex=[872000000, 864000000, 860000000].index(packet.freq)
    timeofacking = env.now + 1  # one sec after receiving the packet
    if (timeofacking >= nearstACK1p[chanlindex]):
        # this packet can be acked
        packet.acked = 1
        tempairtime = airtime(packet.sf, CodingRate, AckMessLen+LorawanHeader, Bandwidth)
        nearstACK1p[chanlindex] = timeofacking+(tempairtime/0.01)
        nodes[packet.nodeid].rxtime += tempairtime
        return packet.acked
    else:
        # this packet can not be acked
        packet.acked = 0
        Tsym = (2**packet.sf)/(Bandwidth*1000) # sec
        Tpream = (8 + 4.25)*Tsym
        nodes[packet.nodeid].rxtime += Tpream

    # check ack in the second window
    timeofacking = env.now + 2  # two secs after receiving the packet
    if (timeofacking >= nearstACK10p):
        # this packet can be acked
        packet.acked = 1
        tempairtime = airtime(12, CodingRate, AckMessLen+LorawanHeader, Bandwidth)
        nearstACK10p = timeofacking+(tempairtime/0.1)
        nodes[packet.nodeid].rxtime += tempairtime
        return packet.acked
    else:
        # this packet can not be acked
        packet.acked = 0
        Tsym = (2.0**12)/(Bandwidth*1000.0) # sec
        Tpream = (8 + 4.25)*Tsym
        nodes[packet.nodeid].rxtime += Tpream
        return packet.acked

#
# frequencyCollision, conditions
#
#        |f1-f2| <= 120 kHz if f1 or f2 has bw 500
#        |f1-f2| <= 60 kHz if f1 or f2 has bw 250
#        |f1-f2| <= 30 kHz if f1 or f2 has bw 125
def frequencyCollision(p1,p2):
    if (abs(p1.freq-p2.freq)<=120 and (p1.bw==500 or p2.freq==500)):
        return True
    elif (abs(p1.freq-p2.freq)<=60 and (p1.bw==250 or p2.freq==250)):
        return True
    else:
        if (abs(p1.freq-p2.freq)<=30):
            return True
    return False

def sfCollision(p1, p2):
    if p1.sf == p2.sf:
        # p2 may have been lost too, will be marked by other checks
        return True
    return False

# check only the capture between the same spreading factor
def powerCollision_1(p1, p2):
    #powerThreshold = 6
    print ("pwr: node {0.nodeid} {0.rssi:3.2f} dBm node {1.nodeid} {1.rssi:3.2f} dBm; diff {2:3.2f} dBm".format(p1, p2, round(p1.rssi - p2.rssi,2)))
    if p1.sf == p2.sf:
       if abs(p1.rssi - p2.rssi) < IsoThresholds[p1.sf-7][p2.sf-7]:
            print ("collision pwr both node {} and node {}".format(p1.nodeid, p2.nodeid))
            # packets are too close to each other, both collide
            # return both pack ets as casualties
            return (p1, p2)
       elif p1.rssi - p2.rssi < IsoThresholds[p1.sf-7][p2.sf-7]:
            # p2 overpowered p1, return p1 as casualty
            print ("collision pwr node {} overpowered node {}".format(p2.nodeid, p1.nodeid))
            return (p1,)
       print ("p1 wins, p2 lost")
       # p2 was the weaker packet, return it as a casualty
       return (p2,)
    else:
       return ()

# check the capture effect and checking the effect of pesudo-orthognal SFs
def powerCollision_2(p1, p2):
    #powerThreshold = 6
    print ("SF: node {0.nodeid} {0.sf} node {1.nodeid} {1.sf}".format(p1, p2))
    print ("pwr: node {0.nodeid} {0.rssi:3.2f} dBm node {1.nodeid} {1.rssi:3.2f} dBm; diff {2:3.2f} dBm".format(p1, p2, round(p1.rssi - p2.rssi,2)))
    if p1.sf == p2.sf:
       if abs(p1.rssi - p2.rssi) < IsoThresholds[p1.sf-7][p2.sf-7]:
           print ("collision pwr both node {} and node {}".format(p1.nodeid, p2.nodeid))
           # packets are too close to each other, both collide
           # return both packets as casualties
           return (p1, p2)
       elif p1.rssi - p2.rssi < IsoThresholds[p1.sf-7][p2.sf-7]:
           # p2 overpowered p1, return p1 as casualty
           print ("collision pwr node {} overpowered node {}".format(p2.nodeid, p1.nodeid))
           print ("capture - p2 wins, p1 lost")
           return (p1,)
       print ("capture - p1 wins, p2 lost")
       # p2 was the weaker packet, return it as a casualty
       return (p2,)
    else:
       if p1.rssi-p2.rssi > IsoThresholds[p1.sf-7][p2.sf-7]:
          print ("P1 is OK")
          if p2.rssi-p1.rssi > IsoThresholds[p2.sf-7][p1.sf-7]:
              print ("p2 is OK")
              return ()
          else:
              print ("p2 is lost")
              return (p2,)
       else:
           print ("p1 is lost")
           if p2.rssi-p1.rssi > IsoThresholds[p2.sf-7][p1.sf-7]:
               print ("p2 is OK")
               return (p1,)
           else:
               print ("p2 is lost")
               return (p1,p2)

def timingCollision(p1, p2):
    # assuming p1 is the freshly arrived packet and this is the last check
    # we've already determined that p1 is a weak packet, so the only
    # way we can win is by being late enough (only the first n - 5 preamble symbols overlap)

    # assuming 8 preamble symbols
    Npream = 8

    # we can lose at most (Npream - 5) * Tsym of our preamble
    Tpreamb = 2**p1.sf/(1.0*p1.bw) * (Npream - 5)

    # check whether p2 ends in p1's critical section
    p2_end = p2.addTime + p2.rectime
    p1_cs = env.now + (Tpreamb/1000.0)  # to sec
    print ("collision timing node {} ({},{},{}) node {} ({},{})".format(
        p1.nodeid, env.now - env.now, p1_cs - env.now, p1.rectime,
        p2.nodeid, p2.addTime - env.now, p2_end - env.now
    ))
    if p1_cs < p2_end:
        # p1 collided with p2 and lost
        print ("not late enough")
        return True
    print ("saved by the preamble")
    return False

# this function computes the airtime of a packet
# according to LoraDesignGuide_STD.pdf
#
def airtime(sf,cr,pl,bw):
    H = 0        # implicit header disabled (H=0) or not (H=1)
    DE = 0       # low data rate optimization enabled (=1) or not (=0)
    Npream = 8   # number of preamble symbol (12.25  from Utz paper)

    if bw == 125 and sf in [11, 12]:
        # low data rate optimization mandated for BW125 with SF11 and SF12
        DE = 1
    if sf == 6:
        # can only have implicit header with SF6
        H = 1

    Tsym = (2.0**sf)/bw  # msec
    Tpream = (Npream + 4.25)*Tsym
    print ("sf", sf, " cr", cr, "pl", pl, "bw", bw)
    payloadSymbNB = 8 + max(math.ceil((8.0*pl-4.0*sf+28+16-20*H)/(4.0*(sf-2*DE)))*(cr+4),0)
    Tpayload = payloadSymbNB * Tsym
    return ((Tpream + Tpayload)/1000.0)  # to secs
#
# check for nodes in the BS
#
def check_nodes_in_BS(x, y):
    global distBS0
    global nodes
    result = False
    for node in nodes:
        d = geopy.distance.distance((node.x,node.y), (x,y))
        if distBS0 > d:
            return True

    return result

#
# check if the point is inside the map
#
def check_point(x, y):
    global map_loaded
    result = False

    aux_point = Point (x, y)
    polygons = map_loaded['geometry']
    values = polygons.apply(lambda x: aux_point.within(x))
    for i in range (0, len(values)):
        if values[i]:
            result = True

    return result

#
# reassign the point to the closest point on the map
#
def reassign(x, y):
    global map_loaded
    polygons = map_loaded['geometry']
    point = Point (x, y)
    aux_list = []

    for i in range (0, len(polygons)):
        p1, p2 = nearest_points(polygons[i], point)
        aux_list.append(p1)
    
    current = sys.maxsize
    final_point = None
    for i in range (0, len(aux_list)):
        if geopy.distance.distance((aux_list[i].x, aux_list[i].y), (x, y)) < current:
            current = geopy.distance.distance((aux_list[i].x, aux_list[i].y), (x, y))
            final_point = Point (aux_list[i].x, aux_list[i].y)
    
    return final_point

#
# check if the basestation is valid
#
def valid_bs():
    global bslist
    idbs = 0
    for i in range(0, nrBS):
        x = Xbs[int(i/lbs)][int(i%lbs)]+offsetXbs
        y = Ybs[int(i/lbs)][int(i%lbs)]+offsetYbs
        out = check_point(x, y)
        valid = check_nodes_in_BS(x, y)
        if out:
            b = myBS(idbs, x, y)
            bslist.append(b)
            packetsAtBS.append({})
            packetsRecBS.append([])
            idbs = idbs + 1
        if valid and not out:
            aux_point = reassign(x, y)
            x = aux_point.x
            y = aux_point.y
            b = myBS(idbs, x, y)
            bslist.append(b)
            packetsAtBS.append({})
            packetsRecBS.append([])
            idbs = idbs + 1

#
# check if the node is valid
#
def valid_node():
    idnode = 0
    for i in range(0, nrNodes):
        x = Xn[int(i/ln)][int(i%ln)]+offsetXnode
        y = Yn[int(i/ln)][int(i%ln)]+offsetYnode
        valid = check_point(x, y)
        if valid:
            node = myNode(idnode, avgSendTime, x, y)
            nodes.append(node)
            idnode = idnode + 1

#
# create "virtual" packet for each BS
#
def create_packets():
    global nodes
    for node in nodes:
        for i in range(0,len(bslist)):
            d = geopy.distance.distance((node.x,node.y), (bslist[i].x,bslist[i].y)).m
            node.dist.append(d)
            node.parameters = assignParameters(node.nodeid, node.dist[i], SFtype)
            node.packet.append(myPacket(node.nodeid, node.parameters.freq, node.parameters.sf, node.parameters.bw, node.parameters.cr, node.parameters.txpow, node.dist[i], i))
        print ('node: ', node.nodeid, "x: ", node.x, "y: ", node.y, "dist: ", node.dist)

#
# this function creates a BS
#
class myBS():
    def __init__(self, id, x, y):
        self.id = id
        self.x = x
        self.y = y

        print ("BSx:", self.x, "BSy:", self.y)

        # graphics for bs
        global graphics
        if (graphics == 1):
            global ax
            ax.add_artist(plt.Circle((self.x, self.y), 0.0010, fill=True, zorder=2, color='red'))
            ax.add_artist(plt.Circle((self.x, self.y), distBS, fill=False, zorder=2, color='red'))

#
# this function creates a node
#
class myNode():
    def __init__(self, nodeid, period, x, y):
        self.nodeid = nodeid
        self.period = period
        self.lstretans = 0
        self.sent = 0
        self.coll = 0
        self.lost = 0
        self.noack = 0
        self.acklost = 0
        self.recv = 0
        self.losterror = 0
        self.rxtime = 0
        self.energyTX = 0
        self.energyRX = 0

        #node placement
        self.x = x
        self.y = y

        self.packet = []
        self.dist = []
        print ("Nx:", self.x, "Ny:", self.y)  

        # graphics for node
        global graphics
        if (graphics == 1):
            global ax
            ax.add_artist(plt.Circle((self.x, self.y), 0.0005, fill=True, zorder=2, color='black'))

class assignParameters():
    def __init__(self, nodeid, distance, SFtype):
        global Ptx
        global gamma
        global d0
        global var
        global Lpld0
        global GL

        self.nodeid = nodeid
        self.txpow = 14
        self.bw = Bandwidth
        self.cr = CodingRate
        self.sf = 12
        self.rectime = airtime(self.sf, self.cr, LorawanHeader+PcktLength_SF[self.sf-7], self.bw)
        self.freq = random.choice([872000000, 864000000, 860000000])

        Prx = self.txpow  ## zero path loss by default
        # log-shadow
        Lpl = Lpld0 + 10*gamma*math.log10(distance/d0) + var
        print ("Lpl:", Lpl)
        Prx = self.txpow - GL - Lpl
        minairtime = 9999
        minsf = 0
        minbw = 0
        print ("Prx:", Prx)
        if SFtype == -1:
            for i in range(0,6):  # SFs
                if ((sensi[i, [125,250,500].index(self.bw) + 1]) < Prx):
                    at = airtime(i+7, self.cr, LorawanHeader+PcktLength_SF[i], self.bw)
                    if at < minairtime:
                        minairtime = at
                        minsf = i+7
                        minsensi = sensi[i, [125,250,500].index(self.bw) + 1]
            print ("best sf:", minsf, " best bw: ", minbw, "best airtime:", minairtime)
            if (minsf != 0):
                self.rectime = minairtime
                self.sf = minsf
        else:
            self.rectime = airtime(int(SFtype), self.cr, LorawanHeader+PcktLength_SF[0], self.bw)
            self.sf = int(SFtype)

        # SF, BW, CR and PWR distributions
        print ("bw", self.bw, "sf", self.sf, "cr", self.cr)
        global SFdistribution, CRdistribution, TXdistribution, BWdistribution
        SFdistribution[self.sf-7]+=1;
        CRdistribution[self.cr-1]+=1;
        TXdistribution[int(self.txpow)-2]+=1;
        if self.bw==125:
            BWdistribution[0]+=1;
        elif self.bw==250:
            BWdistribution[1]+=1;
        else:
            BWdistribution[2]+=1;

#
# this function creates a packet (associated with a node)
# it also sets all parameters, currently random
#
class myPacket():
    def __init__(self, nodeid, freq, sf, bw, cr, txpow, distance, bslist):
        global gamma
        global d0
        global var
        global Lpld0
        global GL

        # new: base station ID
        self.bs = bslist
        self.nodeid = nodeid
        self.seqNr = 0
        self.freq = freq
        self.sf = sf
        self.bw = bw
        self.cr = cr
        self.txpow = txpow
        # transmission range, needs update XXX
        self.transRange = 150
        self.pl = LorawanHeader+PcktLength_SF[self.sf-7]
        self.symTime = (2.0**self.sf)/self.bw
        self.arriveTime = 0

        if var == 0:
            Lpl = Lpld0 + 10*gamma*math.log10(distance/d0)
        else:
            Lpl = Lpld0 + 10*gamma*math.log10(distance/d0) + np.random.normal(-var, var)

        self.rssi = self.txpow - GL - Lpl
        print ("node id", self.nodeid, "symTime ", self.symTime, "rssi", self.rssi)
        self.rectime = airtime(self.sf,self.cr,self.pl,self.bw)
        print ("rectime node ", self.nodeid, "  ", self.rectime)
        # denote if packet is collided
        self.collided = 0
        self.processed = 0
        self.lost = False
        self.perror = False
        self.acked = 0
        self.acklost = 0

#
# main discrete event loop, runs for each node
# a global list of packet being processed at the gateway
# is maintained
#
def transmit(env,node):
    while True:
        yield env.timeout(random.expovariate(1.0/float(node.period)))

        # time sending and receiving
        # packet arrives -> add to base station
        node.sent = node.sent + 1
        
        global packetSeq
        global bslist

        packetSeq = packetSeq + 1

        for bs in range(0, len(bslist)):
           if (node.nodeid in packetsAtBS[bs]):
                print ("ERROR: packet already in")
           else:
                sensitivity = sensi[node.packet[bs].sf - 7, [125,250,500].index(node.packet[bs].bw) + 1]
                if node.packet[bs].rssi < sensitivity:
                    print ("node {}: packet will be lost".format(node.nodeid))
                    node.packet[bs].lost = True
                else:
                    node.packet[bs].lost = False
                    if (per(node.packet[bs].sf,node.packet[bs].bw,node.packet[bs].cr,node.packet[bs].rssi,node.packet[bs].pl) < random.uniform(0,1)):
                        # OK CRC
                        node.packet[bs].perror = False
                    else:
                        # Bad CRC
                        node.packet[bs].perror = True
                    # adding packet if no collision
                    if (checkcollision(node.packet[bs])==1):
                        node.packet[bs].collided = 1
                    else:
                        node.packet[bs].collided = 0
                    packetsAtBS[bs][node.nodeid] = node
                    node.packet[bs].addTime = env.now
                    node.packet[bs].seqNr = packetSeq

        # take first packet rectime
        yield env.timeout(node.packet[0].rectime)

        for bs in range(0, len(bslist)):
            if (node.packet[bs].lost == 0\
                    and node.packet[bs].perror == False\
                    and node.packet[bs].collided == False\
                    and checkACK(node.packet[bs])):
                node.packet[bs].acked = 1
                # the packet can be acked
                # check if the ack is lost or not
                if((14 - Lpld0 - 10*gamma*math.log10(node.dist[bs]/d0) - np.random.normal(-var, var)) > sensi[node.packet[bs].sf-7, [125,250,500].index(node.packet[bs].bw) + 1]):
                # the ack is not lost
                    node.packet[bs].acklost = 0
                else:
                # ack is lost
                    node.packet[bs].acklost = 1
            else:
                node.packet[bs].acked = 0
            
            if node.packet[bs].processed == 1:
                global nrProcessed
                nrProcessed = nrProcessed + 1
            if node.packet[bs].lost:
                node.lost = node.lost + 1
                node.lstretans += 1
                global nrLost
                nrLost += 1
            elif node.packet[bs].perror:
                node.losterror = node.losterror + 1
                global nrLostError
                nrLostError += 1
            elif node.packet[bs].collided == 1:
                node.coll = node.coll + 1
                node.lstretans += 1
                global nrCollisions
                nrCollisions = nrCollisions +1
            elif node.packet[bs].acked == 0:
                node.noack = node.noack + 1
                node.lstretans += 1
                global nrNoACK
                nrNoACK += 1
            elif node.packet[bs].acklost == 1:
                node.acklost = node.acklost + 1
                node.lstretans += 1
                global nrACKLost
                nrACKLost += 1
            else:
                node.recv = node.recv + 1
                global nrReceived
                nrReceived = nrReceived + 1

        # if packet did not collide, add it in list of received packets
        # unless it is already in
        for bs in range(0, len(bslist)):
            if node.packet[bs].lost:
                lostPackets.append(node.packet[bs].seqNr)
            else:
                if node.packet[bs].collided == 0:
                    packetsRecBS[bs].append(node.packet[bs].seqNr)
                    if (recPackets):
                        if (recPackets[-1] != node.packet[bs].seqNr):
                            recPackets.append(node.packet[bs].seqNr)
                    else:
                        recPackets.append(node.packet[bs].seqNr)
                else:
                    # XXX only for debugging
                    collidedPackets.append(node.packet[bs].seqNr)

        # complete packet has been received by base station
        # can remove it
        for bs in range(0, len(bslist)):
            if (node.nodeid in packetsAtBS[bs]):
                del packetsAtBS[bs][node.nodeid]
                # reset the packet
                node.packet[bs].collided = 0
                node.packet[bs].processed = 0
                node.packet[bs].lost = False
                node.packet[bs].acked = 0
                node.packet[bs].acklost = 0

class Dialog(QDialog):

    def __init__(self):
        super(Dialog, self).__init__()
        self.createFormGroupBox()
        
        buttonBox = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        buttonBox.accepted.connect(self.accept)
        buttonBox.rejected.connect(self.reject)
        
        mainLayout = QVBoxLayout()
        mainLayout.addWidget(self.formGroupBox)
        mainLayout.addWidget(buttonBox)
        self.setLayout(mainLayout)
        
        self.setWindowTitle("LoRaCity")

        
    def createFormGroupBox(self):
        self.formGroupBox = QGroupBox("Data:")
        self.map = QComboBox()
        map_types = ["Sevilla", "Barcelona", "Berlin", "Paris", "Moscow"]
        for i in range(len(map_types)):
            self.map.addItem(map_types[i])
        self.nodes = QLineEdit()
        self.basestations = QLineEdit()
        self.avgsend = QLineEdit()
        self.sf = QComboBox()
        sf_types = ["Best", "7", "8", "9", "10", "11", "12"]
        for i in range(len(sf_types)):
            self.sf.addItem(sf_types[i])
        self.collisions = QComboBox()
        collision_types = ["0", "1", "2"]
        for i in range(len(collision_types)):
            self.collisions.addItem(collision_types[i])
        self.cr = QComboBox()
        cr_types = ["1", "2", "3", "4"]
        for i in range(len(cr_types)):
            self.cr.addItem(cr_types[i])
        self.bw = QComboBox()
        bw_types = ["500", "250", "125"]
        for i in range(len(bw_types)):
            self.bw.addItem(bw_types[i])
        self.pcktlen = QLineEdit()
        self.simtime = QLineEdit()
        self.seed = QLineEdit()
        layout = QFormLayout()
        layout.setLabelAlignment(Qt.AlignRight)
        layout.addRow(QLabel("Map:"), self.map)
        layout.addRow(QLabel("Distance nodes (km):"), self.nodes)
        layout.addRow(QLabel("Distance BS (km):"), self.basestations)
        layout.addRow(QLabel("Average send (min):"), self.avgsend)
        layout.addRow(QLabel("Collision:"), self.collisions)
        layout.addRow(QLabel("Spreading factor:"), self.sf)
        layout.addRow(QLabel("Coding rate:"), self.cr)
        layout.addRow(QLabel("Bandwidth(kHz):"), self.bw)
        layout.addRow(QLabel("Packet length(B):"), self.pcktlen)
        layout.addRow(QLabel("Simtime (min):"), self.simtime)
        layout.addRow(QLabel("Seed:"), self.seed)
        self.formGroupBox.setLayout(layout)

#
# "main" program
#
if __name__ == "__main__":
    app = QApplication(sys.argv)
    dialog = Dialog()
    state = dialog.exec_()
    app.exit()
    if state==0:
        sys.exit(0)
    map_path = "Maps/"+str(dialog.map.currentText())+"/"+str(dialog.map.currentText())+".shp"
    map_loaded = gpd.read_file(map_path)
    distnodes0 = float(dialog.nodes.text())
    distBS0 = float(dialog.basestations.text())
    avgSendTime = int(dialog.avgsend.text())*60000
    full_collision = int(dialog.collisions.currentText())
    SFtype = dialog.sf.currentText()
    if SFtype == 'Best':
        SFtype = -1
    CodingRate = int(dialog.cr.currentText())
    Bandwidth = int(dialog.bw.currentText())
    pcktbytes = int(dialog.pcktlen.text())
    PcktLength_SF = [pcktbytes, pcktbytes, pcktbytes, pcktbytes, pcktbytes, pcktbytes]
    simtime = int(dialog.simtime.text())*60000
    Rnd = random.seed(int(dialog.seed.text()))

    print ("Distance nodes: ", distnodes0)
    print ("Distance BS: ", distBS0)
    print ("AvgSendTime (exp. distributed):",avgSendTime)
    print ("Full Collision: ", full_collision)
    print ("Simtime: ", simtime)
    print ("Seed: ", int(dialog.seed.text()))

    #Convert kilometers to latitude
    distnodes = distnodes0/111.12
    distBS = distBS0/111.12

    # global stuff
    nodes = []
    packetsAtBS = [{} for _ in range(nrBS)]
    SFdistribution = [0 for x in range(0,6)]
    BWdistribution = [0 for x in range(0,3)]
    CRdistribution = [0 for x in range(0,4)]
    TXdistribution = [0 for x in range(0,13)]
    env = simpy.Environment()

    # maximum number of packets the BS can receive at the same time
    maxBSReceives = 8

    # max distance: 300m in city, 3000 m outside (5 km Utz experiment)
    # also more unit-disc like according to Utz
    nrCollisions = 0
    nrReceived = 0
    nrProcessed = 0
    nrLost = 0
    nrLostError = 0
    nrNoACK = 0
    nrACKLost = 0
    nrRetrans = 0
    
    # global value of packet sequence numbers
    packetSeq = 0

    # list of received packets
    recPackets=[]
    collidedPackets=[]
    lostPackets = []

    Ptx = 9.75
    gamma = 2.08
    d0 = 1000.0 #40.0
    var = 0.0 #2.0
    Lpld0 = 127.41
    GL = 0
    minsensi = np.amin(sensi[:,[125,250,500].index(Bandwidth) + 1])
    Lpl = Ptx - minsensi
    maxDist = d0*(10**((Lpl-Lpld0)/(10.0*gamma)))

    # nodes and basestation placement
    limits = map_loaded.total_bounds         
    Xo = limits[0]
    Yo = limits[1]
    X = limits[2]
    Y = limits[3]
    offsetXnode = ((X-Xo)%distnodes)/2
    offsetYnode = ((Y-Yo)%distnodes)/2
    offsetXbs = ((X-Xo)%distBS)/2
    offsetYbs = ((Y-Yo)%distBS)/2
    nx = np.arange(Xo, X+distnodes//2, distnodes, dtype=float)
    ny = np.arange(Yo, Y+distnodes//2, distnodes, dtype=float)
    bx = np.arange(Xo, X+distBS//2, distBS, dtype=float)
    by = np.arange(Yo, Y+distBS//2, distBS, dtype=float)

    Xn, Yn = np.meshgrid(nx,ny)
    Xbs, Ybs = np.meshgrid(bx,by)

    ln = len(nx)
    lbs = len(bx)

    nrNodes = int(np.trunc(((X-Xo)/distnodes)+1)*np.trunc(((Y-Yo)/distnodes)+1))
    nrBS = int(np.trunc(((X-Xo)/distBS)+1)*np.trunc(((Y-Yo)/distBS)+1))

    # prepare graphics and add sink
    if (graphics == 1):
        plt.ion()
        map_loaded.plot()
        ax = plt.gcf().gca()

        ax.add_patch(Rectangle((Xo, Yo), X-Xo, Y-Yo, fill=None, alpha=1))

    # list of base stations
    bslist = []

    # list of packets at each base station, init with 0 packets
    packetsAtBS = [{} for _ in range(nrBS)]
    packetsRecBS = []

    # optimize nodes and base stations
    valid_node()
    valid_bs()
    create_packets()
    
    # start simulation
    for node in nodes:
        env.process(transmit(env, node))

    #prepare show
    if (graphics == 1):
        plt.xlim([Xo, X])
        plt.ylim([Yo, Y])
        plt.title(str(dialog.map.currentText()), fontweight="bold")
        plt.xlabel("Longitude")
        plt.ylabel("Latitude")
        plt.draw()
        plt.show()
    
    # store nodes and basestation locations
    dirResults = "Results"
    if not os.path.exists(dirResults):
        os.mkdir(dirResults)
    
    with open('Results/nodes.txt', 'w') as nfile:
        nfile.write('id'.ljust(7) + 'x'.ljust(18) + 'y\n')
        for node in nodes:
            nodeid = '{nodeid}'.format(**vars(node))
            x = node.x
            y = node.y
            nfile.write('{}{:.13f}  {:.13f}\n'.format(nodeid.ljust(7), x, y))

    with open('Results/basestation.txt', 'w') as bfile:
        bfile.write('id'.ljust(5) + 'x'.ljust(20) + 'y\n')
        for basestation in bslist:
            bsid = '{id}'.format(**vars(basestation))
            x = '{x}'.format(**vars(basestation))
            y = '{y}'.format(**vars(basestation))
            bfile.write('{} {} {}\n'.format(bsid.ljust(4), x.ljust(19), y.ljust(18)))

    # start simulation
    env.run(until=simtime)

    # compute energy
    # Transmit consumption in mA from -2 to +17 dBm
    TX = [22, 22, 22, 23,                                      # RFO/PA0: -2..1
        24, 24, 24, 25, 25, 25, 25, 26, 31, 32, 34, 35, 44,  # PA_BOOST/PA1: 2..14
        82, 85, 90,                                          # PA_BOOST/PA1: 15..17
        105, 115, 125]                                       # PA_BOOST/PA1+PA2: 18..20
    RX = 16
    V = 3.0     # voltage XXX
    energyTotal = 0
    energyTX = 0
    energyRX = 0

    for node in nodes:
        for bsindex in range(0, len(bslist)):
            node.energyTX += (node.packet[bsindex].rectime * TX[int(node.packet[bsindex].txpow)+2] * V * node.sent)/1e3
            node.energyRX += (node.rxtime * RX * V) / 1e3
        energyTX += node.energyTX
        energyRX += node.energyRX
        energyTotal += node.energyTX + node.energyRX

    with open('Results/energy.txt', 'w') as nfile:
        nfile.write('id'.ljust(7) + 'energyTX'.ljust(15) + 'energyRX\n')
        for node in nodes:
            nodeid = '{nodeid}'.format(**vars(node))
            auxenergyTX = node.energyTX
            auxenergyRX = node.energyRX
            nfile.write('{}{:.10f}   {:.10f}\n'.format(nodeid.ljust(7), auxenergyTX, auxenergyRX))

    # LoRaCity stats
    print ("============================")
    sent = sum(n.sent for n in nodes)
    retrans = sum(n.lstretans for n in nodes)
    print ("-----LoRaCity stats-----")
    print ("Nodes: {} BS: {}".format(len(nodes), len(bslist)))
    print ("Sent packets: ", sent)
    print ("Received packets: ", nrReceived)
    print ("Collided packets: ", nrCollisions)
    print ("Lost packets: ", nrLost)
    print ("Processed packets: ", nrProcessed)
    print ("Retransmissions: ", retrans)
    print ("Bad CRC: ", nrLostError)
    print ("NoACK packets: ", nrNoACK)
    print ("ACKLost:", nrACKLost)
    totalpacketsAtBS = 0
    for i in range(0,len(bslist)):
        print ("Packets at BS",i, ": ", len(packetsRecBS[i]))
        totalpacketsAtBS += len(packetsRecBS[i])
    print ("Total packets at BS: ", totalpacketsAtBS)

    # data extraction rate
    der1 = (sent-nrCollisions)/float(sent) if sent!=0 else 0
    print ("DER:", der1)
    der2 = (nrReceived)/float(sent) if sent!=0 else 0
    print ("DER method 2:", der2)
    print ("Energy (in J): ", energyTotal)

    print ("============================")
    print ("SFdistribution: ", SFdistribution)
    print ("BWdistribution: ", BWdistribution)
    print ("CRdistribution: ", CRdistribution)
    print ("TXdistribution: ", TXdistribution)
    print ("CollectionTime: ", env.now)

    # Pie graphics
    pietitle = ["Collisions", "Received", "Retransmissions"]
    pie1 = [nrCollisions, (sent*nrBS)-nrCollisions] 
    pie2 = [nrReceived, (sent*nrBS)-nrReceived]
    pie3 = [retrans, sent*nrBS-retrans]
    pie1labels = ["Collisions", "No collisions"]
    pie2labels = ["Received", "No received"]
    pie3labels = ["Retransmissions", "No retransmissions"]
    pievalues = [pie1, pie2, pie3]
    pielabels = [pie1labels, pie2labels, pie3labels]
    fig, axes= plt.subplots(1, 3)

    for i, ax in enumerate(axes.flatten()):
        x = pievalues[i]
        ax.pie(x, autopct='%1.2f%%', pctdistance=0.9)
        ax.legend(pielabels[i])
        ax.set_title(pietitle[i], fontweight="bold")
    plt.show()

    # this can be done to keep graphics visible
    if (graphics == 1):
        input('Press Enter to continue ...')

    # save experiment data
    with open('Results/retransmissions.txt', 'w') as bfile:
        bfile.write('id'.ljust(7) + 'Percentage'.ljust(11) + 'Retransmissions\n')
        for n in nodes:
            nodeid = '{nodeid}'.format(**vars(n))
            lstretans = n.lstretans
            auxsent = n.sent
            if auxsent+lstretans == 0:
                percentage = 0.0
            else:
                percentage = format(float(lstretans/(auxsent+lstretans)*100), '.4f')

            totalsent = int(lstretans+auxsent)
            bfile.write('{} {} {}/{}\n'.format(nodeid.ljust(6), str(percentage).ljust(10), lstretans, totalsent))

    fname = "Results/results.dat"
    print (fname)
    if os.path.isfile(fname):
        res = "\n" + str(dialog.seed.text()).ljust(12) + str(len(nodes)).ljust(9) + str(avgSendTime).ljust(11) + str(len(bslist)).ljust(14) + str(full_collision).ljust(10) + str(sent).ljust(17) + str(nrReceived).ljust(12) + str(nrCollisions).ljust(14) + str(nrLost).ljust(8) + str(nrLostError).ljust(13) + str(nrNoACK).ljust(9) +str(nrACKLost).ljust(11) + str(simtime).ljust(16) + '{:.12f}  {:.12f}  {:.11f}  {:.9f}  {:.9f}  '.format(der1, der2, energyTotal, energyTX, energyRX) + str(SFdistribution).ljust(26) + str(BWdistribution).ljust(16) + str(CRdistribution).ljust(16) + str(TXdistribution)
    else:
        'id'.ljust(5) + 'x'.ljust(14) + 'y\n'
        res = "randomseed".ljust(12) + "nrNodes".ljust(9) + "TransRate".ljust(11) + "Basestations".ljust(14) + "collType".ljust(10) + "nrTransmissions".ljust(17) + "nrReceived".ljust(12) + "nrCollisions".ljust(14) + "nrlost".ljust(8) + "nrlosterror".ljust(13) + "nrnoack".ljust(9) + "nracklost".ljust(11) + "CollectionTime".ljust(16) + "DER1".ljust(16) + "DER2".ljust(16) + "OverallEnergy".ljust(15) + "EnergyTX".ljust(13) + "EnergyRX".ljust(13) + "sfdistribution".ljust(26) + "bwdistribution".ljust(16) + "crdistribution".ljust(16) + "txdistribution\n" + str(dialog.seed.text()).ljust(12) + str(len(nodes)).ljust(9) + str(avgSendTime).ljust(11) + str(len(bslist)).ljust(14) + str(full_collision).ljust(10) + str(sent).ljust(17) + str(nrReceived).ljust(12) + str(nrCollisions).ljust(14) + str(nrLost).ljust(8) + str(nrLostError).ljust(13) + str(nrNoACK).ljust(9) +str(nrACKLost).ljust(11) + str(simtime).ljust(16) + '{:.12f}  {:.12f}  {:.11f}  {:.9f}  {:.9f}  '.format(der1, der2, energyTotal, energyTX, energyRX) + str(SFdistribution).ljust(26) + str(BWdistribution).ljust(16) + str(CRdistribution).ljust(16) + str(TXdistribution)
    with open(fname, "a") as myfile:
        myfile.write(res)
    myfile.close()

    exit(-1)
