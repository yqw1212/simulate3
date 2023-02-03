#!/usr/bin/env python2
# -------------------------------------------------------------------------------------------------
#
#    ,ggggggggggg,     _,gggggg,_      ,ggggggggggg,      ,gggg,  
#   dP"""88""""""Y8, ,d8P""d8P"Y8b,   dP"""88""""""Y8,  ,88"""Y8b,
#   Yb,  88      `8b,d8'   Y8   "8b,dPYb,  88      `8b d8"     `Y8
#    `"  88      ,8Pd8'    `Ybaaad88P' `"  88      ,8Pd8'   8b  d8
#        88aaaad8P" 8P       `""""Y8       88aaaad8P",8I    "Y88P'
#        88""""Y8ba 8b            d8       88"""""   I8'          
#        88      `8bY8,          ,8P       88        d8           
#        88      ,8P`Y8,        ,8P'       88        Y8,          
#        88_____,d8' `Y8b,,__,,d8P'        88        `Yba,,_____, 
#       88888888P"     `"Y8888P"'          88          `"Y8888888 
#
#   The Block Oriented Programming (BOP) Compiler - v2.1
#
#
# Kyriakos Ispoglou (ispo) - ispo@purdue.edu
# PURDUE University, Fall 2016-18
# -------------------------------------------------------------------------------------------------
#
#
# coreutils.py:
#
# This module contains basic declarations and functions that are being used by all other modules.
#
# -------------------------------------------------------------------------------------------------
from config import *                                # load configuration options

from graphviz import Digraph
import networkx as nx
import datetime
import random
import re
import angr
import textwrap




# -------------------------------------------------------------------------------------------------

''' =========================================================================================== '''
'''                                    CONSTANT DECLARATIONS                                    '''
''' =========================================================================================== '''

# -------------------------------------------------------------------------------------------------
RETURN_SUCCESS     = 0                              # return code for success
RETURN_FAILURE     = -1                             # return code for failure

DBG_LVL_0          = 0                              # debug level 0: Display no information
DBG_LVL_1          = 1                              # debug level 1: Display minimum information
DBG_LVL_2          = 2                              # debug level 2: Display basic information
DBG_LVL_3          = 3                              # debug level 3: Display detailed information
DBG_LVL_4          = 4                              # debug level 3: Display all information

INFINITY           = 9999999                        # value of infinity

START_PC           = 0                              # PC of the for the 1st statement

ADDR2NODE          = { }                            # map addresses to basic block nodes
ADDR2FUNC          = { }                            # map basic block addresses to their functions
STR2BV             = { }                            # map strings to bitvectors


# WARNING: be very careful how to set rbp
FRAMEPTR_BASE_ADDR = RSP_BASE_ADDR + 0xc00          # base address of rbp (when it's used)

HARDWARE_REGISTERS = [                              # x64 hardware registers
    'rax', 'rdx', 'rcx', 'rbx', 'rdi', 'rsi', 'rsp', 'rbp',
    'r8',  'r9',  'r10', 'r11', 'r12', 'r13', 'r14', 'r15' 
]

SYM2ADDR = { }

SYMBOLIC_FILENAME = 'foo.txt'                       # filename for the symbolic execution to use



# -------------------------------------------------------------------------------------------------

''' =========================================================================================== '''
'''                                     AUXILIARY FUNCTIONS                                     '''
''' =========================================================================================== '''

# -------------------------------------------------------------------------------------------------
dbg_lvl = DBG_LVL_0                                 # initially, debug level is set to 0


# -------------------------------------------------------------------------------------------------
# set_dbg_lvl(): Set the current debug level. This is a small trick to share a variable between
#   modules. We set the debug level once during startup, so we don't have to carry it around the
#   modules.
# 
# :Arg lvl: Desired debug lebel.
# :Ret: None.
#
def set_dbg_lvl( lvl ):
    global dbg_lvl                                  # use the global var     
    if lvl: dbg_lvl = lvl                           # set it accordingly (if lvl is proper)



# ---------------------------------------------------------------------------------------------
# to_uid(): Cast program counter (PC) to unique ID (UID).
#
# :Arg pc: The program counter
# :Ret: The uid.
#
def to_uid( pc ):
    if not re.match(r'^@__[0-9]+$', pc):            # verify pc
        raise Exception("Invalid Program counter '%s'." % pc)

    return int(pc[3:])                              # simply drop the first 3 characters



# ---------------------------------------------------------------------------------------------
# pretty_list(): Cast a list into a pretty string, for displaying to the user. This can be
#       also done using join(), but code starts getting ugly when we have to cast each element.
#
# :Arg uglylist: The list to work on
# :Ret: A string containing a pretty "join" of the list.
#
def pretty_list( uglylist, delimiter=' - '):
    pretty = ''                                     # the final string

    for elt in uglylist:
        if isinstance(elt, int) or isinstance(elt, long):
            pretty += delimiter + '%x' % elt

        elif isinstance(elt, str):
            pretty += delimiter + elt

        elif isinstance(elt, angr.analyses.cfg.cfg_node.CFGNode):
            pretty += delimiter + '%x' % elt.addr

        else:
            fatal("Unsupported list element type'%s'" % str(type(elt)))


    # drop the first delimiter (if exists) and return string
    return pretty[len(delimiter):] if pretty else ''



# -------------------------------------------------------------------------------------------------
# to_edges(): Convert a path to edges. That is, given the path P = ['A', 'B', 'C', 'D', 'E'],
#       return its edges: [('A', 'B'), ('B', 'C'), ('C', 'D'), ('D', 'E')]. Function is a 
#       generator, so it returns one edge at a time.
#
#       Note that function can be implemented with a single line: "return zip(path, path[1:])".
#       However, the problem with zip() is that it creates 2 more copies of the list, which is
#       not very efficient, when paths are long and all we want is to iterate over the edges.
#
# :Arg path: A list that contains a path
# :Arg direction: Edge direction (forward/backward)
# :Ret: Function is a generator. Each time the next edge from the path is returned.
#
def to_edges( path, direction='forward' ):
    if len(path) < 2: return                        # nothing to do

    u = path[0]                                     # get the 1st node
    for v in path[1:]:
        if   direction == 'forward':  yield (u, v)  # return the previous and the current node
        elif direction == 'backward': yield (v, u)  # or return the backward edge

        u = v                                       # update previous node



# -------------------------------------------------------------------------------------------------
# mk_reverse_adj(): Given an Adjacency List, make the Reverse Adjacency List.
#
# :Arg adj: The Adjacency List
# :Ret: Function returns a dictionary which encodes the Reverse Adjacency List.
#
def mk_reverse_adj( adj ):        
        radj = { }

        for a, b in adj.iteritems():
            for c in b:
                radj.setdefault(c, []).append(a)

        return radj



# -------------------------------------------------------------------------------------------------
# disjoint(): Check whether two sets are disjoint or not.
#
# :Arg set_a: The first set
# :Arg set_b: The second set
# :Ret: If sets are disjoint, function returns True. Otherwise it returns False.
#
def disjoint( set_a, set_b ):
    for a in set_a:
        for b in set_b:
            if a == b: 
                return False

    return True



# -------------------------------------------------------------------------------------------------
# log(): Log execution statistics to a file.
#
# :Arg msg: Message to log
# :Ret: None.
#
def log( msg ):
    pass                                            # not used.



# -------------------------------------------------------------------------------------------------

''' =========================================================================================== '''
'''                                     PRINTING FUNCTIONS                                      '''
''' =========================================================================================== '''

# -------------------------------------------------------------------------------------------------
# now(): Get current time. Time is prepended to every print statement.
#
# :Ret: A string containing the current time.
#
def now():
    return '[%s]' % datetime.datetime.now().strftime("%H:%M:%S,%f")[:-3]



# -------------------------------------------------------------------------------------------------
# dbg_prnt(): Display a debug message to the user.
#
# :Arg lvl: Message's debug level
# :Arg msg: Message to print
# :Arg pre: Message prefix (OPTIONAL)
# :Ret: None.
#
def dbg_prnt( lvl, msg, pre='[+] ' ):
    if dbg_lvl >= lvl:                              # print only if you're in the right level
        print now(), pre + msg



# -------------------------------------------------------------------------------------------------
# dbg_arb(): Display a debug message followed by an arbitrary data structure to the user.
#
# :Arg lvl: Message's debug level
# :Arg msg: Message to print
# :Arg arb: The arbitrary data struct (e.g., list, dict) to print
# :Arg pre: Message prefix (OPTIONAL)
# :Ret: None.
#
def dbg_arb( lvl, msg, arb, pre='[+] ' ):
    if dbg_lvl >= lvl:                              # print only if you're in the right level
        print now(), pre + msg, arb
    


# -------------------------------------------------------------------------------------------------
# func_name(): Convert an address to the name of its function, or
# "__unknown" if it cannot be found.
#
# :Arg addr: The address to lookup
# :Ret: Returns a string with the name of the function containing the address, or "__unknown".
#
def func_name ( addr ):
    if addr in ADDR2FUNC:
        return ADDR2FUNC[addr].name
    else:
        return "__unknown"



# -------------------------------------------------------------------------------------------------
# fatal(): This function is invoked when a fatal error occurs. It prints the error and terminates
#       the program.
#
# :Arg err: Error message to print
# :Ret: None.
#
def fatal( err ):
    print '\033[91m%s [FATAL]' % now(), err + '.\033[0m'
    exit( RETURN_FAILURE )



# -------------------------------------------------------------------------------------------------
# error(): This function is invoked when a non-fatal error occurs. It prints the error without
#       terminating the program.
#
# :Arg err: Error message to print
# :Ret: None.
#
def error( err ):
    print '\033[91m%s [ERROR]' % now(), err + '.\033[0m'
    


# -------------------------------------------------------------------------------------------------
# warn(): Print a warning.
#
# :Arg warning: Warning to print
# :Ret: None.
#
def warn( warn, lvl=DBG_LVL_0 ):
    if dbg_lvl >= lvl:                              # print only if you're in the right level
        print  '\033[93m%s [WARNING]' % now(),  warn + '.\033[0m'
    


# -------------------------------------------------------------------------------------------------
# warn(): Print an emphasized message.
#
# :Arg msg: Message to pring
# :Arg lvl: Message's debug level
# :Arg pre: Message prefix (OPTIONAL)# :Ret: None.
# :Ret: None.
#
def emph( msg, lvl=DBG_LVL_0 , pre='[*] '):
    # default mode is to print always
    if dbg_lvl >= lvl:                              # print only if you're in the right level
        print  '\033[0;32m%s' % now(), pre + msg + '\033[0m'



# -------------------------------------------------------------------------------------------------
# bold(): Emphasize a number (bold).
#
# :Arg num: Number to make bold
# :Arg ty: The type of the number (int / float)
# :Arg pad: Zero padding size (OPTIONAL)
# :Ret: The emphasized number.
#
def bold( num, ty='int', pad=None ):
    fms = 'd' if ty == 'int' else '.2f'           # select the format string (int / float)

    if not pad:
        return ("\033[1m%" + fms + "\033[21m") % num
    else:
        # this is a double format string (recursive)        
        return ("\033[1m" + (("%%%d" + fms) % pad) + "\033[21m") % num 



# -------------------------------------------------------------------------------------------------
# bolds(): Emphasize a string (bold).
#
# :Arg string: Message to make bold
# :Ret: The emphasized string.
#
def bolds( string ):
    return "\033[1m%s\033[21m" % string             # print in bold (and unbold)



# -------------------------------------------------------------------------------------------------
# rainbow(): Print a string with rainbow colors.
#
# :Arg string: Message to make rainbow.
# :Ret: None.
#
def rainbow( string ):
    RED     = lambda key : "\033[91m%c\033[0m" % key
    GREEN   = lambda key : "\033[92m%c\033[0m" % key
    YELLOW  = lambda key : "\033[93m%c\033[0m" % key
    MAGENTA = lambda key : "\033[95m%c\033[0m" % key
    CYAN    = lambda key : "\033[96m%c\033[0m" % key
   
    return ''.join([{ 0 : RED, 
                      1 : CYAN, 
                      2 : YELLOW, 
                      3 : MAGENTA, 
                      4 : GREEN 
                    }[ ctr % 5 ](ch) for ctr, ch in enumerate(string)])

