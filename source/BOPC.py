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
# BOPC.py:
#
#
# This is the main module of BOPC. It configures the environment and launches the other modules.
#
# -------------------------------------------------------------------------------------------------
from coreutils import *
import absblk     as A
import compile    as C
import optimize   as O
import mark       as M
import search     as S


import ntpath
import angr
import os



# ------------------------------------------------------------------------------------------------
# Constant Definitions
# ------------------------------------------------------------------------------------------------
VERSION  = 'v2.1'                                   # current version
comments = ''                                       # Additional comments to display on startup


# ---------------------------------------------------------------------------------------------
# load(): Load the target binary and generate its CFG.
#
# :Arg filename: Binary's file name
# :Ret: Function returns
#
def load( filename ):
    # load the binary (exception is thrown if name is invalid)
    project = angr.Project(filename, load_options={'auto_load_libs': False})



    # generate CFG
    dbg_prnt(DBG_LVL_0, "Generating CFG. It might take a while...")
    CFG = project.analyses.CFGFast()
    dbg_prnt(DBG_LVL_0, "CFG generated.")


    # normalize CFG (i.e. make sure that there are no overlapping basic blocks)
    dbg_prnt(DBG_LVL_0, "Normalizing CFG...")
    CFG.normalize()

    # normalize every function object as well
    for _, func in project.kb.functions.iteritems():
        if not func.normalized:
            func.normalize()

    dbg_prnt(DBG_LVL_0, "Done.")


    emph("CFG has %s nodes and %s edges" %
                (bold(len(CFG.graph.nodes())), bold(len(CFG.graph.edges()))))


    # create a quick mapping between addresses and nodes (basic blocks)
    for node in CFG.graph.nodes():
        ADDR2NODE[ node.addr ] = node


    # create a quick mapping between basic block addresses and their corresponding functions
    for _, func in CFG.functions.iteritems():       # for each function
        for addr in func.block_addrs:               # for each basic block in that function
            ADDR2FUNC[ addr ] = func


    return project, CFG



# ---------------------------------------------------------------------------------------------
# abstract(): Abstract the CFG and apply any further abstraction-related operations.
#
# :Arg mark: A valid graph marking object.
# :Arg mode: Abstraction mode (load, save, saveonly, none)
# :Arg filename: Abstraction's file name (if applicable)
# :Ret: None.
#
def abstract( mark, filename ):
    mark.load_abstractions(filename)            # simply load the abstractions

    return 0


# -------------------------------------------------------------------------------------------------
# main(): This is the main function of BOPC.
#
# Ret: None.
#
if __name__ == '__main__':
    set_dbg_lvl( DBG_LVL_4 )                 # set debug level in coreutils
    binary = "../evaluation/nullhttpd"
    source = "../payloads/regmod.spl"
    entry = 0x4026cf

    if entry:
        IR = C.compile(source)
        IR.compile()                                # compile the SPL payload

        IR = O.optimize(IR.get_ir())
        IR.optimize(mode="none")            # optimize IR (if needed)


        project, CFG = load(binary)
        mark         = M.mark(project, CFG, IR, 'puts')

        if abstract(mark, binary) > -1:

            X = mark.mark_candidate(sorted(map(lambda s : tuple(s.split('=')), [])))

            if not X:
                print 'abort';
                exit()


            # extract payload name (without the extenstion)
            payload_name = ntpath.basename(source)
            payload_name = os.path.splitext(payload_name)[0]


            try:
                options = {
                    'format'     : "gdb",
                    'solutions'  : "one",
                    'mapping-id' : int(-1),
                    'mapping'    : sorted(map(lambda s : tuple(s.split('=')), [])),
                    'filename'   : '%s-%s' % (binary, payload_name),
                    'enum'       : False,

                    'simulate'   : False,
                    '#mappings'  : 0,
                    '#solutions' : 0
                }

            except ValueError:
                fatal("'mapping' argument must be an integer")


            tsearch = S.search(project, CFG, IR, entry, options)
            tsearch.trace_searching(mark)


