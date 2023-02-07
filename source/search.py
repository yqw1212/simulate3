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
# search.py:
#
# This module is the "heart" of BOPC. It implements the trace searching algorithm that looks
# for a trace that uses several accepted blocks (and no clobbering blokcs) that successfully
# reconstructs the execution of the SPL payload.
#
# -------------------------------------------------------------------------------------------------
from coreutils import *
import map      as M
import path     as P
import delta    as D
import simulate as S

import math



# -------------------------------------------------------------------------------------------------
# search: This class searches for subsets of accepted blocks that could reconstruct the execution
#   of the SPL payload.
#
class search:
    ''' ======================================================================================= '''
    '''                                   INTERNAL FUNCTIONS                                    '''
    ''' ======================================================================================= '''

    # ---------------------------------------------------------------------------------------------
    # __remove_goto: Remove goto statements. Goto are not real statements; that is they don't 
    #       require an accepted block to get executed. Therefore if they stay on the statement
    #       list, we will have a lot of issues. Thus, the best solution is to remove them.
    #       
    # :Arg accepted: A dictionary with all accepted blocks
    # :Arg adj: The adjacency list.
    # :Ret: Function returns a tuple that has the updated adjacency list and another list with all
    #       goto statements that should be removed.
    #
    def __remove_goto( self, accepted, adj ):
        dbg_prnt(DBG_LVL_3, "Removing goto statements...")
        
        # Build the reverse adjacency list (r_adj)
        r_adj = self.__mk_reverse_adjacency_list(adj)
        rm    = []                                  # remove list


        for stmt in self.__IR:                      # iterate over goto statements
            if stmt['type'] == 'jump':               
                rm.append(stmt['uid'])              # add statement to remove list

                # fix every statement that points to the goto
                for src in r_adj[ stmt['uid'] ]:

                    # remove edges that point to the goto
                    adj[src]  = filter(lambda x : x != stmt['uid'], adj[src])                    
                    adj[src] += adj[stmt['uid']]    # add the bypass edge

                    # if we have multiple gotos chained together, also fix the 'target' attribute
                    if  self.__IR[ src ]['type'] == 'jump':
                        self.__IR[ src ]['target'] = stmt['target']


                del adj[ stmt['uid'] ]              # we don't need the goto anymore

                # Now we have to update r_adj as well. The simplest way to do that, is to 
                # rebuild it from scratch (not efficient, but adj is pretty small)
                r_adj = self.__mk_reverse_adjacency_list(adj)


        # return the updated adjacency and the UIDs of the goto statements
        return adj, rm



    # ---------------------------------------------------------------------------------------------
    # __mk_adjacency_list(): This function builds the adjacency list between SPL statements. That
    #       is, the adjacency list indicates the set of possible statements that can be executed
    #       after i-th statement (statement i does not always go to i+1).
    #
    # :Arg stmt_l: A (shuffled) list with the UIDs of all SPL statements.
    # :Ret: A dictionary that has an entry for each statement (except the last one) that shows the
    #       next statements
    #
    def __mk_adjacency_list( self, stmt_l ):
        # To simply this process, we make some observations first.
        #   [1]. The first statement cannot be a conditional jump (it uses a register)
        #   [2]. goto and conditional jumps are single groups
        #   [3]. When a group has >1 statements, then i -> i+1 for each statement in the group

        adj  = { }                                  # The adjacency list (dictionary)
        prev = stmt_l[0]                            # get the first statement

        for curr in stmt_l[1:]:                     # for each statement
            # goto statements have a single target (probably not i+1)
            if self.__IR[prev]['type'] == 'jump':
                adj[prev] = [to_uid(self.__IR[prev]['target'])]
                
            # conditional jumps have two targets (the one is i+1)
            elif self.__IR[prev]['type'] == 'cond':
                # Taken branch always first
                adj[prev] = [to_uid(self.__IR[prev]['target']), curr]

            # every other statement have i+1 as target
            else:
                adj[prev] = [curr]

            prev = curr                             # update previous statement and move on


        # special case for the last statement: There's no next statement, unless it's a jump
        if self.__IR[curr]['type'] in ['jump', 'cond']:
            adj[curr] = [to_uid(self.__IR[ prev ]['target'])]
            

        dbg_arb(DBG_LVL_3, "SPL statement adjacency list", adj)

        return adj                                  # return the adjacency list



    # ---------------------------------------------------------------------------------------------
    # __mk_reverse_adjacency_list(): This function builds the reverse adjacency list between SPL
    #       statements. That is, it actually reverses the edge direction
    #
    # :Arg adj: The adjacency list
    # :Ret: A dictionary that has an entry for each statement (except the last one) that shows the
    #       *previous* statements
    #
    def __mk_reverse_adjacency_list( self, adj ):
        rev_adj = { }

        for a, b in adj.iteritems():
            for c in b:
                rev_adj.setdefault(c, []).append(a)

        return rev_adj



    # ---------------------------------------------------------------------------------------------
    # __shuffle: Shuffle the statements. This function is a generator that every time returns the
    #       SPL statements in a different order, so they can be executed out-of-order. The order
    #       must preserve the execution flow, so statements have to be shuffled in groups.
    #       
    # :Arg accepted: A dictionary with all accepted blocks
    # :Ret: Function is a generator, so each time a different permutation of the SPL payload is 
    #       returned. The permutation is an ordered list with the UIDs of the SPL statements.
    #
    def __shuffle( self, accepted ):
        # -------------------------------------------------------------------------------
        # kth_permutation(): This internal function returns the k-th permutation of a
        #       given sequence of numbers.
        #
        # :Arg group: Group to work on
        # :Arg k: The index of the k-th permutation
        #
        def kth_permutation( group, k ):
            tmpgrp = list(group[:])                 # create a temporary copy of the group
            shuff  = []                             # result            
            fact   = math.factorial(len(group))     # find group's factorial            
            k     %= fact                           # don't go beyonnd n!

            while tmpgrp:
                fact = fact / len(tmpgrp)           # n! /= n
                what, k = k // fact, k % fact       # select element and update k
                
                # add element to shuffle list and remove it from temporary group
                shuff.append( tmpgrp.pop(what) )

            return shuff

        # -------------------------------------------------------------------------------

  
        # ---------------------------------------------------------------------
        # Initialize permutation struct according to statement groups
        # ---------------------------------------------------------------------
        permlist = []                               # permutation list
        upper    = 1                                # total number of permutations

        # iterate on statement groups. Statements in each group can be executed in any
        # order without affecting the execution flow of the SPL program.
        for group in self.__IR.itergroup():
            G = sorted([stmt['uid'] for stmt in group if stmt['type'] != 'varset'])
            
            if G:                                   # discard empty groups
                fact = math.factorial(len(G))         

                # add group to the permutation list. Each element contains the group uids (G),
                # the total number of permutations (n) and the current permutation (i).    
                permlist.append( {'G':G, 'n':fact, 'i':1} )

                upper *= fact                       # calculate upper bound of permutations


        # update upper bound according to the configuration
        if N_OUT_OF_ORDER_ATTEMPTS != -1 and upper > N_OUT_OF_ORDER_ATTEMPTS:
            upper = N_OUT_OF_ORDER_ATTEMPTS


        # return the first permutation. Simply merge all groups (G) from 'permlist'
        yield [x for p in permlist for x in p['G']]


        # ---------------------------------------------------------------------
        # Calculate the remaining upper-1 permutations (1 at a time)
        # ---------------------------------------------------------------------
        # make a list of the permutations groups. E.g.: [[0], [8, 10, 12], [14], [16, 18]]
        perm = [p['G'] for p in permlist]

        for i in range(upper - 1):            
            for j in range(len(permlist)):          # for each permutation group

                # calculate the (i-th + 1) permutation (the next one) for the current group
                perm[j] = kth_permutation(permlist[j]['G'], permlist[j]['i'])
                
                # check if we exhausted all permutations for that group
                if  permlist[j]['i'] % permlist[j]['n'] != 0:
                    permlist[j]['i'] += 1           # if not simply increment current index
                    break                           # and don't move on the next group

                permlist[j]['i'] += 1               # increment index and move on the next group
                
            yield [x for p in perm for x in p]      # return the next permutation (merge first)
 


    # ---------------------------------------------------------------------------------------------
    # __enum_tree(): TODO
    #
    # 
    # :Ret: If function returns 0, we have found a solution!
    #
    def __enum_tree( self, tree, simulation, path=[], prev_uid=-1, totpath=set()  ):

        print 'TREE', tree

        # ---------------------------------------------------------------------
        # If tree is empty we have reached a solution
        # ---------------------------------------------------------------------
        if not tree:
            dbg_arb(DBG_LVL_2, 'Path simulated successfully: ', path)

            # Ok we have executed all statements (for one branch of the Hk) successfully.
            # Execution has stopped at the beginning of the accepted block. For goto and
            # return statements that's ok, but for regset, regmod, call and cond we have
            # to execute the final block as well.

            if self.__IR[prev_uid]['type'] not in ['jump', 'return'] or \
                 self.__IR[prev_uid]['type'] == 'return' and self.__IR[prev_uid]['target'] == -1:

                dbg_prnt(DBG_LVL_2, "Final statement is '%s', so we need to do one more step..." % 
                                        self.__IR[prev_uid]['type'])

                term = simulation.step(self.__IR[prev_uid])

                if term == -1: return -1

                self.__terminals += term

            else: self.__terminals.append( path[-1][1] )


            emph('Solution found!', DBG_LVL_1)

            return 0


        # ---------------------------------------------------------------------
        # Tree is not empty and next node is unique
        # ---------------------------------------------------------------------
        elif isinstance(tree[0], tuple):
            uid, currb, nextb = tree[0]
            

            print uid, self.__IR[uid], tree[0], self.__adj
            print 'PATH', path, [p[2] for p in path] #, self.__adj[ uid ][0]


            if nextb == -1:
                nextb = currb                   # make target to be itself

            if currb == -1:
                subpath = []
            else:

                subpath = simulation.simulate_edge(currb, nextb, uid)
                if subpath == None:
                    return -1

            for (a,b) in to_edges(subpath):
                totpath.add((a,b))

            # edge simulated. Move on the next one!
            if self.__enum_tree(tree[1:], simulation, path+[(currb, nextb, uid)], uid, totpath) < 0:
                return -1

        else:
            raise Exception('Malformed tree!')

        return 0
        


    # ---------------------------------------------------------------------------------------------
    # __mapping_callback(): This callback function is invoked every time that a register and a
    #       variable mappings are found.
    #
    # :Arg regmap: The register mapping as a list of (virtual_register, real_register) tuples
    # :Arg varmap: The variable mapping as a list of (name, value) tuples
    # :Ret: A returned value of 0 causes the callback function to be invoked again with a different
    #       mapping (it means that the current mapping wasn't suitable). When function returns -1,
    #       the enumeration process halts and the callback function returns to the enum_mappings()
    #       caller (this means that the current mapping ended up in a valid solution).
    #
    def __mapping_callback( self, regmap, varmap ):
        self.__varmap = varmap                      # save current variable mapping
        self.__regmap = regmap
        self.__ctr   += 1                           # increment counter


        
        # if case that you want to apply a specific mapping, discard all others
        if self.__options['mapping-id'] != -1 and self.__ctr < self.__options['mapping-id']:
            # dbg_prnt(DBG_LVL_1, "Discard current mapping.")
            return 0


        # ---------------------------------------------------------------------
        # Pretty-print the register/variable mappings
        # ---------------------------------------------------------------------
        emph('Trying mapping #%s:' % bold(self.__ctr), DBG_LVL_1)

        s = ['%s <-> %s' % (bolds(virt), bolds(real)) for virt, real in regmap]
        emph('\tRegisters: %s' % ' | '.join(s), DBG_LVL_1)


        s = ['%s <-> %s' % (bolds(var), bolds(hex(val) if isinstance(val, long) else str(val))) 
                    for var, val in varmap]
        emph('\tVariables: %s' % ' | '.join(s), DBG_LVL_1)



        # ---------------------------------------------------------------------
        # Apply (any) filters to the current mapping (DEBUG)
        # ---------------------------------------------------------------------

        # if you want to enumerate mappings, don't move on
        if self.__options['enum']:
            return 0

    
        self.__options['#mappings'] += 1



        # ---------------------------------------------------------------------
        # Identify accepted and clobbering blocks
        # ---------------------------------------------------------------------


        # given the current mapping, go back to the CFG and mark all accepted blocks
        accblks, rsvp = self.__mark.mark_accepted(regmap, varmap)  
        
        # if there is (are) >= 1 statement(s) that don't have accepted blocks, discard mapping
        if not accblks:
            dbg_prnt(DBG_LVL_1, 'There are not enough accepted blocks. Discard mapping...')
            return 0                                # try another mapping



        # if there are enough accepted blocks, go back to the CFG and mark clobbering blocks
        cloblks = self.__mark.mark_clobbering( regmap, varmap )


        # add entry point to accblks (with min uid) to avoid special cases
        accblks[ START_PC ] = [self.__entry]


        # ---------------------------------------------------------------------
        # Shuflle statements and build the Delta Graph
        # ---------------------------------------------------------------------
        dbg_prnt(DBG_LVL_1, "Shuffling SPL payload...")

        for perm in self.__shuffle(accblks):        # start shuffling IR

            dbg_arb(DBG_LVL_1, 'Statement order:', perm)


            # build the adjacency list for that order
            adj = self.__mk_adjacency_list(perm)
            self.__adj = adj
            # remove goto statements as they are problematic
            adj, rm = self.__remove_goto(accblks, adj)

            perm = filter(lambda x : x not in rm, perm)
            perm = [(y, accblks[y]) for y in perm]

            dbg_arb(DBG_LVL_3, "Updated SPL statement adjacency list", adj)
            

            # create the Delta Graph for the given permutation        
            DG = D.delta(self.__cfg, self.__entry, perm, cloblks, adj)
       

            # select the K minimum induced subgraphs Hk from the Delta Graph
            # Hk = a subset of accepted blocks that reconstruct the execution of the SPL payload) 
            for size, Hk in DG.k_min_induced_subgraphs( PARAMETER_K ): 
                if size < 0:                        # Delta Graph disconnected?
                    dbg_prnt(DBG_LVL_1, "Delta Graph is disconnected.")
                    break                           # try another permutation (or mapping)
                
                # Paths that are too long should be discarded as it's unlikely to find a trace
                if size > MAX_ALLOWED_TRACE_SIZE:
                    dbg_prnt(DBG_LVL_1, "Subgraph size is too long (%d > %d). Discard it." % 
                                                    (size, MAX_ALLOWED_TRACE_SIZE))
                    break                           # try another permutation (or mapping)

                         
                # subgraph is ok. Flatten it and make it a "tree", to easily process it
                tree, pretty_tree = DG.flatten_graph(Hk)                

                emph('Flattened subgraph (size %d): %s' % (size, bolds(str(pretty_tree))), DBG_LVL_2)
                

                # TODO: this check will discard "trivial" solutions (all in 1 block)
                if size == 0:
                    warn('Delta graph found but it has size 0' )
                    # continue


                # enumerate all paths, and fork accordingly


                # Symbolic execution used?
                self.__options['simulate'] = True


                # TODO: In case of conditional jump, we'll have multiple "final" states.
                # We should check whether those states have conflicting constraints.
                #
                dbg_prnt(DBG_LVL_2, "Enumerating Tree...")

                self.__simstash = []


                entry = self.__entry            # use the regular entry point
                self.__cfg_sp = P._cfg_shortest_path(self.__cfg, cloblks, adj)
                try:
                    simulation = S.simulate(self.__proj, self.__cfg_sp, entry)
                except Exception, e:
                    dbg_prnt(DBG_LVL_2, "Cannot create simulation object. Discard current Hk")
                    continue


                self.__sim_objs = [simulation]
                self.__terminals = [tree[0][1]]

                self.__enum_tree( tree, simulation )


            del DG

        return 0                                    # try another mapping...      



    ''' ======================================================================================= '''
    '''                                     CLASS INTERFACE                                     '''
    ''' ======================================================================================= '''

    # ---------------------------------------------------------------------------------------------
    # __init__(): Class constructor. Simply initialize private members
    #
    # :Arg project: Instance of angr project
    # :Arg cfg: Binary's CFG
    # :Arg IR: SPL's Intermediate Representation (IR)
    # :Arg entry: Binary's entry point
    # :Arg options: Addtional options needed for the trace searching
    #
    def __init__( self, project, cfg, IR, entry, options ):
        self.__proj    = project                    # store arguments internally
        self.__cfg     = cfg
        self.__IR      = IR
        self.__entry   = entry
        self.__options = options

        self.__reg   = { }
        self.__mem   = { }
        self.__ext   = { }       

        self.__solved     = False
        self.__nsolutions = 0

        # make sure that the upper bound is valid
        assert(N_OUT_OF_ORDER_ATTEMPTS > 0 or N_OUT_OF_ORDER_ATTEMPTS == -1)
              


    # ---------------------------------------------------------------------------------------------
    # trace_searching(): Build a trace that cnnects all functional blocks.
    #
    # :Arg mark: A graph marking object
    # :Arg 
    # :Ret: If function can successfully find trace, function returns True. Otherwise it returns
    #       False.
    #
    def trace_searching( self, mark ):
        dbg_prnt(DBG_LVL_1, "Trace searching algorithm started.")

        self.__mark = mark                          # store object internally
        self.__ctr  = 0                             # clear mapping counter


        # create a mapping object
        mapping = M.map(mark.map_graph, self.__IR.nregs, self.__IR.nregvars)

        # enumerate all possible register and variable mappings
        rval = mapping.enum_mappings( self.__mapping_callback )

        dbg_prnt(DBG_LVL_1, "Trace searching algorithm finished with exit code %s" % bold(rval))
        
        return rval



# -------------------------------------------------------------------------------------------------
