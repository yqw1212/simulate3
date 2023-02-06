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
# simulate.py:
#
# This module performs the concolic execution. That is it verifies a solution proposed by search
# module. For more details please refer to the paper.
#
#
# * * * ---===== TODO list =====--- * * *
#
#   [1]. Consider overlapping cases. For instance, when we write e.g., 8 bytes at address X and
#        then we write 4 bytes at address X+1, we may have issues
#
#
# -------------------------------------------------------------------------------------------------
from coreutils import *

import angr
import archinfo
import copy

# ------------------------------------------------------------------------------------------------
# Constant Definitions
# ------------------------------------------------------------------------------------------------

# WARNING: In case that relative addresses fail, adjust them.
# TODO: Add command line options for them.
MAX_MEM_UNIT_BYTES = 8  # max. memory unit size (for x64 is 8 bytes)
MAX_MEM_UNIT_BITS = MAX_MEM_UNIT_BYTES << 3  # max. memory unit size in bits

ALLOCATOR_BASE_ADDR = 0xd8000000  # the base address of the allocator
ALLOCATOR_GRANULARITY = 0x1000  # the allocation size
ALLOCATOR_CEIL_ADDR = 0xd9000000  # the upper bound of the allocator
ALLOCATOR_NAME = '$alloca'

POOLVAR_BASE_ADDR = 0xca000000  # the base address of the pool
POOLVAR_GRANULARITY = 0x1000  # (safe) offset between pools
POOLVAR_NAME = '$pool'

SIM_MODE_INVALID = 0xffff  # invalid simulation mode
SIM_MODE_FUNCTIONAL = 0x0001  # simulation mode: Functional
SIM_MODE_DISPATCH = 0x0000  # simulation mode: Dispath

MAX_BOUND = 0x4000

# addresses that are not recognized as R/W but they are
_whitelist_ = [
    0x2010028,  # fs:0x28
    0xc0000000,  # __errno_location
    0xc0000070  # fopen() internal
]



EXTERNAL_UNINITIALIZED = -1


# -------------------------------------------------------------------------------------------------
# simulate: This class simulates the execution between a pair of accepted blocks
#
class simulate:
    ''' ======================================================================================= '''
    '''                             INTERNAL FUNCTIONS - AUXILIARY                              '''
    ''' ======================================================================================= '''

    # ---------------------------------------------------------------------------------------------
    # __in_constraints(): This function checks whether a symbolic variable is part of the
    #       constraints.
    #
    # :Arg symv: The symbolic variable to check
    # :Arg state: Current state of the symbolic execution
    # :Ret: If symv is in constraints, function returns True. Otherwise it returns False.
    #
    def __in_constraints(self, symv, state=None):
        if not state:  # if no state is given, use the current one
            state = self.__state

        # drop the "uninitialized" thing from everywhere
        symvstr = symv.shallow_repr().replace("{UNINITIALIZED}", "")

        # We may have this in the constraints:
        #   <Bool Reverse(mem_801_64[7:0] .. Reverse(mem_801_64)[55:0]) != 0x0>
        #
        # But symvstr is:
        #   <BV64 Reverse(mem_801_64[7:0] .. Reverse(mem_801_64)[55:0])>
        #
        # A quick fix is to drop the type:

        symvstr2 = symvstr[symvstr.find(' '):-1]


        # this is the old style check
        if symvstr2 in ' '.join([c.shallow_repr().replace("{UNINITIALIZED}", "") \
                                 for c in state.se.constraints]):
            return True

        # reinforce function with a stronger check
        for constraint in state.se.constraints:

            try:
                # treat constraint as an AST and iterate over its leaves
                for leaf in constraint.recursive_leaf_asts:

                    # we can't compare them directly, so we cast them into strings first
                    # (not a very "clean" way to do that, but it works)
                    if leaf.shallow_repr().replace("{UNINITIALIZED}", "") == symvstr:
                        return True  # symbolic variable found!

            except Exception, err:
                pass

        return False  # symbolic variable not found

    # ---------------------------------------------------------------------------------------------
    # __getreg(): Get the symbolic value of a register that has in the current state.
    #
    # :Arg reg: The name of the register
    # :Arg state: Current state of the symbolic execution
    # :Ret: The symbolic value for that register.
    #
    def __getreg(self, reg, state=None):
        if not state:  # if no state is given, use the current one
            state = self.__state

        try:
            return {
                'rax': state.regs.rax,
                'rbx': state.regs.rbx,
                'rcx': state.regs.rcx,
                'rdx': state.regs.rdx,
                'rsi': state.regs.rsi,
                'rdi': state.regs.rdi,
                'rbp': state.regs.rbp,
                'rsp': state.regs.rsp,
                'r8': state.regs.r8,
                'r08': state.regs.r8,
                'r9': state.regs.r9,
                'r09': state.regs.r9,
                'r10': state.regs.r10,
                'r11': state.regs.r11,
                'r12': state.regs.r12,
                'r13': state.regs.r13,
                'r14': state.regs.r14,
                'r15': state.regs.r15,
            }[reg]
        except KeyError:
            fatal("Unknow register '%s'" % reg)

    # ---------------------------------------------------------------------------------------------
    # __mread(): This function reads from memory. The problem here is that we have to explicitly
    #       specify how to interpret memory (.uint8_t, .uint32_t, etc.), according to the number
    #       of bytes that we want to read. This results in cumbersome code, as we need a different
    #       case for every possible length, so we provide a simply interface through this function.
    #
    # :Arg state: Current state of the symbolic execution
    # :Arg addr: Address to read from
    # :Arg length: Number of bytes to read
    # :Ret: The contents of the desired memory "area".
    #
    def __mread(self, state, addr, length):

        return state.memory.load(addr, length, endness=archinfo.Endness.LE)



    # ---------------------------------------------------------------------------------------------
    # __mwrite(): Similar to __mread() but this function writes to memory instead.
    #
    # :Arg state: Current state of the symbolic execution
    # :Arg addr: Address to write to
    # :Arg length: Number of bytes to write
    # :Ret: None.
    #
    def __mwrite(self, state, addr, length, value):
        state.memory.store(addr, value, length, endness=archinfo.Endness.LE)



    # ---------------------------------------------------------------------------------------------
    # __get_permissions(): Get
    #
    # :Arg state: Current state of the symbolic execution
    # :Arg addr: Address to write to
    # :Arg length: Number of bytes to write
    # :Ret: None.
    #
    def __get_permissions(self, addr, length=1, state=None):
        if not state:  # if no state is given, use the current one
            state = self.__state


        # special cases first
        if addr < 0x10000:
            return ''

        elif ALLOCATOR_BASE_ADDR <= addr and addr <= ALLOCATOR_CEIL_ADDR:
            return 'RW'

            # TOOD:!!! 0x10000
        elif POOLVAR_BASE_ADDR <= addr and addr <= POOLVAR_BASE_ADDR + self.__plsz + 0x1000:
            return 'RW'

        # special case when a stack address is in the next page
        # TODO: make it relative from STACK_BASE_ADDR
        elif addr & 0x07ffffffffff0000 == 0x07ffffffffff0000:
            return 'RW'

        try:
            for _, sec in self.__proj.loader.main_object.sections_map.iteritems():
                if sec.contains_addr(addr):
                    return ('R' if sec.is_readable else '') + \
                        ('W' if sec.is_writable else '') + \
                        ('X' if sec.is_executable else '')

            permissions = state.se.eval(state.memory.permissions(addr))

            return ('R' if permissions & 4 else '') + \
                ('W' if permissions & 2 else '') + \
                ('X' if permissions & 1 else '')

        except angr.errors.SimMemoryError:
            return ''  # no permissions at all

    # ---------------------------------------------------------------------------------------------
    # __symv_in(): Check whether a symbolic expression contains a given symbolic variable.
    #
    # :Arg symexpr: The symblolic expression
    # :Arg symv: The symbolic variable to look for
    # :Ret: If symexpr contains symv, function returns True. Otherwise it returns False.
    #
    def __symv_in(self, symexpr, symv):
        if symexpr == None or symv == None:  # check special cases
            return False


        try:
            # treat symexpr as an AST and iterate over its leaves
            for leaf in symexpr.recursive_leaf_asts:

                # we can't compare them directly, so we cast them into strings first
                # (not a very "clean" way to do that, but it works)
                if leaf.shallow_repr() == symv.shallow_repr():
                    return True  # variable found!

            return False  # variable not found

        except Exception, err:
            raise Exception('__symv_in() unexpected exception: %s' % str(err))


    # ---------------------------------------------------------------------------------------------
    # __alloc_un(): "Allocate" memory for uninitialized symbolic variables (if needed).
    #
    # :Arg state: Current symbolic state of the execution
    # :Arg symv: The symbolic variable
    # :Ret: If symv is uninitialized, function returns True; otherwise it returns False.
    #
    def __alloc_un(self, state, symv):
        if symv == None:  # make sure that variable is valid
            return False

        # This code works fine for single variables but not for expressions:
        #
        # # nothing to do when variable is not uninitialized (i.e. initialized)
        # if "{UNINITIALIZED}" not in symv.shallow_repr():
        #     return False
        #
        # # After calling __alloc_un(), a variable will still have the UNINITIALIZED keyword
        # # even though, it has a single solution. Avoid initializing a variable twice.
        #
        #
        addr = state.se.eval(symv)  # try to concretize it


        # we say < 0x1000, to catch cases with small offsets:
        # e.g., *<BV64 Reverse(stack_16660_262144[258239:258176]) + 0x68>
        # which gets concretized to 0x68
        if addr < 0x1000 or addr > 0xfffffffffffff000:
            # if addr == 0: # < ALLOCATOR_BASE_ADDR or addr > ALLOCATOR_CEIL_ADDR

            alloca = ALLOCATOR_BASE_ADDR + self.__alloc_size

            # add the right contraint, to make variable, point where you want
            # address now becomes concrete (it has exactly 1 solution)

            # in case that addr > 0, make sure that symv is concretized from 0
            # (otherwise, we'll start before self.__alloc_size)
            x = state.se.BVS('x', 64)

            # this indirection ensure that symv concretized to 64 bits
            state.add_constraints(x == alloca + addr)
            state.add_constraints(symv == x)


            self.__relative[alloca] = '%s + 0x%03x' % (ALLOCATOR_NAME, self.__alloc_size)

            self.__sym[alloca] = symv

            # shift allocator
            self.__alloc_size += ALLOCATOR_GRANULARITY

            return True  # we had an allocation

        return False  # no allocation

    # ---------------------------------------------------------------------------------------------
    # __init_mem(): This function initializes (if needed) a memory cell. When we start execution
    #       from an arbitrary point, it's likely that the memory cell will be empty/uninitialized.
    #       Therefore, we need to assign a symbolic variable to it first.
    #
    #       A special case here is global variables from .bss and .data, which have a default value
    #       of 0. Therefore, these variables are actually uninitialized, but instead of containing
    #       a symbolic variable, they contain the default value (a bitvector of value 0). However,
    #       this can cause problems to the symbolic execution, as variables are already concrete.
    #
    # :Arg state: Current symbolic state of the execution
    # :Arg addr: Address of the variable
    # :Arg length: Length of the variable
    # :Ret: If memory was initialized, function returns True. Otherwise it returns False.
    #
    def __init_mem(self, state, addr, length=MAX_MEM_UNIT_BYTES):
        if addr in self.__mem:  # memory cell is already initialized
            return False

        self.__mem[addr] = length  # simply mark used addresses

        # get ELF sections that give default values to their uninitialized variables
        bss = self.__proj.loader.main_object.sections_map[".bss"]
        data = self.__proj.loader.main_object.sections_map[".data"]

        # print 'INIT MEMORY', hex(addr), self.__mread(state, addr, length)

        # if the memory cell is empty (None) or if the cell is initialized with a
        # default value, then we should give it a symbolic variable. You can also use:
        #       state.inspect.mem_read_expr == None:
        #
        if self.__mread(state, addr, length) == None or \
                bss.min_addr <= addr and addr <= bss.max_addr or \
                data.min_addr <= addr and addr <= data.max_addr or \
                ALLOCATOR_BASE_ADDR <= addr and addr <= ALLOCATOR_CEIL_ADDR:

            # Alternative: state.memory.make_symbolic('mem', addr, length << 3) (big endian)
            symv = state.se.BVS("mem_%x" % addr, length << 3)

            # write symbolic variable to both states (current and original)
            self.__mwrite(state, addr, length, symv)
            self.__mwrite(self.__origst, addr, length, symv)

            # get symbolic variable
            self.__sym[addr] = self.__mread(state, addr, length)

            return True  # memory initialized

        # if it's uninitialized, simply add it variable to the __sym table
        # (but memory is not initialized at all)
        if "{UNINITIALIZED}" in self.__mread(state, addr, length).shallow_repr():
            self.__sym[addr] = self.__mread(state, addr, length)

        return False  # memory not initialized

    # ---------------------------------------------------------------------------------------------

    ''' ======================================================================================= '''
    '''                          INTERNAL FUNCTIONS - EXECUTION HOOKS                           '''
    ''' ======================================================================================= '''

    # ---------------------------------------------------------------------------------------------
    # __dbg_read_hook(): This callback function is invoked when a memory "area" is being read.
    #
    # :Arg state: Current state of the symbolic execution
    # :Ret: None.
    #
    def __dbg_read_hook(self, state):
        if self.__disable_hooks:  # if hooks are disabled, abort
            return

        # if you read/write memory inside the hook, this operation will trigger __dbg_read_hook()
        # again, thus resulting in a endless recursion. We need "exclusive access" here, so we
        # disable hooks inside function's body. This is pretty much like a mutex.
        self.__disable_hooks = True


        print 'state.inspect.mem_read_address', state.inspect.mem_read_address

        # if the address is an uninitialized symbolic variable, it can point to any location,
        # thus, when it's being evaluated it gets a value of 0. To fix this, we "allocate" some
        # memory and we make the address point to it.
        self.__alloc_un(state, state.inspect.mem_read_address)

        # now you can safely, "evaluate" address and concretize it
        addr = state.se.eval(state.inspect.mem_read_address)

        # concretize size (newer versions of angr never set state.inspect.mem_read_length to None)
        if state.inspect.mem_read_length == None:
            size = MAX_MEM_UNIT_BYTES  # if size is None, set it to default
        else:
            size = state.se.eval(state.inspect.mem_read_length)

        self.__init_mem(state, addr, size)  # initialize memory (if needed)

        if state.inspect.instruction:
            insn_addr = state.inspect.instruction
        else:
            insn_addr = state.addr

        dbg_prnt(DBG_LVL_3, '\t0x%08x: mem[0x%x] = %s (%x bytes)' %
                 (insn_addr, addr, self.__mread(state, addr, size), size), pre='[R] ')

        # make sure that the address that you read from has +R permissions
        # TODO: fs:0x28 (canary hits an error here) 0x2010028
        if 'R' not in self.__get_permissions(addr, state) and addr not in _whitelist_:
            raise Exception("Attempted to read from an non-readable address '0x%x'" % addr)

        self.__disable_hooks = False  # release "lock" (i.e., enable hooks again)

    # ---------------------------------------------------------------------------------------------
    # __dbg_write_hook(): This callback function is invoked when a memory "area" is being written.
    #
    # :Arg state: Current state of the symbolic execution
    # :Ret: None.
    #
    def __dbg_write_hook(self, state):
        if self.__disable_hooks:  # if hooks are disabled, abort
            return

        # as in __dbg_read_hook(), we need mutual exclusion here as well
        self.__disable_hooks = True


        if state.inspect.instruction:
            insn_addr = state.inspect.instruction
        else:
            insn_addr = state.addr

        # as in __dbg_read_hook(), fix uninitialized addresses first
        self.__alloc_un(state, state.inspect.mem_write_address)

        # now you can safely, "evaluate" address and concretize it
        addr = state.se.eval(state.inspect.mem_write_address)

        # concretize size (newer versions of angr never set state.inspect.mem_read_length to None)
        if state.inspect.mem_write_length == None:
            size = MAX_MEM_UNIT_BYTES  # if size is None, set it to default
        else:
            size = state.se.eval(state.inspect.mem_write_length)

        dbg_prnt(DBG_LVL_3, '\t0x%08x: mem[0x%x] = %s (%x bytes)' %
                 (insn_addr, addr, state.inspect.mem_write_expr, size), pre='[W] ')


        if 'W' not in self.__get_permissions(addr, state) and addr not in _whitelist_:
            raise Exception("Attempted to write to an non-writable address '0x%x'" % addr)

        # if we are trying to write to an immutable cell, currect execution path must be discarded
        if self.__sim_mode == SIM_MODE_DISPATCH:
            if addr in self.__imm:

                oldval = state.se.eval(state.memory.load(addr, size))
                newval = state.se.eval(state.inspect.mem_write_expr)

                # if the new value is the same with the old one, we're good :)
                if oldval != newval:  # if value really changes
                    self.__disable_hooks = False

                    raise Exception("Attempted to write to immutable address '0x%x'" % addr)

        if state.inspect.mem_write_expr in self.__ext:
            self.__ext[state.inspect.mem_write_expr] = addr

        # if it's not the 1st time that you see this address
        if not self.__init_mem(state, addr, size):

            # if address is not concretized already and it's in the symbolic variable set
            if not isinstance(self.__mem[addr], tuple) and addr in self.__sym:
                symv = self.__sym[addr]  # get symbolic variable

                # check whether symbolic variable persists after write
                if not self.__symv_in(state.inspect.mem_write_expr, symv):
                    # Variable gets vanished. We should concretize it now, because, after
                    # that point, memory cell is dead; that is it's not part of the constraints
                    # anymore, as its original value got lost.
                    #
                    # To better illustrate the reason, consider the following code:
                    #       a = input();
                    #       if (a > 10 && a < 20) {
                    #           a = 0;
                    #           /* target block */
                    #       }
                    #
                    # Here, if we concretize 'a' at the end of the symbolic execution if will
                    # get a value of 0, which of course is not the desired one. The coorect
                    # approach, is to concretize, right before it gets overwritten.

                    # if variable is part of the constraints, add it to the set
                    if self.__in_constraints(symv, state):
                        val = state.se.eval(symv)  # self.__mread(state, addr, size))
                        self.__mem[addr] = (val, size)

                        emph('Address/Value pair found: *0x%x = 0x%x (%d bytes)' %
                             (addr, val, size), DBG_LVL_2)

                    # if the contents of that cell get lost, we cannot use AWP to write to it
                    # anymore
                    #
                    # TODO: Not sure if this correct
                    # UPDATE: Immutables should be fine when we write them with the exact same valut

        # All external inputs (sockets, file descriptors, etc.) should be first written somewhere
        # in memory / registers eventually, so we can concretize them afterwards

        self.__disable_hooks = False  # release "lock" (i.e., enable hooks again)

    # ---------------------------------------------------------------------------------------------
    # __dbg_symv_hook(): This callback function is invoked when a new symbolic variable is being
    #       created.
    #
    # :Arg state: Current state of the symbolic execution
    # :Ret: None.
    #
    def __dbg_symv_hook(self, state):
        name = state.inspect.symbolic_name  # get name of the variable

        # we're only interested in symbolic variables that come from external inputs (sockets,
        # file descriptors, etc.), as register and memory symbolic variables are already been
        # handled.
        if not name.startswith('mem_') and not name.startswith('reg_') \
                and not name.startswith('x_') and not name.startswith('cond_'):
            # x  and cond are our variable so they're discarded too
            dbg_prnt(DBG_LVL_3, " New symbolic variable '%s'" % name, pre='[S]')

            self.__ext[state.inspect.symbolic_expr] = EXTERNAL_UNINITIALIZED


    # ---------------------------------------------------------------------------------------------
    # __dbg_reg_wr_hook(): This callback function is invoked when a register is being modified.
    #
    # :Arg state: Current state of the symbolic execution
    # :Ret: None.
    #
    def __dbg_reg_wr_hook(self, state):
        if self.__disable_hooks:  # if hooks are disabled, abort
            return

        # as in __dbg_read_hook(), we need mutual exclusion here as well
        self.__disable_hooks = True


        if state.inspect.instruction:
            insn_addr = state.inspect.instruction
        else:
            insn_addr = state.addr

        # get register name (no exceptions here)
        regnam = state.arch.register_names[state.inspect.reg_write_offset]
        if regnam in HARDWARE_REGISTERS:  # we don't care about all registers (rip, etc.)

            dbg_prnt(DBG_LVL_3, '\t0x%08x: %s = %s' %
                     (insn_addr, regnam, state.inspect.reg_write_expr), pre='[r] ')

            # if simulation is in dispatch mode, check whether the modified register is immutable
            if self.__sim_mode == SIM_MODE_DISPATCH:

                if regnam in self.__imm_regs:

                    # if the new value is the same with the old one, we're good :)

                    # we can concretize them as SPL registers always have integer values
                    oldval = state.se.eval(self.__getreg(regnam))
                    newval = state.se.eval(state.inspect.reg_write_expr)

                    # if value really changes (and it has changed in the past)
                    if oldval != newval and \
                            self.__getreg(regnam).shallow_repr() != self.__inireg[regnam].shallow_repr():
                        self.__disable_hooks = False

                        raise Exception("Attempted to write to immutable register '%s'" % regnam)

                    else:
                        print "immutable register '%s' overwritten with same value 0x%x" % (regnam, newval)

            # check whether symbolic variable persists after write
            if not self.__symv_in(state.inspect.reg_write_expr, self.__inireg[regnam]):
                if regnam not in self.__reg:  # if register is already concretized, skip it
                    # concretize register (after this point, its value will get lost)
                    val = state.se.eval(self.__getreg(regnam, state))

                    # if register is in the constraints, it should be part of the solution.
                    # But in any case we need the register to be in __reg, as its value is now
                    # lost, so we don't want any further register writes to be part of the
                    # solution.

                    if self.__in_constraints(self.__inireg[regnam], state):
                        self.__reg[regnam] = val

                        emph('Register found: %s = %x' % (regnam, val), DBG_LVL_2)
                    else:
                        # make it a tuple to distinguish the 2 cases
                        self.__reg[regnam] = (val,)

        self.__disable_hooks = False  # release "lock" (i.e., enable hooks again)

    # ---------------------------------------------------------------------------------------------
    # __dbg_call_hook(): This callback function is invoked when a function is invoked.
    #
    # :Arg state: Current state of the symbolic execution
    # :Ret: None.
    #
    def __dbg_call_hook(self, state):
        if self.__disable_hooks:  # if hooks are disabled, abort
            return

        # as in __dbg_read_hook(), we need mutual exclusion here as well
        self.__disable_hooks = True

        address = state.se.eval(state.inspect.function_address)
        name = self.__proj.kb.functions[address].name

        # This function is called to solve a difficult problem: Crashes.

        dbg_prnt(DBG_LVL_3, "\tCall to '%s' found." % name, pre='[C] ')

        # ---------------------------------------------------------------------
        # FILE *fopen(const char *path, const char *mode)
        # ---------------------------------------------------------------------
        if name == 'fopen':

            # if rdi is an expression then we may need to

            # we work similarly with __mem_RSVPs, but our task here is simpler
            con_addr = state.se.eval(state.regs.rdi)
            # print 'ADDR', hex(con_addr)

            if 'W' not in self.__get_permissions(con_addr, state):
                self.__alloc_un(state, state.regs.rdi)
                # raise Exception("Attempted to write to an non-writable address '0x%x'" % addr)

            con_addr = state.se.eval(state.regs.rdi)

            name = SYMBOLIC_FILENAME

            # if this address has already been written in the past, any writes will
            # be overwritten, so discard current path
            if con_addr in self.__mem or con_addr in self.__imm or (con_addr + 7) in self.__imm:
                raise Exception("Address 0x%x has already been written or it's immutable. "
                                "Discard current path." % con_addr)

            # write value byte-by-byte.
            for i in range(len(name)):
                self.__mwrite(state, con_addr + i, 1, name[i])
                self.__imm.add(con_addr + i)

            self.__inivar_rel[con_addr] = name
            self.__mem[con_addr] = 0
            dbg_prnt(DBG_LVL_2, "Writing call *0x%x = '%s'" % (con_addr, name))


        self.__disable_hooks = False  # release "lock" (i.e., enable hooks again)



    # ---------------------------------------------------------------------------------------------

    ''' ======================================================================================= '''
    '''                          INTERNAL FUNCTIONS - TRACE MANAGEMENT                          '''
    ''' ======================================================================================= '''

    # ---------------------------------------------------------------------------------------------
    # __simulate_subpath(): This internal function performs the actual symbolic execution, for
    #       the candidate subpath. It guides symbolic execution through the specific subpath.
    #
    # :Arg sublen: The length of the subpath
    # :Arg subpath: The actual subpath
    # :Arg mode: The simluation mode for each step
    # :Ret: If the subpath can be simulated successfully, function returns the new state for the
    #       symbolic execution. Otherwise, function returns None.
    #
    def __simulate_subpath(self, sublen, subpath, mode):
        emph("Trying subpath (%d): %s" % (sublen,
                                          ' -> '.join(['0x%x' % p for p in subpath])), DBG_LVL_2)

        self.__disable_hooks = False  # enable hooks


        # clone current state (so we can revert if subpath extension fails)
        self.stash_context()

        state = self.__state.copy()

        # create hte simulation manager object
        simgr = self.__proj.factory.simulation_manager(thing=state)

        found = simgr.active[0]  # a.k.a. state

        dbg_arb(DBG_LVL_3, "BEFORE Constraints: ", found.se.constraints)

        # guide the symbolic execution: move from basic block to basic block
        for blk in subpath[1:]:
            simgr.drop(stash='errored')  # drop errored stashes

            self.__sim_mode = mode.pop(0)

            try:
                dbg_prnt(DBG_LVL_3, "Next basic block: 0x%x" % blk)

                node = ADDR2NODE[found.addr]

                num_inst = len(node.instruction_addrs) if node is not None else None
                if num_inst:
                    simgr.step(num_inst=num_inst)

                else:
                    simgr.step()


            except Exception, msg:
                dbg_prnt(DBG_LVL_3, "Subpath failed. Exception raised: '%s'" % bolds(str(msg)))
                found = None  # nothing found
                break  # abort


            if not simgr.active:
                dbg_arb(DBG_LVL_3, "Constraints: ", found.se.constraints)

                dbg_prnt(DBG_LVL_3, "Subpath failed (No 'active' stashes)")
                found = None  # nothing found
                break  # abort


            found = None  # nothing found


            # drop any active stashes and make found stashes, active so you
            # can continue the search
            simgr.move(from_stash='active', to_stash='found', \
                       filter_func=lambda s: s.addr == blk)

            simgr.drop(stash='active')
            simgr.move(from_stash='found', to_stash='active')

            if simgr.active:
                found = simgr.active[0]  # TODO: Shall we use .copy() here?

                dbg_prnt(DBG_LVL_3, "Block 0x%x found!" % blk)
                dbg_arb(DBG_LVL_3, "Constraints: ", found.se.constraints)


        if not found:  # if nothing found, drop cloned state
            print'Stashes', simgr.stashes

            self.unstash_context()
            del state
        else:
            self.drop_context_stash()
            dbg_prnt(DBG_LVL_3, "Subpath simulated successfully!")


        self.__disable_hooks = True  # hooks should be disabled

        return found  # return state (if any)

    # ---------------------------------------------------------------------------------------------

    ''' ======================================================================================= '''
    '''                                     CLASS INTERFACE                                     '''
    ''' ======================================================================================= '''

    # ---------------------------------------------------------------------------------------------
    # __init__(): Class constructor. Create and initialize a blank state and prepare the
    #       environment for the symbolic execution.
    #
    # :Arg project: Instance of angr project
    # :Arg cfg: Binary's CFG
    # :Arg IR: SPL's Intermediate Representation (IR)
    # :Arg entry: Payload's entry point
    #
    def __init__(self, project, __cfg_sp, entry):
        self.__proj = project  # store arguments internally

        self.__imm = set()  # immutable addresses
        self.__sym = {}  # symbolic variables
        self.__inireg = {}  # initial register symbolic variables

        self.__reg = {}  # final output for registers,
        self.__mem = {}  # memory and
        self.__ext = {}  # external data (from files, sockets, etc.)

        # 0xca00013b is actually pool_base + 0x13b
        self.__relative = {}

        self.condreg = ''
        # regsets that are not checked after block execution
        self.unchecked_regsets = []

        # even though we avoid all clobbering blocks from our path, this doesn't mean that
        # registers may not get clobbered. This usally happens inside system or library calls
        # where registers are being changed, even though there are no clobbering blocks.
        #
        # to deal with it, we simply mark a register as immutable after
        #
        # all register that used by SPL are immutable (only functional blocks can modify them)
        #
        self.__imm_regs = set()  # initially empty; add registers on the fly

        self.__sim_mode = SIM_MODE_INVALID


        # the base adress that uninitialized symbolic variables should be allocated
        # don't start form 0 to catch allocations that start BEFORE the initial (.e.g. if
        # [rax + 0x20] = ALLOC, then rax will be below allocator)
        self.__alloc_size = 0x100

        # create a CFG shortest path object
        self.__cfg_sp = __cfg_sp

        # create a symbolic execution state
        self.__state = self.__proj.factory.call_state(
            mode='symbolic',
            addr=entry,
            stack_base=STACK_BASE_ADDR,
            stack_size=0x10000
        )

        # initialize all registers with a symbolic variable
        self.__state.regs.rax = self.__state.se.BVS("rax", 64)
        self.__state.regs.rbx = self.__state.se.BVS("rbx", 64)
        self.__state.regs.rcx = self.__state.se.BVS("rcx", 64)
        self.__state.regs.rdx = self.__state.se.BVS("rdx", 64)
        self.__state.regs.rsi = self.__state.se.BVS("rsi", 64)
        self.__state.regs.rdi = self.__state.se.BVS("rdi", 64)

        # rsp must be concrete and properly initialized
        self.__state.registers.store('rsp', RSP_BASE_ADDR, size=8)

        # rbp may also needed as it's mostly used to access local variables (e.g.,
        # rax = [rbp-0x40]) but some binaries don't use rbp and all references are
        # rsp related. In these cases it may worth to use rbp as well.
        if MAKE_RBP_SYMBOLIC:
            self.__state.regs.rbp = self.__state.se.BVS("rbp", 64)
        else:
            self.__state.registers.store('rbp', FRAMEPTR_BASE_ADDR, size=8)

        self.__state.regs.r8 = self.__state.se.BVS("r08", 64)
        self.__state.regs.r9 = self.__state.se.BVS("r09", 64)
        self.__state.regs.r10 = self.__state.se.BVS("r10", 64)
        self.__state.regs.r11 = self.__state.se.BVS("r11", 64)
        self.__state.regs.r12 = self.__state.se.BVS("r12", 64)
        self.__state.regs.r13 = self.__state.se.BVS("r13", 64)
        self.__state.regs.r14 = self.__state.se.BVS("r14", 64)
        self.__state.regs.r15 = self.__state.se.BVS("r15", 64)

        # remember the initial symbolic variables for the registers
        self.__inireg = {r: self.__getreg(r) for r in HARDWARE_REGISTERS}

        # initialize SPL variables
        self.__plsz = 0  # our pool size
        self.__inivar_rel = {}  # values in the relative-form

        # An alternative way to enable/disable hooks is this:
        self.__disable_hooks = False  # enable breakpoints

        self.__state.inspect.b('mem_write', when=angr.BP_BEFORE, action=self.__dbg_write_hook)
        self.__state.inspect.b('mem_read', when=angr.BP_BEFORE, action=self.__dbg_read_hook)
        self.__state.inspect.b('reg_write', when=angr.BP_BEFORE, action=self.__dbg_reg_wr_hook)
        self.__state.inspect.b('symbolic_variable',
                               when=angr.BP_AFTER, action=self.__dbg_symv_hook)
        self.__state.inspect.b('call', when=angr.BP_AFTER, action=self.__dbg_call_hook)

        self.__origst = self.__state.copy()  # create a copy of the original state

        # deep copy
        self.imm = self.__imm
        self.sym = self.__sym
        self.inireg = self.__inireg
        self.reg = self.__reg
        self.mem = self.__mem
        self.ext = self.__ext
        self.relative = self.__relative
        self.imm_regs = self.__imm_regs
        self.alloc_size = self.__alloc_size
        self.state = self.__state
        self.disable_hooks = self.__disable_hooks = False  # enable breakpoints

        self.project = project


    # ---------------------------------------------------------------------------------------------
    # __check_regsets(): TODO:
    #
    # Some RSVPs have weird addresses that we can't even concretize right before the block execution:
    #   <Bool (Reverse(symbolic_read_unconstrained_277383_64) + (r13_277379_64 << 0x3)) == x_472_64>
    #
    # This means that our reservation will be wrong and the register will never be assigned to the
    # right value. A quick patch here, is to check whether register gets concretized to the right
    # value after the block execution and if not we add the desired constraint
    #
    # <Bool (0#32 .. (mem_d8003100_481_64[31:0] & 0xf8000000)) != 0x30000000>]
    #
    def __check_regsets(self, state=None):
        if not state:
            state = self.__state


        for reg, val in self.unchecked_regsets:
            if not isinstance(val, tuple):

                if state.se.eval(self.__getreg(reg, state)) != val:

                    warn('Wrong concretized value! Fixing it.... %x != %x' %
                         (state.se.eval(self.__getreg(reg, state)), val))

                    state.add_constraints(self.__getreg(reg, state) == val)

                    if not state.satisfiable():
                        dbg_prnt(DBG_LVL_2, "Reservation constraint was un-satisfiable. Rolling back...")

                        self.unchecked_regsets = []  # all registers are checked!
                        return False  # check failed


        self.unchecked_regsets = []  # all registers are checked!

        return True

    # ---------------------------------------------------------------------------------------------
    # simulate_edge(): This function is invoked for every edge in the induced subgraph Hk and it
    #       performs a symbolic execution from one accepted block to another. Essentially, its
    #       purpose is to find a "dispatcher gadget" (i.e., a sequence of non-clobbering blocks)
    #       between two SPL statements.
    #
    #       Unfortunately, the symbolic execution engine, may take forever to move from the one
    #       accepted block to the other To address this issue, we "guide" the symbolic execution,
    #       by selecting the exact subpath that will follow. This path however, is just an
    #       estimation so it may not be correct. Therefore, simulate_edge() quickly generates
    #       candidate subpaths, starting from the shortest one.
    #
    #       simulate_edge() generates PARAMETER_P different subpaths. However, if we let it
    #       generate all possible paths, the result will be the same with the unguided symbolic
    #       execution.
    #
    # :Arg currb: Address of the current basic block
    # :Arg nextb: Address of the basic block that we want to reach
    # :Arg uid: Current UID of the payload
    # :Arg loopback: A boolean indicating whether we should simulate a path or a loop
    # :Ret: If function can extend the path, it returns the basic block path. Otherwise, it returns
    #   None.
    #
    def simulate_edge(self, currb, nextb, uid, loopback=False):
        dbg_prnt(DBG_LVL_2, "Simulating edge (0x%x, 0x%x) for UID = %d" % (currb, nextb, uid))


        # Check if current basic block matches with the address of the current state
        if currb != self.__state.addr:  # base check
            raise Exception('Illegal transition from current state '
                            '(starts from 0x%x, but state is at 0x%x)' % (currb, self.__state.addr))

        if loopback and currb != nextb:  # base check
            raise Exception('Loopback mode on distinct blocks')


        self.__disable_hooks = True


        # ---------------------------------------------------------------------
        # Loopback mode
        # ---------------------------------------------------------------------
        if loopback:
            dbg_prnt(DBG_LVL_2, "Simluation a loop, starting from 0x%x ..." % self.__state.addr)

            # guide the symbolic execution: generate P shortest loops
            for length, loop in self.__cfg_sp.k_shortest_loops(currb, uid, PARAMETER_P):

                if length > MAX_ALLOWED_SUBPATH_LEN:  # if loop is too long, discard it
                    # This won't happen as the same check happens inside path.py, but we
                    # should keep modules independent

                    dbg_prnt(DBG_LVL_3, "Loop is too big (%d). Discard current path ..." % length)
                    break

                mode = [SIM_MODE_FUNCTIONAL] + [SIM_MODE_DISPATCH] * (len(loop) - 2) + [SIM_MODE_FUNCTIONAL]

                # if we need to simulate loop multiple times, we unroll current loop by a constant
                # factor
                if SIMULATED_LOOP_ITERATIONS > 2:
                    loop = loop[:-1] * (SIMULATED_LOOP_ITERATIONS - 1)
                    mode = mode[:-1] * (SIMULATED_LOOP_ITERATIONS - 1)


                # do the actual symbolic execution and verify that loop is correct
                nextst = self.__simulate_subpath(length, loop, mode)

                if nextst != None:  # success!
                    emph("Edge successfully simulated.", DBG_LVL_2)

                    del self.__state  # we don't need current state
                    self.__state = nextst  # update state

                    return loop  # return subpath


        # ---------------------------------------------------------------------
        # Path mode
        # ---------------------------------------------------------------------
        else:
            # guide the symbolic execution: generate P shortest paths
            for slen, subpath in self.__cfg_sp.k_shortest_paths(currb, nextb, uid, PARAMETER_P):

                if slen > MAX_ALLOWED_SUBPATH_LEN:  # if subpath is too long, discard it
                    break

                mode = [SIM_MODE_FUNCTIONAL] + [SIM_MODE_DISPATCH] * (len(subpath) - 1)

                # do the actual symbolic execution and verify if subpath is correct
                nextst = self.__simulate_subpath(slen, subpath, mode)

                if nextst != None:  # success!
                    dbg_prnt(DBG_LVL_2, "Edge successfully simulated.")

                    if slen > 0:
                        self.__check_regsets(nextst)

                    del self.__state  # we don't need current state
                    self.__state = nextst  # update state

                    return subpath  # return subpath


        # we cannot simulate this edge. Try another induced subgraph
        dbg_prnt(DBG_LVL_2, "Cannot simulate egde. Discarding current induced subgraph...")

        return None  # no subpath to return



    # ---------------------------------------------------------------------------------------------
    # step(): This function moves the execution forward by 1 basic block.
    #
    # :Arg stmty: The type of the last statement
    # :Ret: None.
    #
    def step(self, stmt):
        dbg_prnt(DBG_LVL_2, "Moving one step forward from 0x%x ..." % self.__state.addr)

        # create hte simulation manager object
        simgr = self.__proj.factory.simulation_manager(thing=self.__state)


        self.__disable_hooks = False  # enable hooks to capture reads/writes

        # this should throw no exception (it was already successful in absblk.py)
        if stmt['type'] == 'call':
            self.__sim_mode = SIM_MODE_DISPATCH
        else:
            # step is in functional mode ;)
            self.__sim_mode = SIM_MODE_FUNCTIONAL
        try:

            try:
                node = ADDR2NODE[self.__state.addr]

            except Exception, e:
                node = None

            num_inst = len(node.instruction_addrs) if node is not None else None
            if num_inst:
                simgr.step(num_inst=num_inst)
            else:
                simgr.step()


        except Exception, msg:
            dbg_prnt(DBG_LVL_3, "Step failed. Exception raised: '%s'" % bolds(str(msg)))
            return -1

        except angr.errors.SimUnsatError:  # un-satisfiable constraints
            dbg_prnt(DBG_LVL_2, "Step constraints were un-satisfiable. Discard current path.")
            return -1

        dbg_prnt(DBG_LVL_2, "Step simulated successfully.")

        if not simgr.active:
            print 'Stashes', simgr.stashes

            dbg_prnt(DBG_LVL_3, "Stop failed (No 'active' stashes)")

            # We may endup in deadended state if the last block is a retn
            return [0xdeadbeef]


        self.__disable_hooks = True  # disable hooks again

        # pick the state (if > 1) with satisfiable constraints
        for state in simgr.active:
            dbg_prnt(DBG_LVL_3, "Checking constraints from state: 0x%x" % state.addr)

            state_copy = state.copy()
            unchecked = self.unchecked_regsets[:]

            if self.__check_regsets(state_copy):
                self.__state = state_copy

                dbg_prnt(DBG_LVL_2, "Done.")
                dbg_arb(DBG_LVL_3, "Constraints: ", self.__state.se.constraints)

                return [state.addr for state in simgr.active]

            del state_copy
            self.unchecked_regsets = unchecked[:]

        return -1



    # ---------------------------------------------------------------------------------------------
    # clone(): This function clones the current simulation object, once it reaches a conditional
    #       basic block. TODO: elaborate
    #
    # :Arg condreg: The register that is used in the condition (must be symbolic)
    # :Ret: An identical hardcopy of the current object.
    #
    def clone(self, condreg):

        dbg_prnt(DBG_LVL_1, "Cloning current state at 0x%x ..." % self.__state.addr)

        print 'RBX', self.__state.regs.rbx, self.__inireg['rbx'], self.__getreg('rbx')

        # TODO: That's a bad way to do it. Nevermind it works.
        if condreg == 'rax':
            self.__state.regs.rax = self.__state.se.BVS("cond_rax", 64)
        elif condreg == 'rbx':
            self.__state.regs.rbx = self.__state.se.BVS("cond_rbx", 64)
        elif condreg == 'rcx':
            self.__state.regs.rcx = self.__state.se.BVS("cond_rcx", 64)
        elif condreg == 'rdx':
            self.__state.regs.rdx = self.__state.se.BVS("cond_rdx", 64)
        elif condreg == 'rsi':
            self.__state.regs.rsi = self.__state.se.BVS("cond_rsi", 64)
        elif condreg == 'rdi':
            self.__state.regs.rdi = self.__state.se.BVS("cond_rdi", 64)
        elif condreg == 'rbp':
            self.__state.regs.rbp = self.__state.se.BVS("cond_rbp", 64)
        elif condreg == 'r8':
            self.__state.regs.r8 = self.__state.se.BVS("cond_r08", 64)
        elif condreg == 'r9':
            self.__state.regs.r9 = self.__state.se.BVS("cond_r09", 64)
        elif condreg == 'r10':
            self.__state.regs.r10 = self.__state.se.BVS("cond_r10", 64)
        elif condreg == 'r11':
            self.__state.regs.r11 = self.__state.se.BVS("cond_r11", 64)
        elif condreg == 'r12':
            self.__state.regs.r12 = self.__state.se.BVS("cond_r12", 64)
        elif condreg == 'r13':
            self.__state.regs.r13 = self.__state.se.BVS("cond_r13", 64)
        elif condreg == 'r14':
            self.__state.regs.r14 = self.__state.se.BVS("cond_r14", 64)
        elif condreg == 'r15':
            self.__state.regs.r15 = self.__state.se.BVS("cond_r15", 64)

        self.condreg = condreg

        state_copy = self.__state.copy()

        # create hte simulation manager object
        simgr = self.__proj.factory.simulation_manager(thing=state_copy)

        print 'Stashes', simgr.stashes
        print 'Constraints', self.__state.se.constraints

        # this should throw no exception (it was already successful in absblk.py)
        simgr.step()

        print 'Stashes', simgr.stashes

        # we should have exactly 2 active stashes
        print simgr.active[0].se.constraints
        print simgr.active[1].se.constraints

        if len(simgr.active) != 2:
            print simgr.active
            raise Exception('Conditional jump state should have 2 active stashes')

        dbg_prnt(DBG_LVL_2, "Done.")


        newsim = simulate(self.project, self.__cfg_sp, self.__state.addr)

        newsim.imm = copy.deepcopy(self.__imm)
        newsim.sym = copy.deepcopy(self.__sym)
        newsim.inireg = copy.deepcopy(self.__inireg)
        newsim.reg = copy.deepcopy(self.__reg)
        newsim.mem = copy.deepcopy(self.__mem)
        newsim.ext = copy.deepcopy(self.__ext)
        newsim.relative = copy.deepcopy(self.__relative)
        newsim.imm_regs = copy.deepcopy(self.__imm_regs)
        newsim.alloc_size = copy.deepcopy(self.__alloc_size)
        newsim.state = self.__state.copy()  # copy.deepcopy(self.__state)
        newsim.inireg = copy.deepcopy(self.__inireg)
        newsim.disable_hooks = copy.deepcopy(self.__disable_hooks)
        newsim.unchecked_regsets = copy.deepcopy(self.unchecked_regsets)

        newsim.copy_locally()

        print 'Constraints', self.__state.se.constraints

        self.__state.add_constraints(simgr.active[1].se.constraints[-1])
        newsim.state.add_constraints(simgr.active[0].se.constraints[-1])

        del state_copy

        return newsim


    # ---------------------------------------------------------------------------------------------
    # stash_context(): Save current context to a stash.
    #
    # :Ret: None.
    #
    def copy_locally(self):
        self.__imm = self.imm
        self.__sym = self.sym
        self.__inireg = self.inireg
        self.__reg = self.reg
        self.__mem = self.mem
        self.__ext = self.ext
        self.__relative = self.relative
        self.__imm_regs = self.imm_regs
        self.__alloc_size = self.alloc_size
        self.__state = self.state
        self.__disable_hooks = self.disable_hooks

        # state will have action to the parent object. We have to readjust them?
        self.__state.inspect.b('mem_write', when=angr.BP_BEFORE, action=self.__dbg_write_hook)
        self.__state.inspect.b('mem_read', when=angr.BP_BEFORE, action=self.__dbg_read_hook)
        self.__state.inspect.b('reg_write', when=angr.BP_BEFORE, action=self.__dbg_reg_wr_hook)
        self.__state.inspect.b('symbolic_variable',
                               when=angr.BP_AFTER, action=self.__dbg_symv_hook)
        self.__state.inspect.b('call', when=angr.BP_AFTER, action=self.__dbg_call_hook)

    # ---------------------------------------------------------------------------------------------
    # stash_context(): Save current context to a stash.
    #
    # :Ret: None.
    #
    def update_globals(self):
        self.imm = self.__imm
        self.sym = self.__sym
        self.inireg = self.__inireg
        self.reg = self.__reg
        self.mem = self.__mem
        self.ext = self.__ext
        self.relative = self.__relative
        self.imm_regs = self.__imm_regs
        self.alloc_size = self.__alloc_size
        self.state = self.__state
        self.disable_hooks = self.__disable_hooks

    # ---------------------------------------------------------------------------------------------
    # stash_context(): Save current context to a stash.
    #
    # :Ret: None.
    #      self.__state.inspect.b('mem_write', when=angr.BP_BEFORE, action=self.__dbg_write_hook )
    def stash_context(self):
        self.__stash_imm = copy.deepcopy(self.__imm)
        self.__stash_sym = copy.deepcopy(self.__sym)
        self.__stash_inireg = copy.deepcopy(self.__inireg)
        self.__stash_reg = copy.deepcopy(self.__reg)
        self.__stash_mem = copy.deepcopy(self.__mem)
        self.__stash_ext = copy.deepcopy(self.__ext)
        self.__stash_relative = copy.deepcopy(self.__relative)
        self.__stash_imm_regs = copy.deepcopy(self.__imm_regs)
        self.__stash_alloc_size = copy.deepcopy(self.__alloc_size)
        self.__stash_state = self.__state.copy()  # copy.deepcopy(self.__state)
        self.__stash_disable_hooks = copy.deepcopy(self.__disable_hooks)
        self.__stash_unchecked_regsets = copy.deepcopy(self.unchecked_regsets)

    # ---------------------------------------------------------------------------------------------
    # drop_context_stash(): Drop context stash.
    #
    # :Ret: None.
    #
    def drop_context_stash(self):
        del self.__stash_imm
        del self.__stash_sym
        del self.__stash_inireg
        del self.__stash_reg
        del self.__stash_mem
        del self.__stash_ext
        del self.__stash_relative
        del self.__stash_imm_regs
        del self.__stash_alloc_size
        del self.__stash_state
        del self.__stash_disable_hooks
        del self.__stash_unchecked_regsets

        # ---------------------------------------------------------------------------------------------

    # unstash_context(): Remove a context from stash and use it.
    #
    # :Ret: None.
    #
    def unstash_context(self):
        del self.__imm
        del self.__sym
        del self.__inireg
        del self.__reg
        del self.__mem
        del self.__ext
        del self.__relative
        del self.__imm_regs
        del self.__alloc_size
        del self.__state
        del self.__disable_hooks
        del self.unchecked_regsets

        self.__imm = self.__stash_imm
        self.__sym = self.__stash_sym
        self.__inireg = self.__stash_inireg
        self.__reg = self.__stash_reg
        self.__mem = self.__stash_mem
        self.__ext = self.__stash_ext
        self.__relative = self.__stash_relative
        self.__imm_regs = self.__stash_imm_regs
        self.__alloc_size = self.__stash_alloc_size
        self.__state = self.__stash_state
        self.__disable_hooks = self.__stash_disable_hooks
        self.unchecked_regsets = self.__stash_unchecked_regsets
