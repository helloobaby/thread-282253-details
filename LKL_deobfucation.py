from binaryninja import *

def safe_asm(bv, asm_str) -> bytes:
    b = bv.arch.assemble(asm_str)
    log_debug(f'safe_asm {asm_str} get bytes {b}')
    return b

def llil_at(bv, addr) -> LowLevelILInstruction:
    funcs = bv.get_functions_containing(addr)
    if not funcs:
        return None

    return funcs[0].get_low_level_il_at(addr)

def is_call(bv, addr):
    llil = llil_at(bv, addr)
    if llil is None:
        return False
    return llil.operation == LowLevelILOperation.LLIL_CALL

def get_dominated_by(dominator):
    # 1: initialize worklist
    result = set()
    worklist = [dominator]
    # 2: perform a depth-first search on the dominator tree
    while worklist:
        # get next block
        block = worklist.pop(0)
        # add to result
        result.add(block)
        # add children from dominator tree to worklist
        for child in block.dominator_tree_children:
            worklist.append(child)
    return result

def calc_flattening_score(function):
    score = 0.0
    # 1: walk over all basic blocks
    for block in function.basic_blocks:
        # 2: get all blocks that are dominated by the current block
        dominated = get_dominated_by(block)
        # 3: check for a back edge
        if not any([edge.source in dominated for edge in block.incoming_edges]):
            # https://synthesis.to/2021/03/03/flattening_detection.html
            log_debug(f'back edge {block}')
            continue
        # 4: calculate relation of dominated blocks to the blocks in the graph
        score = max(score, len(dominated)/len(function.basic_blocks))
        log_debug(f'current basic_block {block} flatten score {len(dominated)/len(function.basic_blocks)}')
    return score

class CFGLink(object):
    def __init__(self, block, true_block, false_block=None, def_il=None):
        """ Create a link from a block to its real successors

        Args:
            block (BasicBlock): block to start from
            true_block (BasicBlock): The target block of an unconditional jump,
                or the true branch of a conditional jump
            false_block (BasicBlock): The false branch of a conditional jump
            def_il (MediumLevelILInstruction): The instruction that was used
                to discover this link. This will be a definition of the state
                variable
        """
        self.il:MediumLevelILInstruction = def_il  # The definition il we used to find this link
        self.block:BasicBlock = block

        # Resolve the true/false blocks
        self.true_block:BasicBlock = true_block
        self.false_block:BasicBlock = false_block

        self.nop_addrs = set()

    @property
    def is_uncond(self):
        return self.false_block is None

    @property
    def is_cond(self):
        return not self.is_uncond

    def gen_asm(self, bv, base_addr):
        """ Generates a patch to repair this link

        For an unconditional jump, this will generate
            jmp next_block

        For a conditional jump, this will generate
            jcc true_block
            jmp false_block
        where cc is the condition used in the original CMOVcc in the flattening logic

        Args:
            bv (BinaryView)
            base_addr (int): The address where these instructions will be placed.
                This is necessary to calculate relative addresses

        Returns:
            str: The assembled patch opcodes
        """
        # It's assumed that base_addr is the start of free space
        # at the end of a newly recovered block
        def rel(addr):
            return hex(addr - base_addr).rstrip('L')


        log_debug(f'state_def {self.il} {self.il.address:#x}')
        
        # Unconditional jmp
        if self.is_uncond:
            log_debug('is_uncond')
            next_addr = self.true_block.start
            log_debug('[+] Patching from {:x} to {:x}'.format(base_addr, next_addr))
            log_debug(f'assembly string -> jmp {next_addr:#x}')
            return safe_asm(bv, 'jmp {}'.format(rel(next_addr)))

        # Branch based on original cmovcc
        elif self.is_cond:
            # Conditional jmp
            assert self.il is not None
            log_debug('is_cond')

            true_addr = self.true_block.start
            false_addr = self.false_block.start
            log_debug('[+] Patching from {:x} to T: {:x} F: {:x}'.format(base_addr,
                                                                    true_addr,
                                                                    false_addr))

            # Find the cmovcc by looking at the def il's incoming edges
            # Both parent blocks are part of the same cmov
            curRealBasicBlock:BasicBlock = self.il.il_basic_block.incoming_edges[0].source
            log_debug(f'curRealBasicBlock {curRealBasicBlock}')
            cmov_addr = curRealBasicBlock[-1].address
            log_debug(f'cmov_addr {cmov_addr:#x}')
            if 'cmov' not in bv.get_disassembly(cmov_addr):
                log_error(f'cmov not in expectd cmov_addr {cmov_addr:x}')
                assert(0)

            cmov = bv.get_disassembly(cmov_addr).split(' ')[0]
            # cmovcc -> jcc
            jmp_instr = cmov.replace('cmov', 'j')
            log_debug(f'jmp_instr : {jmp_instr}')
            # Generate the branch instructions
            asm = safe_asm(bv, '{} {}'.format(jmp_instr, rel(true_addr)))
            base_addr += len(asm)
            asm += safe_asm(bv, 'jmp {}'.format(rel(false_addr)))
            log_debug(f'assembly string jcc {true_addr:#x}')
            log_debug(f'assembly string jmp {false_addr:#x}')
            return asm
                

    def __repr__(self):
        if self.is_uncond:
            return '<U Link: {} => {}>'.format(self.block,
                                               self.true_block)
        else:
            return '<C Link: {} => T: {}, F: {}>'.format(self.block,
                                                         self.true_block,
                                                         self.false_block)
def get_ssa_def(mlil, var):
    """ Gets the IL that defines var in the SSA form of mlil """
    return mlil.ssa_form.get_ssa_var_definition(var)


# 清理块,为Patch腾出空间
def clean_block(bv:BinaryView, mlil:MediumLevelILFunction, link:CFGLink):
    """ Return the data for a block with all unnecessary instructions removed

    Args:
        bv (BinaryView)
        mlil (MediumLevelILFunction): The MLIL for the function to be deflattened
        link (CFGLink): a link with the resolved successors for a block

    Returns:
        str: A copy of the block link is based on with all dead instructions removed
    """

    # Helper for resolving new addresses for relative calls
    # call指令重定位
    # addr -> 原call位置, newaddr-> 新call位置
    def _fix_call(bv, addr, newaddr):
        log_debug(f'_fix_call {addr:#x}')
        tgt = llil_at(bv, addr).dest.constant
        reladdr = hex(tgt - newaddr).rstrip('L')
        return safe_asm(bv, 'call {}'.format(reladdr))

    # The terminator gets replaced anyway
    block = link.block 
    old_len = block.length  # 获得原先这个basic_block的指令字节数
    
    # 最后一条指令是跳转,必须删掉,不然会把老的跳转放前面,Patch是从最后开始Patch的
    if 'j' in bv.get_disassembly(block.disassembly_text[-1].address):
        link.nop_addrs.add(block.disassembly_text[-1].address)

    if link.is_cond:
        # 这个样本的模式还是很固定的,后三条指令全部Patch
        """
        00401b9d  0f45c1             cmovne  eax, ecx  {0x279d1104}
        00401ba0  8945e0             mov     dword [ebp-0x20 {var_24}], eax
        00401ba3  e9fb150000         jmp     0x4031a3
        """

        if (len(block.disassembly_text) <= 3):
            log_error(block)
            assert(0)

        if 'cmov' in bv.get_disassembly(block.disassembly_text[-3].address):
            link.nop_addrs.add(block.disassembly_text[-3].address)
    
    # StateVar的这条赋值指令,可以删除
    # 如果是uncond这种情况，不可能出现Patch字节不够的情况,这里提供5个字节
    link.nop_addrs.add(link.il.address)

    for nop_addr in link.nop_addrs:
        log_debug(f'nop_addr {nop_addr:#x} , instruction size {bv.get_instruction_length(nop_addr)}')
        # 不能在这里nop,会影响gen_asm的分析,要最后统一nop
        #bv.convert_to_nop(nop_addr)

    # Rebuild the block, skipping the bad instrs
    log_debug(f'rebuild the block start {block.start:#x}')
    addr = block.start
    data = b''
    # 依次把原来的block里的必须的指令读出来
    while addr < block.end: 
        # How much data to read
        ilen = bv.get_instruction_length(addr)
        # 在nop_addrs里的指令就不要了
        if addr not in link.nop_addrs:
            # Calls need to be handled separately to fix relative addressing
            if is_call(bv, addr) and not isinstance(llil_at(bv,addr).dest,LowLevelILReg):
                data += _fix_call(bv, addr, block.start + len(data))
            else:
                data += bv.read(addr, ilen)

        # Next instruction
        addr += ilen

    log_debug(f'build end ')
    log_debug(f'blockdata {data}')
    log_debug(f'cave_addr {block.start + len(data):#x}') # patch的起始地址
    log_debug(f'old_len {old_len}')
    return data, block.start + len(data), old_len

def compute_backbone_map(func:Function) -> dict[int,MediumLevelILBasicBlock]:
    a={}
    for bb in func.mlil_basic_blocks:

        if len(bb.outgoing_edges) == 0:
            continue

        for instruction in bb:
        # 模式匹配
        # if (temp0_1 == 0x816592e7) then 45 @ 0x47263f else 47 @ 0x438589
            if instruction.operation == MediumLevelILOperation.MLIL_IF and \
                hasattr(instruction.operands[0],'right') and \
                isinstance(instruction.operands[0].right,MediumLevelILConst) and \
                hasattr(instruction.operands[0].left,'src') and \
                hasattr(instruction.operands[0].left.src,'name') and \
                'temp' in instruction.operands[0].left.src.name:

                if instruction.operands[0].operation != MediumLevelILOperation.MLIL_CMP_E:
                    log_error(f'{instruction} undefine behavior 1')
                    assert(0)

                a[instruction.operands[0].right.value.value] = instruction.il_basic_block.outgoing_edges[0].target


    # 还有一种这种情况
    # 40 @ 004010b7  bool z_1 = temp0_1 == 0x8204c59e
    # 41 @ 004010bc  if (z_1) then 42 @ 0x401d44 else 183 @ 0x4010c2
        if len(bb) >= 2:
            if len(bb[-2].operands) >= 2 and \
            hasattr(bb[-2].operands[1],'left') and \
            hasattr(bb[-2].operands[1].left,'src') and \
            hasattr(bb[-2].operands[1].left.src,'name') and \
            'temp' in bb[-2].operands[1].left.src.name:
                a[bb[-2].operands[1].right.value.value] = bb.outgoing_edges[0].target

    return a

log_to_stdout(LogLevel.DebugLog)
for func in bv.functions:
    # 强制设置为当前函数，打断自动化,一般是为了调试单个函数
    func = current_function

    if func.total_bytes < 0x1000:
        log_info(f'function {func} size too small ,skip')
        continue

    if func.analysis_skipped:
        func.analysis_skipped = False
        log_info(f'Wait function analysis {func}')
        bv.update_analysis_and_wait()

    if calc_flattening_score(func) >= 0.8:
        log_info(f'automate get obfucation function {func} , score {calc_flattening_score(func)}')
    else:
        continue

    log_info(f'Analyse Function {func}')


    loopEntry:MediumLevelILBasicBlock = func.medium_level_il.basic_blocks[0].outgoing_edges[0].target
    log_info(f'loopEntry {loopEntry}')
    loopEnd:MediumLevelILBasicBlock = loopEntry.incoming_edges[1].source
    log_info(f'loopEnd {loopEnd}')

    # 通过loopEntry找到StateVar
    StateVar:MediumLevelILVar = loopEntry[0].src
    log_info(f'StateVar {StateVar}')

    StateMap = compute_backbone_map(func)
    log_info('Print StateMap Info')
    log_info(f'len StateMap is {len(StateMap)}')
    for v in StateMap:
        log_info(f'{v:#x} -> {StateMap[v]}')

    func:Function
    defs = func.medium_level_il.get_var_definitions(StateVar.src)
    log_info('Print defs Info')
    for d in defs:
        log_info(f'{d}')

    # 修复CFG
    ListCFG:list[CFGLink]=[]

    for state_def in defs:
        if state_def.operation != MediumLevelILOperation.MLIL_SET_VAR:
            assert(0)
        
        log_debug(f'state_def {state_def}')
        current_basicblock:BasicBlock = bv.get_basic_blocks_at(state_def.address)[0]


        if isinstance(state_def.src,MediumLevelILConst):
            state=state_def.src.value.value
            if state not in StateMap:
                log_warn(f'state {state:#x} has no corresponding dest , state_def insn {state_def}')
                continue
            dest:MediumLevelILBasicBlock=StateMap[state]

            if len(state_def.il_basic_block.outgoing_edges) == 1:
                CFG = CFGLink(current_basicblock,bv.get_basic_blocks_at(dest[0].address)[0],false_block=None,def_il=state_def)
                ListCFG.append(CFG)
                log_info(f'Add Uncond CFG {current_basicblock} -> {bv.get_basic_blocks_at(dest[0].address)[0]}')

        # cmocc
        elif isinstance(state_def.src,MediumLevelILVar):
            if len(state_def.il_basic_block.incoming_edges) != 2:
                log_error(f'{state_def} undefine behavior 2')
                assert(0)

            tmpVar = state_def.src.src
            curRealBasicBlock:MediumLevelILBasicBlock = state_def.il_basic_block.incoming_edges[0].source

            f_block=t_block=None
            for instruction in curRealBasicBlock:
                if instruction.operation == MediumLevelILOperation.MLIL_SET_VAR and instruction.dest == tmpVar:
                    log_debug(f'Find assign tmp var {instruction}')
                    f_block = StateMap[instruction.src.value.value]
                    log_debug(f'false block {f_block}')
                    break

            assert(curRealBasicBlock.outgoing_edges[0].target[0].operation == MediumLevelILOperation.MLIL_SET_VAR)
            t_block=StateMap[curRealBasicBlock.outgoing_edges[0].target[0].src.value.value]

            log_debug(f'true block {t_block}')


            if t_block == None or f_block == None:
                assert(0)

            CFG=CFGLink(bv.get_basic_blocks_at(curRealBasicBlock[0].address)[0],bv.get_basic_blocks_at(t_block[0].address)[0],bv.get_basic_blocks_at(f_block[0].address)[0],def_il=state_def)
            ListCFG.append(CFG)

            log_info(f'Add Cond CFG {current_basicblock} -> {bv.get_basic_blocks_at(t_block[0].address)[0]} {bv.get_basic_blocks_at(f_block[0].address)[0]}')

    log_debug('\nPatch CFG')
    for link in ListCFG:
        log_debug(f'link info ')
        log_debug(f'link.block {link.block} , link.true_block {link.true_block} , link.false_block {link.false_block} , link.is_cond {link.is_cond} , link.is_uncond {link.is_uncond} , link.il {link.il}')

        # Clean out instructions we don't need to make space
        blockdata, cave_addr, orig_len = clean_block(bv, func.medium_level_il, link)
        blockdata += link.gen_asm(bv, cave_addr)
        if len(blockdata) < orig_len:
            pad_nop = orig_len-len(blockdata)
            log_debug(f'need padding {pad_nop} nop ')
            blockdata+= b'\x90'*pad_nop
    
        if len(blockdata) > orig_len:
                log_error(f'Patch的地方 {cave_addr:#x} 大小不够,原block有{orig_len}个字节 新block{len(blockdata)}个字节 , 跳过Patch')
                continue

        bv.write(link.block.start, blockdata)

    # for debug
    break

log_warn('The script has completed')