from binaryninja import *

# 8B /r	MOV r32,r/m32	Move r/m32 to r32.
# A1	MOV EAX,moffs32*	Move doubleword at (seg:offset) to EAX.

# mov ecx ,addr -> mov ecx,0 
# mov eax ,addr -> mov eax,0 

bogus_var_addr=[0x4FF534,0x4FF538,0x4FF53C,0x4FF540,0x4FF544,0x4FF548,0x4FF54C,0x4FF550,0x4FF554,0x4FF558]
target_function={0x401000,0x4031a3,0x403390,0x406f20,0x472da0,0x4384a0}

log_to_stdout(LogLevel.DebugLog)

# for IDE highlight
bv:BinaryView=bv

for func in bv.functions:
    func:Function = func
    if func.start not in target_function:
        continue
    log_info(f'Visit Function {func}')
    for bb in func.basic_blocks:
        for i in range(len(bb.get_disassembly_text())):
            inst_address = bb.get_disassembly_text()[i].address
            inst_length = bv.get_instruction_length(inst_address)
            data=bv.read(inst_address,inst_address)
            if data[0]==0x8b and data[1] == 0x0d and inst_length == 6:
                m32=data[2:5]
                m32 = int.from_bytes(m32,'little')
                if m32 in bogus_var_addr:
                    log_info(hex(inst_address))
                    bv.write(inst_address,b'\xb9\x01\x00\x00\x00\x90')

            elif data[0]==0xa1 and inst_length == 5:
                m32=data[1:4]
                m32=int.from_bytes(m32,'little')
                if m32 in bogus_var_addr:
                    log_info(hex(inst_address))
                    bv.write(inst_address,b'\xb8\x01\x00\x00\x00')
