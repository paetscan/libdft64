#include "ins_ternary_op.h"
#include "ins_helper.h"

/* threads context */
extern thread_ctx_t *threads_ctx;

static void PIN_FAST_ANALYSIS_CALL r2r_ternary_opl(THREADID tid, uint32_t reg_src1, uint32_t reg_src2, uint32_t reg_dst) {
    tag_t src1_tags[] = R32TAG(reg_src1);
    tag_t src2_tags[] = R32TAG(reg_src2);

    for (size_t i = 0; i < 4; i++) {
        RTAG[reg_dst][i] = tag_combine(src1_tags[i], src2_tags[i]);
    }
}

static void PIN_FAST_ANALYSIS_CALL r2r_ternary_opq(THREADID tid, uint32_t reg_src1, uint32_t reg_src2, uint32_t reg_dst) {
    tag_t src1_tags[] = R64TAG(reg_src1);
    tag_t src2_tags[] = R64TAG(reg_src2);

    for (size_t i = 0; i < 8; i++) {
        RTAG[reg_dst][i] = tag_combine(src1_tags[i], src2_tags[i]);
    }
}

static void PIN_FAST_ANALYSIS_CALL r2r_ternary_opx(THREADID tid, uint32_t reg_src1, uint32_t reg_src2, uint32_t reg_dst) {
    tag_t src1_tags[] = R128TAG(reg_src1);
    tag_t src2_tags[] = R128TAG(reg_src2);

    for (size_t i = 0; i < 16; i++) {
        RTAG[reg_dst][i] = tag_combine(src1_tags[i], src2_tags[i]);
    }
}

static void PIN_FAST_ANALYSIS_CALL r2r_ternary_opy(THREADID tid, uint32_t reg_src1, uint32_t reg_src2, uint32_t reg_dst) {
    tag_t src1_tags[] = R256TAG(reg_src1);
    tag_t src2_tags[] = R256TAG(reg_src2);

    for (size_t i = 0; i < 32; i++) {
        RTAG[reg_dst][i] = tag_combine(src1_tags[i], src2_tags[i]);
    }
}

static void PIN_FAST_ANALYSIS_CALL m2r_ternary_opl(THREADID tid, uint32_t reg_dst, uint32_t reg_src1, ADDRINT src2) {
    tag_t src1_tags[] = R32TAG(reg_src1);
    tag_t src2_tags[] = M32TAG(src2);

    for (size_t i = 0; i < 4; i++) {
        RTAG[reg_dst][i] = tag_combine(src1_tags[i], src2_tags[i]);
    }
}

static void PIN_FAST_ANALYSIS_CALL m2r_ternary_opq(THREADID tid, uint32_t reg_dst, uint32_t reg_src1, ADDRINT src2) {
    tag_t src1_tags[] = R64TAG(reg_src1);
    tag_t src2_tags[] = M64TAG(src2);

    for (size_t i = 0; i < 8; i++) {
        RTAG[reg_dst][i] = tag_combine(src1_tags[i], src2_tags[i]);
    }
}

static void PIN_FAST_ANALYSIS_CALL m2r_ternary_opx(THREADID tid, uint32_t reg_dst, uint32_t reg_src1, ADDRINT src2) {
    tag_t src1_tags[] = R128TAG(reg_src1);
    tag_t src2_tags[] = M128TAG(src2);

    for (size_t i = 0; i < 16; i++) {
        RTAG[reg_dst][i] = tag_combine(src1_tags[i], src2_tags[i]);
    }
}

static void PIN_FAST_ANALYSIS_CALL m2r_ternary_opy(THREADID tid, uint32_t reg_dst, uint32_t reg_src1, ADDRINT src2) {
    tag_t src1_tags[] = R256TAG(reg_src1);
    tag_t src2_tags[] = M256TAG(src2);

    for (size_t i = 0; i < 32; i++) {
        RTAG[reg_dst][i] = tag_combine(src1_tags[i], src2_tags[i]);
    }
}
/*
static void PIN_FAST_ANALYSIS_CALL r2m_ternary_opx(THREADID tid, uint32_t reg_src1, uint32_t reg_src2, ADDRINT dst) {
    tag_t src1_tags[] = R128TAG(reg_src1);
    tag_t src2_tags[] = R128TAG(reg_src2);

    tag_t res_tags[16];
    for (size_t i = 0; i < 16; i++) {
        res_tags[i] = tag_combine(src1_tags[i], src2_tags[i]);
        tagmap_setb(dst + i, res_tags[i]);
    }
}

static void PIN_FAST_ANALYSIS_CALL r2m_ternary_opy(THREADID tid, uint32_t reg_src1, uint32_t reg_src2, ADDRINT dst) {
    tag_t src1_tags[] = R256TAG(reg_src1);
    tag_t src2_tags[] = R256TAG(reg_src2);

    tag_t res_tags[32];
    for (size_t i = 0; i < 32; i++) {
        res_tags[i] = tag_combine(src1_tags[i], src2_tags[i]);
        tagmap_setb(dst + i, res_tags[i]);
    }
}*/

static void PIN_FAST_ANALYSIS_CALL m2r_ternary_op_imm(THREADID tid, uint32_t reg_dst, uint64_t address, uint32_t byteCount) {
    tag_t *dst_tags = RTAG[reg_dst];
    for (size_t i = 0; i < byteCount; i++)
        dst_tags[i] = MTAG(address + i);
}

static void PIN_FAST_ANALYSIS_CALL r2r_ternary_op_imm(THREADID tid, uint32_t reg_dst, uint32_t reg_src1, uint32_t byteCount) {
    tag_t *src_tags = RTAG[reg_src1];
    tag_t *dst_tags = RTAG[reg_dst];
    for (size_t i = 0; i < byteCount; ++i)
        dst_tags[i] = src_tags[i];
}

void ins_ternary_op(INS ins) {
    REG reg_dst = INS_OperandReg(ins, OP_0);
    if (INS_OperandIsImmediate(ins, OP_2)) {
        if (INS_OperandIsMemory(ins, OP_1)) {
            if (REG_is_gr16(reg_dst)) {
                INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR) m2r_ternary_op_imm,
                            IARG_FAST_ANALYSIS_CALL, IARG_THREAD_ID,
                            IARG_UINT32, REG_INDX(reg_dst),
                            IARG_MEMORYREAD_EA,
                            IARG_UINT32, 2,
                            IARG_END);
            } else if (REG_is_gr32(reg_dst)) {
                INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR) m2r_ternary_op_imm,
                            IARG_FAST_ANALYSIS_CALL, IARG_THREAD_ID,
                            IARG_UINT32, REG_INDX(reg_dst),
                            IARG_MEMORYREAD_EA,
                            IARG_UINT32, 4,
                            IARG_END);
            } else if (REG_is_gr64(reg_dst)) {
                INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR) m2r_ternary_op_imm,
                            IARG_FAST_ANALYSIS_CALL, IARG_THREAD_ID,
                            IARG_UINT32, REG_INDX(reg_dst),
                            IARG_MEMORYREAD_EA,
                            IARG_UINT32, 8,
                            IARG_END);
            }
        } else {
            REG reg_src1 = INS_OperandReg(ins, OP_1);
            if (REG_is_gr16(reg_dst)) {
                INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR) r2r_ternary_op_imm,
                            IARG_FAST_ANALYSIS_CALL, IARG_THREAD_ID,
                            IARG_UINT32, REG_INDX(reg_dst),
                            IARG_UINT32, REG_INDX(reg_src1),
                            IARG_UINT32, 2,
                            IARG_END);
            } else if (REG_is_gr32(reg_dst)) {
                INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR) r2r_ternary_op_imm,
                            IARG_FAST_ANALYSIS_CALL, IARG_THREAD_ID,
                            IARG_UINT32, REG_INDX(reg_dst),
                            IARG_UINT32, REG_INDX(reg_src1),
                            IARG_UINT32, 4,
                            IARG_END);
            } else if (REG_is_gr64(reg_dst)) {
                INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR) r2r_ternary_op_imm,
                            IARG_FAST_ANALYSIS_CALL, IARG_THREAD_ID,
                            IARG_UINT32, REG_INDX(reg_dst),
                            IARG_UINT32, REG_INDX(reg_src1),
                            IARG_UINT32, 8,
                            IARG_END);
            }
        }
        
    } else if (INS_OperandIsMemory(ins, OP_2) && INS_OperandIsReg(ins, OP_1)) {
        REG reg_src1 = INS_OperandReg(ins, OP_1);
        if (REG_is_xmm(reg_src1)) {
            INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR)m2r_ternary_opx,
                           IARG_FAST_ANALYSIS_CALL, IARG_THREAD_ID,
                           IARG_UINT32, REG_INDX(reg_dst),
                           IARG_UINT32, REG_INDX(reg_src1),
                           IARG_MEMORYREAD_EA,
                           IARG_END);
        } else if (REG_is_ymm(reg_src1)) {
            INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR)m2r_ternary_opy,
                           IARG_FAST_ANALYSIS_CALL, IARG_THREAD_ID,
                           IARG_UINT32, REG_INDX(reg_dst),
                           IARG_UINT32, REG_INDX(reg_src1),
                           IARG_MEMORYREAD_EA,
                           IARG_END);
        } else if (REG_is_gr32(reg_src1)) {
            INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR)m2r_ternary_opl,
                           IARG_FAST_ANALYSIS_CALL, IARG_THREAD_ID,
                           IARG_UINT32, REG_INDX(reg_dst),
                           IARG_UINT32, REG_INDX(reg_src1),
                           IARG_MEMORYREAD_EA,
                           IARG_END);
        } else if (REG_is_gr64(reg_src1)) {
            INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR)m2r_ternary_opq,
                           IARG_FAST_ANALYSIS_CALL, IARG_THREAD_ID,
                           IARG_UINT32, REG_INDX(reg_dst),
                           IARG_UINT32, REG_INDX(reg_src1),
                           IARG_MEMORYREAD_EA,
                           IARG_END);
        } else {
            xed_iclass_enum_t ins_indx = (xed_iclass_enum_t)INS_Opcode(ins);
            LOG(std::string(__func__) + ": unhandled opcode (opcode=" + decstr(ins_indx) + ")\n");
        }
    } else {
        REG reg_src1 = INS_OperandReg(ins, OP_1);
        REG reg_src2 = INS_OperandReg(ins, OP_2);
        if (REG_is_xmm(reg_src1)) {
            INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR)r2r_ternary_opx,
                           IARG_FAST_ANALYSIS_CALL, IARG_THREAD_ID,
                           IARG_UINT32, REG_INDX(reg_src1),
                           IARG_UINT32, REG_INDX(reg_src2),
                           IARG_UINT32, REG_INDX(reg_dst),
                           IARG_END);
        } else if (REG_is_ymm(reg_src1)) {
            INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR)r2r_ternary_opy,
                           IARG_FAST_ANALYSIS_CALL, IARG_THREAD_ID,
                           IARG_UINT32, REG_INDX(reg_src1),
                           IARG_UINT32, REG_INDX(reg_src2),
                           IARG_UINT32, REG_INDX(reg_dst),
                           IARG_END);
        } else if (REG_is_gr32(reg_src1)) {
            INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR)r2r_ternary_opl,
                           IARG_FAST_ANALYSIS_CALL, IARG_THREAD_ID,
                           IARG_UINT32, REG_INDX(reg_src1),
                           IARG_UINT32, REG_INDX(reg_src2),
                           IARG_UINT32, REG_INDX(reg_dst),
                           IARG_END);
        } else if (REG_is_gr64(reg_src1)) {
            INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR)r2r_ternary_opq,
                           IARG_FAST_ANALYSIS_CALL, IARG_THREAD_ID,
                           IARG_UINT32, REG_INDX(reg_src1),
                           IARG_UINT32, REG_INDX(reg_src2),
                           IARG_UINT32, REG_INDX(reg_dst),
                           IARG_END);
        }  else {
            xed_iclass_enum_t ins_indx = (xed_iclass_enum_t)INS_Opcode(ins);
            LOG(std::string(__func__) + ": unhandled opcode (opcode=" + decstr(ins_indx) + ")\n");
        }
    }
}