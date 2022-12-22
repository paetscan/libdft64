#pragma GCC diagnostic ignored "-Wmaybe-uninitialized"

#include "ins_xfer_op.h"
#include "ins_clear_op.h"
#include "ins_helper.h"

/* threads context */
extern thread_ctx_t *threads_ctx;

void PIN_FAST_ANALYSIS_CALL r2r_xfer_opb_ul(THREADID tid, uint32_t dst,
                                            uint32_t src) {
  tag_t src_tag = RTAG[src][0];

  RTAG[dst][1] = src_tag;
}

void PIN_FAST_ANALYSIS_CALL r2r_xfer_opb_lu(THREADID tid, uint32_t dst,
                                            uint32_t src) {
  tag_t src_tag = RTAG[src][1];

  RTAG[dst][0] = src_tag;
}

void PIN_FAST_ANALYSIS_CALL r2r_xfer_opb_u(THREADID tid, uint32_t dst,
                                           uint32_t src) {
  tag_t src_tag = RTAG[src][1];

  RTAG[dst][1] = src_tag;
}

void PIN_FAST_ANALYSIS_CALL r2r_xfer_opb_l(THREADID tid, uint32_t dst,
                                           uint32_t src) {
  tag_t src_tag = RTAG[src][0];

  RTAG[dst][0] = src_tag;
}

void PIN_FAST_ANALYSIS_CALL r2r_xfer_opw(THREADID tid, uint32_t dst,
                                         uint32_t src) {
  for (size_t i = 0; i < 2; i++) {
    RTAG[dst][i] = RTAG[src][i];
    /*
    if (!tag_is_empty(RTAG[src][i]))
      LOGD("[xfer_w] i%ld: src: %d (%d) -> dst: %d (%d)\n", i, src,
           RTAG[src][i], dst, RTAG[dst][i]);
           */
  }
}

void PIN_FAST_ANALYSIS_CALL r2r_xfer_opl(THREADID tid, uint32_t dst,
                                         uint32_t src) {
  for (size_t i = 0; i < 4; i++) {
    RTAG[dst][i] = RTAG[src][i];
  }
}

void PIN_FAST_ANALYSIS_CALL r2r_xfer_opq(THREADID tid, uint32_t dst,
                                         uint32_t src) {
  for (size_t i = 0; i < 8; i++) {
    RTAG[dst][i] = RTAG[src][i];
  }
}

void PIN_FAST_ANALYSIS_CALL r2r_xfer_opx(THREADID tid, uint32_t dst,
                                         uint32_t src) {
  for (size_t i = 0; i < 16; i++)
    RTAG[dst][i] = RTAG[src][i];
}

void PIN_FAST_ANALYSIS_CALL r2r_xfer_opy(THREADID tid, uint32_t dst,
                                         uint32_t src) {
  for (size_t i = 0; i < 32; i++)
    RTAG[dst][i] = RTAG[src][i];
}

void PIN_FAST_ANALYSIS_CALL m2r_xfer_opb_u(THREADID tid, uint32_t dst,
                                           ADDRINT src) {
  tag_t src_tag = MTAG(src);

  RTAG[dst][1] = src_tag;
}

void PIN_FAST_ANALYSIS_CALL m2r_xfer_opb_l(THREADID tid, uint32_t dst,
                                           ADDRINT src) {
  tag_t src_tag = MTAG(src);

  RTAG[dst][0] = src_tag;
}

void PIN_FAST_ANALYSIS_CALL m2r_xfer_opw(THREADID tid, uint32_t dst,
                                         ADDRINT src) {
  for (size_t i = 0; i < 2; i++)
    RTAG[dst][i] = MTAG(src + i);
}

void PIN_FAST_ANALYSIS_CALL m2r_xfer_opl(THREADID tid, uint32_t dst,
                                         ADDRINT src) {
  for (size_t i = 0; i < 4; i++)
    RTAG[dst][i] = MTAG(src + i);
}

void PIN_FAST_ANALYSIS_CALL m2r_xfer_opq(THREADID tid, uint32_t dst,
                                         ADDRINT src) {
  for (size_t i = 0; i < 8; i++)
    RTAG[dst][i] = MTAG(src + i);
}

void PIN_FAST_ANALYSIS_CALL m2r_xfer_opx(THREADID tid, uint32_t dst,
                                         ADDRINT src) {
  for (size_t i = 0; i < 16; i++)
    RTAG[dst][i] = MTAG(src + i);
}

void PIN_FAST_ANALYSIS_CALL m2r_xfer_opy(THREADID tid, uint32_t dst,
                                         ADDRINT src) {
  for (size_t i = 0; i < 32; i++)
    RTAG[dst][i] = MTAG(src + i);
}

void PIN_FAST_ANALYSIS_CALL r2m_xfer_opb_u(THREADID tid, ADDRINT dst,
                                           uint32_t src) {
  tag_t src_tag = RTAG[src][1];

  tagmap_setb(dst, src_tag);
}

void PIN_FAST_ANALYSIS_CALL r2m_xfer_opb_l(THREADID tid, ADDRINT dst,
                                           uint32_t src) {
  tag_t src_tag = RTAG[src][0];

  tagmap_setb(dst, src_tag);
}

void PIN_FAST_ANALYSIS_CALL r2m_xfer_opw(THREADID tid, ADDRINT dst,
                                         uint32_t src) {
  tag_t *src_tags = RTAG[src];

  tagmap_setb(dst, src_tags[0]);
  tagmap_setb(dst + 1, src_tags[1]);
}

void PIN_FAST_ANALYSIS_CALL r2m_xfer_opl(THREADID tid, ADDRINT dst,
                                         uint32_t src) {
  tag_t *src_tags = RTAG[src];

  for (size_t i = 0; i < 4; i++)
    tagmap_setb(dst + i, src_tags[i]);
}

void PIN_FAST_ANALYSIS_CALL r2m_xfer_opq(THREADID tid, ADDRINT dst,
                                         uint32_t src) {
  tag_t *src_tags = RTAG[src];

  for (size_t i = 0; i < 8; i++)
    tagmap_setb(dst + i, src_tags[i]);
}

void PIN_FAST_ANALYSIS_CALL r2m_xfer_opx(THREADID tid, ADDRINT dst,
                                         uint32_t src) {
  tag_t *src_tags = RTAG[src];

  for (size_t i = 0; i < 16; i++)
    tagmap_setb(dst + i, src_tags[i]);
}

void PIN_FAST_ANALYSIS_CALL r2m_xfer_opy(THREADID tid, ADDRINT dst,
                                         uint32_t src) {
  tag_t *src_tags = RTAG[src];

  for (size_t i = 0; i < 32; i++)
    tagmap_setb(dst + i, src_tags[i]);
}

void PIN_FAST_ANALYSIS_CALL m2m_xfer_opb(ADDRINT dst, ADDRINT src) {
  tag_t src_tag = MTAG(src);

  tagmap_setb(dst, src_tag);
}

void PIN_FAST_ANALYSIS_CALL m2m_xfer_opw(ADDRINT dst, ADDRINT src) {
  for (size_t i = 0; i < 2; i++)
    tagmap_setb(dst + i, MTAG(src + i));
}

void PIN_FAST_ANALYSIS_CALL m2m_xfer_opl(ADDRINT dst, ADDRINT src) {
  for (size_t i = 0; i < 4; i++)
    tagmap_setb(dst + i, MTAG(src + i));
}

void PIN_FAST_ANALYSIS_CALL m2m_xfer_opq(ADDRINT dst, ADDRINT src) {
  for (size_t i = 0; i < 8; i++)
    tagmap_setb(dst + i, MTAG(src + i));
}

void PIN_FAST_ANALYSIS_CALL m2r_xfer_opq_h(THREADID tid, uint32_t dst,
                                           ADDRINT src) {
  for (size_t i = 0; i < 8; i++)
    RTAG[dst][i + 8] = MTAG(src + i);
}

void PIN_FAST_ANALYSIS_CALL r2m_xfer_opq_h(THREADID tid, ADDRINT dst,
                                           uint32_t src) {
  tag_t *src_tags = RTAG[src];

  for (size_t i = 0; i < 8; i++)
    tagmap_setb(dst + i, src_tags[i + 8]);
}

static void PIN_FAST_ANALYSIS_CALL r2m_xfer_opbn(THREADID tid, ADDRINT dst,
                                                 ADDRINT count,
                                                 ADDRINT eflags) {
  tag_t src_tag = RTAG[DFT_REG_RAX][0];
  if (likely(EFLAGS_DF(eflags) == 0)) {
    /* EFLAGS.DF = 0 */
    for (size_t i = 0; i < count; i++) {
      tagmap_setb(dst + i, src_tag);
    }
  } else {
    /* EFLAGS.DF = 1 */
    for (size_t i = 0; i < count; i++) {
      size_t dst_addr = dst - count + 1 + i;
      tagmap_setb(dst_addr, src_tag);
    }
  }
}

static void PIN_FAST_ANALYSIS_CALL r2m_xfer_opwn(THREADID tid, ADDRINT dst,
                                                 ADDRINT count,
                                                 ADDRINT eflags) {
  tag_t src_tag[] = R16TAG(DFT_REG_RAX);
  if (likely(EFLAGS_DF(eflags) == 0)) {
    /* EFLAGS.DF = 0 */
    for (size_t i = 0; i < (count << 1); i++) {
      tagmap_setb(dst + i, src_tag[i % 2]);
    }
  } else {
    /* EFLAGS.DF = 1 */
    for (size_t i = 0; i < (count << 1); i++) {
      size_t dst_addr = dst - (count << 1) + 1 + i;
      tagmap_setb(dst_addr, src_tag[i % 2]);
    }
  }
}

static void PIN_FAST_ANALYSIS_CALL r2m_xfer_opln(THREADID tid, ADDRINT dst,
                                                 ADDRINT count,
                                                 ADDRINT eflags) {
  tag_t src_tag[] = R32TAG(DFT_REG_RAX);
  if (likely(EFLAGS_DF(eflags) == 0)) {
    /* EFLAGS.DF = 0 */
    for (size_t i = 0; i < (count << 2); i++) {
      tagmap_setb(dst + i, src_tag[i % 4]);
    }
  } else {
    /* EFLAGS.DF = 1 */
    for (size_t i = 0; i < (count << 2); i++) {
      size_t dst_addr = dst - (count << 2) + 1 + i;
      tagmap_setb(dst_addr, src_tag[i % 4]);
    }
  }
}

static void PIN_FAST_ANALYSIS_CALL r2m_xfer_opqn(THREADID tid, ADDRINT dst,
                                                 ADDRINT count,
                                                 ADDRINT eflags) {
  tag_t src_tag[] = R64TAG(DFT_REG_RAX);
  if (likely(EFLAGS_DF(eflags) == 0)) {
    /* EFLAGS.DF = 0 */
    for (size_t i = 0; i < (count << 3); i++) {
      tagmap_setb(dst + i, src_tag[i % 8]);
    }
  } else {
    /* EFLAGS.DF = 1 */
    for (size_t i = 0; i < (count << 3); i++) {
      size_t dst_addr = dst - (count << 3) + 1 + i;
      tagmap_setb(dst_addr, src_tag[i % 8]);
    }
  }
}

static ADDRINT PIN_FAST_ANALYSIS_CALL rep_predicate(BOOL first_iteration) {
  /* return the flag; typically this is true only once */
  return first_iteration;
}

static void PIN_FAST_ANALYSIS_CALL _lea_opw(THREADID tid, uint32_t dst,
                                            uint32_t base, uint32_t index) {
  for (size_t i = 0; i < 2; i++)
    RTAG[dst][i] = tag_combine(RTAG[base][i], RTAG[index][i]);
}

static void PIN_FAST_ANALYSIS_CALL _lea_opl(THREADID tid, uint32_t dst,
                                            uint32_t base, uint32_t index) {
  for (size_t i = 0; i < 4; i++)
    RTAG[dst][i] = tag_combine(RTAG[base][i], RTAG[index][i]);
}

static void PIN_FAST_ANALYSIS_CALL _lea_opq(THREADID tid, uint32_t dst,
                                            uint32_t base, uint32_t index) {
  for (size_t i = 0; i < 8; i++)
    RTAG[dst][i] = tag_combine(RTAG[base][i], RTAG[index][i]);
}

void ins_xfer_op(INS ins) {
  REG reg_dst, reg_src;
  if (INS_MemoryOperandCount(ins) == 0) {
    reg_dst = INS_OperandReg(ins, OP_0);
    reg_src = INS_OperandReg(ins, OP_1);
    if (REG_is_gr64(reg_dst)) {
      R2R_CALL(r2r_xfer_opq, reg_dst, reg_src);
    } else if (REG_is_gr32(reg_dst)) {
      R2R_CALL(r2r_xfer_opl, reg_dst, reg_src);
    } else if (REG_is_gr16(reg_dst)) {
      R2R_CALL(r2r_xfer_opw, reg_dst, reg_src);
    } else if (REG_is_xmm(reg_dst)) {
      R2R_CALL(r2r_xfer_opx, reg_dst, reg_src);
    } else if (REG_is_ymm(reg_dst)) {
      R2R_CALL(r2r_xfer_opy, reg_dst, reg_src);
    } else if (REG_is_mm(reg_dst)) {
      R2R_CALL(r2r_xfer_opq, reg_dst, reg_src);
    } else {
      if (REG_is_Lower8(reg_dst) && REG_is_Lower8(reg_src)) {
        R2R_CALL(r2r_xfer_opb_l, reg_dst, reg_src);
      } else if (REG_is_Upper8(reg_dst) && REG_is_Upper8(reg_src)) {
        R2R_CALL(r2r_xfer_opb_u, reg_dst, reg_src);
      } else if (REG_is_Lower8(reg_dst)) {
        R2R_CALL(r2r_xfer_opb_lu, reg_dst, reg_src);
      } else {
        R2R_CALL(r2r_xfer_opb_ul, reg_dst, reg_src);
      }
    }
  } else if (INS_OperandIsMemory(ins, OP_1)) {
    reg_dst = INS_OperandReg(ins, OP_0);
    if (REG_is_gr64(reg_dst)) {
      M2R_CALL(m2r_xfer_opq, reg_dst);
    } else if (REG_is_gr32(reg_dst)) {
      M2R_CALL(m2r_xfer_opl, reg_dst);
    } else if (REG_is_gr16(reg_dst)) {
      M2R_CALL(m2r_xfer_opw, reg_dst);
    } else if (REG_is_xmm(reg_dst)) {
      M2R_CALL(m2r_xfer_opx, reg_dst);
    } else if (REG_is_ymm(reg_dst)) {
      M2R_CALL(m2r_xfer_opy, reg_dst);
    } else if (REG_is_mm(reg_dst)) {
      M2R_CALL(m2r_xfer_opq, reg_dst);
    } else if (REG_is_Upper8(reg_dst)) {
      M2R_CALL(m2r_xfer_opb_u, reg_dst);
    } else {
      M2R_CALL(m2r_xfer_opb_l, reg_dst);
    }
  } else {
    reg_src = INS_OperandReg(ins, OP_1);
    if (REG_is_gr64(reg_src)) {
      R2M_CALL(r2m_xfer_opq, reg_src);
    } else if (REG_is_gr32(reg_src)) {
      R2M_CALL(r2m_xfer_opl, reg_src);
    } else if (REG_is_gr16(reg_src)) {
      R2M_CALL(r2m_xfer_opw, reg_src);
    } else if (REG_is_xmm(reg_src)) {
      R2M_CALL(r2m_xfer_opx, reg_src);
    } else if (REG_is_ymm(reg_src)) {
      R2M_CALL(r2m_xfer_opy, reg_src);
    } else if (REG_is_mm(reg_src)) {
      R2M_CALL(r2m_xfer_opq, reg_src);
    } else if (REG_is_Upper8(reg_src)) {
      R2M_CALL(r2m_xfer_opb_u, reg_src);
    } else {
      R2M_CALL(r2m_xfer_opb_l, reg_src);
    }
  }
}

void ins_xfer_op_predicated(INS ins) {
  REG reg_dst, reg_src;
  if (INS_MemoryOperandCount(ins) == 0) {
    reg_dst = INS_OperandReg(ins, OP_0);
    reg_src = INS_OperandReg(ins, OP_1);
    if (REG_is_gr64(reg_dst)) {
      R2R_CALL_P(r2r_xfer_opq, reg_dst, reg_src);
    } else if (REG_is_gr32(reg_dst)) {
      R2R_CALL_P(r2r_xfer_opl, reg_dst, reg_src);
    } else {
      R2R_CALL_P(r2r_xfer_opw, reg_dst, reg_src);
    }
  } else {
    reg_dst = INS_OperandReg(ins, OP_0);
    if (REG_is_gr64(reg_dst)) {
      M2R_CALL_P(m2r_xfer_opq, reg_dst);
    } else if (REG_is_gr32(reg_dst)) {
      M2R_CALL_P(m2r_xfer_opl, reg_dst);
    } else {
      M2R_CALL_P(m2r_xfer_opw, reg_dst);
    }
  }
}

void ins_push_op(INS ins) {
  REG reg_src;
  if (INS_OperandIsReg(ins, OP_0)) {
    reg_src = INS_OperandReg(ins, OP_0);
    if (REG_is_gr64(reg_src)) {
      R2M_CALL(r2m_xfer_opq, reg_src);
    } else if (REG_is_gr32(reg_src)) {
      R2M_CALL(r2m_xfer_opl, reg_src);
    } else {
      R2M_CALL(r2m_xfer_opw, reg_src);
    }
  } else if (INS_OperandIsMemory(ins, OP_0)) {
    if (INS_MemoryOperandSize(ins, OP_0) == BIT2BYTE(MEM_64BIT_LEN)) {
      M2M_CALL(m2m_xfer_opq);
    } else if (INS_MemoryOperandSize(ins, OP_0) == BIT2BYTE(MEM_LONG_LEN)) {
      M2M_CALL(m2m_xfer_opl);
    } else {
      M2M_CALL(m2m_xfer_opw);
    }
  } else {
    INT32 n = INS_OperandWidth(ins, OP_0) / 8;
    M_CLEAR_N(n);
  }
}

void ins_pop_op(INS ins) {
  REG reg_dst;
  if (INS_OperandIsReg(ins, OP_0)) {
    reg_dst = INS_OperandReg(ins, OP_0);
    if (REG_is_gr64(reg_dst)) {
      M2R_CALL(m2r_xfer_opq, reg_dst);
    } else if (REG_is_gr32(reg_dst)) {
      M2R_CALL(m2r_xfer_opl, reg_dst);
    } else {
      M2R_CALL(m2r_xfer_opw, reg_dst);
    }
  } else if (INS_OperandIsMemory(ins, OP_0)) {
    if (INS_MemoryOperandSize(ins, OP_0) == BIT2BYTE(MEM_64BIT_LEN)) {
      M2M_CALL(m2m_xfer_opq);
    } else if (INS_MemoryOperandSize(ins, OP_0) == BIT2BYTE(MEM_LONG_LEN)) {
      M2M_CALL(m2m_xfer_opl);
    } else {
      M2M_CALL(m2m_xfer_opw);
    }
  }
}

void ins_stos_ins(INS ins, AFUNPTR fn) {
  INS_InsertIfPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)rep_predicate,
                             IARG_FAST_ANALYSIS_CALL, IARG_FIRST_REP_ITERATION,
                             IARG_END);
  INS_InsertThenPredicatedCall(
      ins, IPOINT_BEFORE, fn, IARG_FAST_ANALYSIS_CALL, IARG_THREAD_ID,
      IARG_MEMORYWRITE_EA, IARG_REG_VALUE, INS_RepCountRegister(ins),
      IARG_REG_VALUE, INS_OperandReg(ins, OP_4), IARG_END);
}

void ins_stosb(INS ins) {
  if (INS_RepPrefix(ins)) {
    ins_stos_ins(ins, (AFUNPTR)r2m_xfer_opbn);
  } else {
    R2M_CALL(r2m_xfer_opb_l, REG_AL);
  }
}

void ins_stosw(INS ins) {
  if (INS_RepPrefix(ins)) {
    ins_stos_ins(ins, (AFUNPTR)r2m_xfer_opwn);
  } else {
    R2M_CALL(r2m_xfer_opw, REG_AX);
  }
}

void ins_stosd(INS ins) {
  if (INS_RepPrefix(ins)) {
    ins_stos_ins(ins, (AFUNPTR)r2m_xfer_opln);
  } else {
    R2M_CALL(r2m_xfer_opw, REG_EAX);
  }
}

void ins_stosq(INS ins) {
  if (INS_RepPrefix(ins)) {
    ins_stos_ins(ins, (AFUNPTR)r2m_xfer_opqn);
  } else {
    R2M_CALL(r2m_xfer_opw, REG_RAX);
  }
}

void ins_movlp(INS ins) {
  if (INS_OperandIsMemory(ins, OP_0)) {
    REG reg_src = INS_OperandReg(ins, OP_1);
    R2M_CALL(r2m_xfer_opq, reg_src);
  } else {
    REG reg_dst = INS_OperandReg(ins, OP_0);
    M2R_CALL(m2r_xfer_opq, reg_dst);
  }
}

void ins_movhp(INS ins) {
  if (INS_OperandIsMemory(ins, OP_0)) {
    REG reg_src = INS_OperandReg(ins, OP_1);
    R2M_CALL(r2m_xfer_opq_h, reg_src);
  } else {
    REG reg_dst = INS_OperandReg(ins, OP_0);
    M2R_CALL(m2r_xfer_opq_h, reg_dst);
  }
}

void ins_lea(INS ins) {
  REG reg_base = INS_MemoryBaseReg(ins);
  REG reg_indx = INS_MemoryIndexReg(ins);
  REG reg_dst = INS_OperandReg(ins, OP_0);
  if (reg_base == REG_INVALID() && reg_indx == REG_INVALID()) {
    ins_clear_op(ins);
  }
  if (reg_base != REG_INVALID() && reg_indx == REG_INVALID()) {
    if (REG_is_gr64(reg_dst)) {
      R2R_CALL(r2r_xfer_opq, reg_dst, reg_base);
    } else if (REG_is_gr32(reg_dst)) {
      R2R_CALL(r2r_xfer_opl, reg_dst, reg_base);
    } else if (REG_is_gr16(reg_dst)) {
      R2R_CALL(r2r_xfer_opw, reg_dst, reg_base);
    }
  }
  if (reg_base == REG_INVALID() && reg_indx != REG_INVALID()) {
    if (REG_is_gr64(reg_dst)) {
      R2R_CALL(r2r_xfer_opq, reg_dst, reg_indx);
    } else if (REG_is_gr32(reg_dst)) {
      R2R_CALL(r2r_xfer_opl, reg_dst, reg_indx);
    } else if (REG_is_gr16(reg_dst)) {
      R2R_CALL(r2r_xfer_opw, reg_dst, reg_indx);
    }
  }
  if (reg_base != REG_INVALID() && reg_indx != REG_INVALID()) {
    if (REG_is_gr64(reg_dst)) {
      RR2R_CALL(_lea_opq, reg_dst, reg_base, reg_indx);
    } else if (REG_is_gr32(reg_dst)) {
      RR2R_CALL(_lea_opl, reg_dst, reg_base, reg_indx);
    } else if (REG_is_gr16(reg_dst)) {
      RR2R_CALL(_lea_opw, reg_dst, reg_base, reg_indx);
    }
  }
}

void PIN_FAST_ANALYSIS_CALL m2r_xfer_opw_rev(THREADID tid, uint32_t dst,
                                             ADDRINT src) {
  for (size_t i = 0; i < 2; i++)
    RTAG[dst][i] = MTAG(src + (1 - i));
}

void PIN_FAST_ANALYSIS_CALL m2r_xfer_opl_rev(THREADID tid, uint32_t dst,
                                             ADDRINT src) {
  for (size_t i = 0; i < 4; i++)
    RTAG[dst][i] = MTAG(src + (3 - i));
}

void PIN_FAST_ANALYSIS_CALL m2r_xfer_opq_rev(THREADID tid, uint32_t dst,
                                             ADDRINT src) {
  for (size_t i = 0; i < 8; i++)
    RTAG[dst][i] = MTAG(src + (7 - i));
}

void PIN_FAST_ANALYSIS_CALL r2m_xfer_opw_rev(THREADID tid, ADDRINT dst,
                                             uint32_t src) {
  tag_t *src_tags = RTAG[src];
  tagmap_setb(dst, src_tags[1]);
  tagmap_setb(dst + 1, src_tags[0]);
}

void PIN_FAST_ANALYSIS_CALL r2m_xfer_opl_rev(THREADID tid, ADDRINT dst,
                                             uint32_t src) {
  tag_t *src_tags = RTAG[src];
  for (size_t i = 0; i < 4; i++)
    tagmap_setb(dst + (3 - i), src_tags[i]);
}

void PIN_FAST_ANALYSIS_CALL r2m_xfer_opq_rev(THREADID tid, ADDRINT dst,
                                             uint32_t src) {
  tag_t *src_tags = RTAG[src];
  for (size_t i = 0; i < 8; i++)
    tagmap_setb(dst + (7 - i), src_tags[i]);
}

void ins_movbe_op(INS ins) {
  if (INS_OperandIsMemory(ins, OP_1)) {
    REG reg_dst = INS_OperandReg(ins, OP_0);
    if (REG_is_gr64(reg_dst)) {
      M2R_CALL(m2r_xfer_opq_rev, reg_dst);
    } else if (REG_is_gr32(reg_dst)) {
      M2R_CALL(m2r_xfer_opl_rev, reg_dst);
    } else if (REG_is_gr16(reg_dst)) {
      M2R_CALL(m2r_xfer_opw_rev, reg_dst);
    }
  } else {
    REG reg_src = INS_OperandReg(ins, OP_1);
    if (REG_is_gr64(reg_src)) {
      R2M_CALL(r2m_xfer_opq_rev, reg_src);
    } else if (REG_is_gr32(reg_src)) {
      R2M_CALL(r2m_xfer_opl_rev, reg_src);
    } else if (REG_is_gr16(reg_src)) {
      R2M_CALL(r2m_xfer_opw_rev, reg_src);
    }
  }
}

void PIN_FAST_ANALYSIS_CALL r2r_punpcklbw_opq(THREADID tid, uint32_t dst, uint32_t src) {
    tag_t src_tags[] = R64TAG(src);
    tag_t dst_tags[] = R64TAG(dst);

    for (size_t i = 0; i < 4; i++) {
        RTAG[dst][2*i] = dst_tags[i];
        RTAG[dst][2*i + 1] = src_tags[i];
    }
}

void PIN_FAST_ANALYSIS_CALL r2r_punpcklbw_opx(THREADID tid, uint32_t dst, uint32_t src) {
    tag_t src_tags[] = R128TAG(src);
    tag_t dst_tags[] = R128TAG(dst);

    for (size_t i = 0; i < 8; i++) {
        RTAG[dst][2*i] = dst_tags[i];
        RTAG[dst][2*i + 1] = src_tags[i];
    }
}

void PIN_FAST_ANALYSIS_CALL m2r_punpcklbw_opq(THREADID tid, uint32_t dst, ADDRINT src) {
    tag_t src_tags[] = M64TAG(src);
    tag_t dst_tags[] = R64TAG(dst);

    for (size_t i = 0; i < 4; i++) {
        RTAG[dst][2*i] = dst_tags[i];
        RTAG[dst][2*i + 1] = src_tags[i];
    }
}

void PIN_FAST_ANALYSIS_CALL m2r_punpcklbw_opx(THREADID tid, uint32_t dst, ADDRINT src) {
    tag_t src_tags[] = M128TAG(src);
    tag_t dst_tags[] = R128TAG(dst);

    for (size_t i = 0; i < 8; i++) {
        RTAG[dst][2*i] = dst_tags[i];
        RTAG[dst][2*i + 1] = src_tags[i];
    }
}

void ins_punpcklbw_op(INS ins) {
    if (INS_MemoryOperandCount(ins) == 0) {
        REG reg_dst = INS_OperandReg(ins, OP_0);
        REG reg_src = INS_OperandReg(ins, OP_1);
        if (REG_is_mm(reg_dst)) {
            R2R_CALL(r2r_punpcklbw_opq, reg_dst, reg_src);
        } else if (REG_is_xmm(reg_dst)) {
            R2R_CALL(r2r_punpcklbw_opx, reg_dst, reg_src);
        } else {
            xed_iclass_enum_t ins_indx = (xed_iclass_enum_t)INS_Opcode(ins);
            LOG(std::string(__func__) + ": unhandled opcode (opcode=" + decstr(ins_indx) + ")\n");
        }
    } else {
        REG reg_dst = INS_OperandReg(ins, OP_0);
        if (REG_is_mm(reg_dst)) {
            M2R_CALL(m2r_punpcklbw_opq, reg_dst);
        } else if (REG_is_xmm(reg_dst)) {
            M2R_CALL(m2r_punpcklbw_opx, reg_dst);
        } else {
            xed_iclass_enum_t ins_indx = (xed_iclass_enum_t)INS_Opcode(ins);
            LOG(std::string(__func__) + ": unhandled opcode (opcode=" + decstr(ins_indx) + ")\n");
        }
    }
}

void PIN_FAST_ANALYSIS_CALL r2r_punpcklwd_opq(THREADID tid, uint32_t dst, uint32_t src) {
    tag_t src_tags[] = R64TAG(src);
    tag_t dst_tags[] = R64TAG(dst);

    size_t j = 0;
    for (size_t i = 0; i < 8; i += 4) {
        RTAG[dst][i] = dst_tags[j];
        RTAG[dst][i + 2] = src_tags[j];
        j++;
        RTAG[dst][i + 1] = dst_tags[j];
        RTAG[dst][i + 3] = src_tags[j];
        j++;
    }
}

void PIN_FAST_ANALYSIS_CALL r2r_punpcklwd_opx(THREADID tid, uint32_t dst, uint32_t src) {
    tag_t src_tags[] = R128TAG(src);
    tag_t dst_tags[] = R128TAG(dst);

    size_t j = 0;
    for (size_t i = 0; i < 16; i += 4) {
        RTAG[dst][i] = dst_tags[j];
        RTAG[dst][i + 2] = src_tags[j];
        j++;
        RTAG[dst][i + 1] = dst_tags[j];
        RTAG[dst][i + 3] = src_tags[j];
        j++;
    }
}

void PIN_FAST_ANALYSIS_CALL m2r_punpcklwd_opq(THREADID tid, uint32_t dst, ADDRINT src) {
    tag_t src_tags[] = M64TAG(src);
    tag_t dst_tags[] = R64TAG(dst);

    size_t j = 0;
    for (size_t i = 0; i < 8; i += 4) {
        RTAG[dst][i] = dst_tags[j];
        RTAG[dst][i + 2] = src_tags[j];
        j++;
        RTAG[dst][i + 1] = dst_tags[j];
        RTAG[dst][i + 3] = src_tags[j];
        j++;
    }
}

void PIN_FAST_ANALYSIS_CALL m2r_punpcklwd_opx(THREADID tid, uint32_t dst, ADDRINT src) {
    tag_t src_tags[] = M128TAG(src);
    tag_t dst_tags[] = R128TAG(dst);

    size_t j = 0;
    for (size_t i = 0; i < 16; i += 4) {
        RTAG[dst][i] = dst_tags[j];
        RTAG[dst][i + 2] = src_tags[j];
        j++;
        RTAG[dst][i + 1] = dst_tags[j];
        RTAG[dst][i + 3] = src_tags[j];
        j++;
    }
}

void ins_punpcklwd_op(INS ins) {
    if (INS_MemoryOperandCount(ins) == 0) {
        REG reg_dst = INS_OperandReg(ins, OP_0);
        REG reg_src = INS_OperandReg(ins, OP_1);
        if (REG_is_mm(reg_dst)) {
            R2R_CALL(r2r_punpcklwd_opq, reg_dst, reg_src);
        } else if (REG_is_xmm(reg_dst)) {
            R2R_CALL(r2r_punpcklwd_opx, reg_dst, reg_src);
        }  else {
            xed_iclass_enum_t ins_indx = (xed_iclass_enum_t)INS_Opcode(ins);
            LOG(std::string(__func__) + ": unhandled opcode (opcode=" + decstr(ins_indx) + ")\n");
        }
    } else {
        REG reg_dst = INS_OperandReg(ins, OP_0);
        if (REG_is_mm(reg_dst)) {
            M2R_CALL(m2r_punpcklwd_opq, reg_dst);
        } else if (REG_is_xmm(reg_dst)) {
            M2R_CALL(m2r_punpcklwd_opx, reg_dst);
        }  else {
            xed_iclass_enum_t ins_indx = (xed_iclass_enum_t)INS_Opcode(ins);
            LOG(std::string(__func__) + ": unhandled opcode (opcode=" + decstr(ins_indx) + ")\n");
        }
    }
}

void PIN_FAST_ANALYSIS_CALL r2r_punpckldq_opq(THREADID tid, uint32_t dst, uint32_t src) {
    tag_t src_tags[] = R64TAG(src);
    tag_t dst_tags[] = R64TAG(dst);

    size_t j = 0;
    for (size_t i = 0; i < 8; i += 8) {
        RTAG[dst][i] = dst_tags[j];
        RTAG[dst][i + 4] = src_tags[j];
        j++;
        RTAG[dst][i + 1] = dst_tags[j];
        RTAG[dst][i + 5] = src_tags[j];
        j++;
        RTAG[dst][i + 2] = dst_tags[j];
        RTAG[dst][i + 6] = src_tags[j];
        j++;
        RTAG[dst][i + 3] = dst_tags[j];
        RTAG[dst][i + 7] = src_tags[j];
        j++;
    }
}

void PIN_FAST_ANALYSIS_CALL r2r_punpckldq_opx(THREADID tid, uint32_t dst, uint32_t src) {
    tag_t src_tags[] = R128TAG(src);
    tag_t dst_tags[] = R128TAG(dst);

    size_t j = 0;
    for (size_t i = 0; i < 16; i += 8) {
        RTAG[dst][i] = dst_tags[j];
        RTAG[dst][i + 4] = src_tags[j];
        j++;
        RTAG[dst][i + 1] = dst_tags[j];
        RTAG[dst][i + 5] = src_tags[j];
        j++;
        RTAG[dst][i + 2] = dst_tags[j];
        RTAG[dst][i + 6] = src_tags[j];
        j++;
        RTAG[dst][i + 3] = dst_tags[j];
        RTAG[dst][i + 7] = src_tags[j];
        j++;
    }
}

void PIN_FAST_ANALYSIS_CALL m2r_punpckldq_opq(THREADID tid, uint32_t dst, ADDRINT src) {
    tag_t src_tags[] = M64TAG(src);
    tag_t dst_tags[] = R64TAG(dst);

    size_t j = 0;
    for (size_t i = 0; i < 8; i += 8) {
        RTAG[dst][i] = dst_tags[j];
        RTAG[dst][i + 4] = src_tags[j];
        j++;
        RTAG[dst][i + 1] = dst_tags[j];
        RTAG[dst][i + 5] = src_tags[j];
        j++;
        RTAG[dst][i + 2] = dst_tags[j];
        RTAG[dst][i + 6] = src_tags[j];
        j++;
        RTAG[dst][i + 3] = dst_tags[j];
        RTAG[dst][i + 7] = src_tags[j];
        j++;
    }
}

void PIN_FAST_ANALYSIS_CALL m2r_punpckldq_opx(THREADID tid, uint32_t dst, ADDRINT src) {
    tag_t src_tags[] = M128TAG(src);
    tag_t dst_tags[] = R128TAG(dst);

    size_t j = 0;
    for (size_t i = 0; i < 16; i += 8) {
        RTAG[dst][i] = dst_tags[j];
        RTAG[dst][i + 4] = src_tags[j];
        j++;
        RTAG[dst][i + 1] = dst_tags[j];
        RTAG[dst][i + 5] = src_tags[j];
        j++;
        RTAG[dst][i + 2] = dst_tags[j];
        RTAG[dst][i + 6] = src_tags[j];
        j++;
        RTAG[dst][i + 3] = dst_tags[j];
        RTAG[dst][i + 7] = src_tags[j];
        j++;
    }
}

void ins_punpckldq_op(INS ins) {
    if (INS_MemoryOperandCount(ins) == 0) {
        REG reg_dst = INS_OperandReg(ins, OP_0);
        REG reg_src = INS_OperandReg(ins, OP_1);
        if (REG_is_mm(reg_dst)) {
            R2R_CALL(r2r_punpckldq_opq, reg_dst, reg_src);
        } else if (REG_is_xmm(reg_dst)) {
            R2R_CALL(r2r_punpckldq_opx, reg_dst, reg_src);
        }  else {
            xed_iclass_enum_t ins_indx = (xed_iclass_enum_t)INS_Opcode(ins);
            LOG(std::string(__func__) + ": unhandled opcode (opcode=" + decstr(ins_indx) + ")\n");
        }
    } else {
        REG reg_dst = INS_OperandReg(ins, OP_0);
        if (REG_is_mm(reg_dst)) {
            M2R_CALL(m2r_punpckldq_opq, reg_dst);
        } else if (REG_is_xmm(reg_dst)) {
            M2R_CALL(m2r_punpckldq_opx, reg_dst);
        }  else {
            xed_iclass_enum_t ins_indx = (xed_iclass_enum_t)INS_Opcode(ins);
            LOG(std::string(__func__) + ": unhandled opcode (opcode=" + decstr(ins_indx) + ")\n");
        }
    }
}

void PIN_FAST_ANALYSIS_CALL r2r_punpcklqdq_opx(THREADID tid, uint32_t dst, uint32_t src) {
    tag_t src_tags[] = R128TAG(src);
    tag_t dst_tags[] = R128TAG(dst);

    size_t j = 0;
    for (size_t i = 0; i < 8; i++) {
        RTAG[dst][i] = dst_tags[j];
        RTAG[dst][i + 8] = src_tags[j];
        j++;
    }
}

void PIN_FAST_ANALYSIS_CALL m2r_punpcklqdq_opx(THREADID tid, uint32_t dst, ADDRINT src) {
    tag_t src_tags[] = M128TAG(src);
    tag_t dst_tags[] = R128TAG(dst);

    size_t j = 0;
    for (size_t i = 0; i < 8; i++) {
        RTAG[dst][i] = dst_tags[j];
        RTAG[dst][i + 8] = src_tags[j];
        j++;
    }
}

void ins_punpcklqdq_op(INS ins) {
    if (INS_MemoryOperandCount(ins) == 0) {
        REG reg_dst = INS_OperandReg(ins, OP_0);
        REG reg_src = INS_OperandReg(ins, OP_1);
        if (REG_is_xmm(reg_dst)) {
            R2R_CALL(r2r_punpcklqdq_opx, reg_dst, reg_src);
        } else {
            xed_iclass_enum_t ins_indx = (xed_iclass_enum_t)INS_Opcode(ins);
            LOG(std::string(__func__) + ": unhandled opcode (opcode=" + decstr(ins_indx) + ")\n");
        }
    } else {
        REG reg_dst = INS_OperandReg(ins, OP_0);
        if (REG_is_xmm(reg_dst)) {
            M2R_CALL(m2r_punpcklqdq_opx, reg_dst);
        } else {
            xed_iclass_enum_t ins_indx = (xed_iclass_enum_t)INS_Opcode(ins);
            LOG(std::string(__func__) + ": unhandled opcode (opcode=" + decstr(ins_indx) + ")\n");
        }
    }
}

void PIN_FAST_ANALYSIS_CALL r2r_punpckhbw_opq(THREADID tid, uint32_t dst, uint32_t src) {
    tag_t src_tags[] = R64TAG(src);
    tag_t dst_tags[] = R64TAG(dst);

    for (size_t i = 0; i < 4; i++) {
        RTAG[dst][2*i] = dst_tags[i + 4];
        RTAG[dst][2*i + 1] = src_tags[i + 4];
    }
}

void PIN_FAST_ANALYSIS_CALL r2r_punpckhbw_opx(THREADID tid, uint32_t dst, uint32_t src) {
    tag_t src_tags[] = R128TAG(src);
    tag_t dst_tags[] = R128TAG(dst);

    for (size_t i = 0; i < 8; i++) {
        RTAG[dst][2*i] = dst_tags[i + 8];
        RTAG[dst][2*i + 1] = src_tags[i + 8];
    }
}

void PIN_FAST_ANALYSIS_CALL m2r_punpckhbw_opq(THREADID tid, uint32_t dst, ADDRINT src) {
    tag_t src_tags[] = M64TAG(src);
    tag_t dst_tags[] = R64TAG(dst);

    for (size_t i = 0; i < 4; i++) {
        RTAG[dst][2*i] = dst_tags[i + 4];
        RTAG[dst][2*i + 1] = src_tags[i + 4];
    }
}

void PIN_FAST_ANALYSIS_CALL m2r_punpckhbw_opx(THREADID tid, uint32_t dst, ADDRINT src) {
    tag_t src_tags[] = M128TAG(src);
    tag_t dst_tags[] = R128TAG(dst);

    for (size_t i = 0; i < 8; i++) {
        RTAG[dst][2*i] = dst_tags[i + 8];
        RTAG[dst][2*i + 1] = src_tags[i + 8];
    }
}

void ins_punpckhbw_op(INS ins) {
    if (INS_MemoryOperandCount(ins) == 0) {
        REG reg_dst = INS_OperandReg(ins, OP_0);
        REG reg_src = INS_OperandReg(ins, OP_1);
        if (REG_is_mm(reg_dst)) {
            R2R_CALL(r2r_punpckhbw_opq, reg_dst, reg_src);
        } else if (REG_is_xmm(reg_dst)) {
            R2R_CALL(r2r_punpckhbw_opx, reg_dst, reg_src);
        } else {
            xed_iclass_enum_t ins_indx = (xed_iclass_enum_t)INS_Opcode(ins);
            LOG(std::string(__func__) + ": unhandled opcode (opcode=" + decstr(ins_indx) + ")\n");
        }
    } else {
        REG reg_dst = INS_OperandReg(ins, OP_0);
        if (REG_is_mm(reg_dst)) {
            M2R_CALL(m2r_punpckhbw_opq, reg_dst);
        } else if (REG_is_xmm(reg_dst)) {
            M2R_CALL(m2r_punpckhbw_opx, reg_dst);
        } else {
            xed_iclass_enum_t ins_indx = (xed_iclass_enum_t)INS_Opcode(ins);
            LOG(std::string(__func__) + ": unhandled opcode (opcode=" + decstr(ins_indx) + ")\n");
        }
    }
}

void PIN_FAST_ANALYSIS_CALL r2r_punpckhwd_opq(THREADID tid, uint32_t dst, uint32_t src) {
    tag_t src_tags[] = R64TAG(src);
    tag_t dst_tags[] = R64TAG(dst);

    size_t j = 4;
    for (size_t i = 0; i < 8; i += 4) {
        RTAG[dst][i] = dst_tags[j];
        RTAG[dst][i + 2] = src_tags[j];
        j++;
        RTAG[dst][i + 1] = dst_tags[j];
        RTAG[dst][i + 3] = src_tags[j];
        j++;
    }
}

void PIN_FAST_ANALYSIS_CALL r2r_punpckhwd_opx(THREADID tid, uint32_t dst, uint32_t src) {
    tag_t src_tags[] = R128TAG(src);
    tag_t dst_tags[] = R128TAG(dst);

    size_t j = 8;
    for (size_t i = 0; i < 16; i += 4) {
        RTAG[dst][i] = dst_tags[j];
        RTAG[dst][i + 2] = src_tags[j];
        j++;
        RTAG[dst][i + 1] = dst_tags[j];
        RTAG[dst][i + 3] = src_tags[j];
        j++;
    }
}

void PIN_FAST_ANALYSIS_CALL m2r_punpckhwd_opq(THREADID tid, uint32_t dst, ADDRINT src) {
    tag_t src_tags[] = M64TAG(src);
    tag_t dst_tags[] = R64TAG(dst);

    size_t j = 4;
    for (size_t i = 0; i < 8; i += 4) {
        RTAG[dst][i] = dst_tags[j];
        RTAG[dst][i + 2] = src_tags[j];
        j++;
        RTAG[dst][i + 1] = dst_tags[j];
        RTAG[dst][i + 3] = src_tags[j];
        j++;
    }
}

void PIN_FAST_ANALYSIS_CALL m2r_punpckhwd_opx(THREADID tid, uint32_t dst, ADDRINT src) {
    tag_t src_tags[] = M128TAG(src);
    tag_t dst_tags[] = R128TAG(dst);

    size_t j = 8;
    for (size_t i = 0; i < 16; i += 4) {
        RTAG[dst][i] = dst_tags[j];
        RTAG[dst][i + 2] = src_tags[j];
        j++;
        RTAG[dst][i + 1] = dst_tags[j];
        RTAG[dst][i + 3] = src_tags[j];
        j++;
    }
}

void ins_punpckhwd_op(INS ins) {
    if (INS_MemoryOperandCount(ins) == 0) {
        REG reg_dst = INS_OperandReg(ins, OP_0);
        REG reg_src = INS_OperandReg(ins, OP_1);
        if (REG_is_mm(reg_dst)) {
            R2R_CALL(r2r_punpckhwd_opq, reg_dst, reg_src);
        } else if (REG_is_xmm(reg_dst)) {
            R2R_CALL(r2r_punpckhwd_opx, reg_dst, reg_src);
        }  else {
            xed_iclass_enum_t ins_indx = (xed_iclass_enum_t)INS_Opcode(ins);
            LOG(std::string(__func__) + ": unhandled opcode (opcode=" + decstr(ins_indx) + ")\n");
        }
    } else {
        REG reg_dst = INS_OperandReg(ins, OP_0);
        if (REG_is_mm(reg_dst)) {
            M2R_CALL(m2r_punpckhwd_opq, reg_dst);
        } else if (REG_is_xmm(reg_dst)) {
            M2R_CALL(m2r_punpckhwd_opx, reg_dst);
        }  else {
            xed_iclass_enum_t ins_indx = (xed_iclass_enum_t)INS_Opcode(ins);
            LOG(std::string(__func__) + ": unhandled opcode (opcode=" + decstr(ins_indx) + ")\n");
        }
    }
}

void PIN_FAST_ANALYSIS_CALL r2r_punpckhdq_opq(THREADID tid, uint32_t dst, uint32_t src) {
    tag_t src_tags[] = R64TAG(src);
    tag_t dst_tags[] = R64TAG(dst);

    size_t j = 4;
    for (size_t i = 0; i < 8; i += 8) {
        RTAG[dst][i] = dst_tags[j];
        RTAG[dst][i + 4] = src_tags[j];
        j++;
        RTAG[dst][i + 1] = dst_tags[j];
        RTAG[dst][i + 5] = src_tags[j];
        j++;
        RTAG[dst][i + 2] = dst_tags[j];
        RTAG[dst][i + 6] = src_tags[j];
        j++;
        RTAG[dst][i + 3] = dst_tags[j];
        RTAG[dst][i + 7] = src_tags[j];
        j++;
    }
}

void PIN_FAST_ANALYSIS_CALL r2r_punpckhdq_opx(THREADID tid, uint32_t dst, uint32_t src) {
    tag_t src_tags[] = R128TAG(src);
    tag_t dst_tags[] = R128TAG(dst);

    size_t j = 8;
    for (size_t i = 0; i < 16; i += 8) {
        RTAG[dst][i] = dst_tags[j];
        RTAG[dst][i + 4] = src_tags[j];
        j++;
        RTAG[dst][i + 1] = dst_tags[j];
        RTAG[dst][i + 5] = src_tags[j];
        j++;
        RTAG[dst][i + 2] = dst_tags[j];
        RTAG[dst][i + 6] = src_tags[j];
        j++;
        RTAG[dst][i + 3] = dst_tags[j];
        RTAG[dst][i + 7] = src_tags[j];
        j++;
    }
}

void PIN_FAST_ANALYSIS_CALL m2r_punpckhdq_opq(THREADID tid, uint32_t dst, ADDRINT src) {
    tag_t src_tags[] = M64TAG(src);
    tag_t dst_tags[] = R64TAG(dst);

    size_t j = 4;
    for (size_t i = 0; i < 8; i += 8) {
        RTAG[dst][i] = dst_tags[j];
        RTAG[dst][i + 4] = src_tags[j];
        j++;
        RTAG[dst][i + 1] = dst_tags[j];
        RTAG[dst][i + 5] = src_tags[j];
        j++;
        RTAG[dst][i + 2] = dst_tags[j];
        RTAG[dst][i + 6] = src_tags[j];
        j++;
        RTAG[dst][i + 3] = dst_tags[j];
        RTAG[dst][i + 7] = src_tags[j];
        j++;
    }
}

void PIN_FAST_ANALYSIS_CALL m2r_punpckhdq_opx(THREADID tid, uint32_t dst, ADDRINT src) {
    tag_t src_tags[] = M128TAG(src);
    tag_t dst_tags[] = R128TAG(dst);

    size_t j = 8;
    for (size_t i = 0; i < 16; i += 8) {
        RTAG[dst][i] = dst_tags[j];
        RTAG[dst][i + 4] = src_tags[j];
        j++;
        RTAG[dst][i + 1] = dst_tags[j];
        RTAG[dst][i + 5] = src_tags[j];
        j++;
        RTAG[dst][i + 2] = dst_tags[j];
        RTAG[dst][i + 6] = src_tags[j];
        j++;
        RTAG[dst][i + 3] = dst_tags[j];
        RTAG[dst][i + 7] = src_tags[j];
        j++;
    }
}

void ins_punpckhdq_op(INS ins) {
    if (INS_MemoryOperandCount(ins) == 0) {
        REG reg_dst = INS_OperandReg(ins, OP_0);
        REG reg_src = INS_OperandReg(ins, OP_1);
        if (REG_is_mm(reg_dst)) {
            R2R_CALL(r2r_punpckhdq_opq, reg_dst, reg_src);
        } else if (REG_is_xmm(reg_dst)) {
            R2R_CALL(r2r_punpckhdq_opx, reg_dst, reg_src);
        }  else {
            xed_iclass_enum_t ins_indx = (xed_iclass_enum_t)INS_Opcode(ins);
            LOG(std::string(__func__) + ": unhandled opcode (opcode=" + decstr(ins_indx) + ")\n");
        }
    } else {
        REG reg_dst = INS_OperandReg(ins, OP_0);
        if (REG_is_mm(reg_dst)) {
            M2R_CALL(m2r_punpckhdq_opq, reg_dst);
        } else if (REG_is_xmm(reg_dst)) {
            M2R_CALL(m2r_punpckhdq_opx, reg_dst);
        }  else {
            xed_iclass_enum_t ins_indx = (xed_iclass_enum_t)INS_Opcode(ins);
            LOG(std::string(__func__) + ": unhandled opcode (opcode=" + decstr(ins_indx) + ")\n");
        }
    }
}

void PIN_FAST_ANALYSIS_CALL r2r_punpckhqdq_opx(THREADID tid, uint32_t dst, uint32_t src) {
    tag_t src_tags[] = R128TAG(src);
    tag_t dst_tags[] = R128TAG(dst);

    size_t j = 8;
    for (size_t i = 0; i < 8; i++) {
        RTAG[dst][i] = dst_tags[j];
        RTAG[dst][i + 8] = src_tags[j];
        j++;
    }
}

void PIN_FAST_ANALYSIS_CALL m2r_punpckhqdq_opx(THREADID tid, uint32_t dst, ADDRINT src) {
    tag_t src_tags[] = M128TAG(src);
    tag_t dst_tags[] = R128TAG(dst);

    size_t j = 8;
    for (size_t i = 0; i < 8; i++) {
        RTAG[dst][i] = dst_tags[j];
        RTAG[dst][i + 8] = src_tags[j];
        j++;
    }
}

void ins_punpckhqdq_op(INS ins) {
    if (INS_MemoryOperandCount(ins) == 0) {
        REG reg_dst = INS_OperandReg(ins, OP_0);
        REG reg_src = INS_OperandReg(ins, OP_1);
        if (REG_is_xmm(reg_dst)) {
            R2R_CALL(r2r_punpckhqdq_opx, reg_dst, reg_src);
        } else {
            xed_iclass_enum_t ins_indx = (xed_iclass_enum_t)INS_Opcode(ins);
            LOG(std::string(__func__) + ": unhandled opcode (opcode=" + decstr(ins_indx) + ")\n");
        }
    } else {
        REG reg_dst = INS_OperandReg(ins, OP_0);
        if (REG_is_xmm(reg_dst)) {
            M2R_CALL(m2r_punpckhqdq_opx, reg_dst);
        } else {
            xed_iclass_enum_t ins_indx = (xed_iclass_enum_t)INS_Opcode(ins);
            LOG(std::string(__func__) + ": unhandled opcode (opcode=" + decstr(ins_indx) + ")\n");
        }
    }
}

void PIN_FAST_ANALYSIS_CALL r2r_vpunpckhqdq_opx(THREADID tid, uint32_t dst, uint32_t src1, uint32_t src2) {
    tag_t src1_tags[] = R128TAG(src1);
    tag_t src2_tags[] = R128TAG(src2);

    size_t j = 8;
    for (size_t i = 0; i < 8; i++) {
        RTAG[dst][i] = src2_tags[j];
        RTAG[dst][i + 8] = src1_tags[j];
        j++;
    }
}

void PIN_FAST_ANALYSIS_CALL m2r_vpunpckhqdq_opx(THREADID tid, uint32_t dst, uint32_t src1, ADDRINT src2) {
    tag_t src2_tags[] = M128TAG(src2);
    tag_t src1_tags[] = R128TAG(src1);

    size_t j = 8;
    for (size_t i = 0; i < 8; i++) {
        RTAG[dst][i] = src2_tags[j];
        RTAG[dst][i + 8] = src1_tags[j];
        j++;
    }
}

void ins_vpunpckhqdq_op(INS ins) {
    REG reg_dst = INS_OperandReg(ins, OP_0);
    REG reg_src1 = INS_OperandReg(ins, OP_1);
    if (INS_MemoryOperandCount(ins) == 0) {
        REG reg_src2 = INS_OperandReg(ins, OP_2);
        if (REG_is_xmm(reg_dst)) {
            INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR)r2r_vpunpckhqdq_opx,
                           IARG_FAST_ANALYSIS_CALL, IARG_THREAD_ID,
                           IARG_UINT32, REG_INDX(reg_src1),
                           IARG_UINT32, REG_INDX(reg_src2),
                           IARG_UINT32, REG_INDX(reg_dst),
                           IARG_END);
        } else {
            xed_iclass_enum_t ins_indx = (xed_iclass_enum_t)INS_Opcode(ins);
            LOG(std::string(__func__) + ": unhandled opcode (opcode=" + decstr(ins_indx) + ")\n");
        }
    } else {
        if (REG_is_xmm(reg_dst)) {
            INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR)m2r_vpunpckhqdq_opx,
                           IARG_FAST_ANALYSIS_CALL, IARG_THREAD_ID,
                           IARG_UINT32, REG_INDX(reg_dst),
                           IARG_UINT32, REG_INDX(reg_src1),
                           IARG_MEMORYREAD_EA,
                           IARG_END);
        } else {
            xed_iclass_enum_t ins_indx = (xed_iclass_enum_t)INS_Opcode(ins);
            LOG(std::string(__func__) + ": unhandled opcode (opcode=" + decstr(ins_indx) + ")\n");
        }
    }
}

static void PIN_FAST_ANALYSIS_CALL r2r_pshufd_op(THREADID tid, uint32_t reg_dst, uint32_t reg_src, uint32_t imm, uint32_t byteCount, uint32_t chunkSize, bool isVex128) {
    tag_t src_tags[byteCount];
    for (size_t i = 0; i < byteCount; i++) {
        src_tags[i] = RTAG[reg_src][i];
    }

    size_t choice0 = imm & 0x3; // imm[1:0]
    size_t choice1 = (imm & 0xc) >> 2; // imm[3:2]
    size_t choice2 = (imm & 0x30) >> 4; // imm[5:4]
    size_t choice3 = (imm & 0xc0) >> 6; // imm[7:6]

    for (size_t i = 0; i < chunkSize; ++i)
    {
        RTAG[reg_dst][i] = src_tags[i + (choice0 * chunkSize)];
        RTAG[reg_dst][i + 4] = src_tags[i + (choice1 * chunkSize)];
        RTAG[reg_dst][i + 8] = src_tags[i + (choice2 * chunkSize)];
        RTAG[reg_dst][i + 12] = src_tags[i + (choice3 * chunkSize)];
    }

    if (isVex128)
    {
        for (size_t i = 16; i < 32; ++i)
        {
            RTAG[reg_dst][i] = tag_traits<tag_t>::cleared_val;
        }
    }
}

static void PIN_FAST_ANALYSIS_CALL m2r_pshufd_op(THREADID tid, uint32_t reg_dst, uint64_t addr, uint32_t imm, uint32_t byteCount, uint32_t chunkSize, bool isVex128) {
    tag_t src_tags[byteCount];
    for (size_t i = 0; i < byteCount; i++) {
        src_tags[i] = MTAG(addr + i);
    }

    size_t choice0 = imm & 0x3; // imm[1:0]
    size_t choice1 = (imm & 0xc) >> 2; // imm[3:2]
    size_t choice2 = (imm & 0x30) >> 4; // imm[5:4]
    size_t choice3 = (imm & 0xc0) >> 6; // imm[7:6]

    for (size_t i = 0; i < chunkSize; ++i)
    {
        RTAG[reg_dst][i] = src_tags[i + (choice0 * chunkSize)];
        RTAG[reg_dst][i + 4] = src_tags[i + (choice1 * chunkSize)];
        RTAG[reg_dst][i + 8] = src_tags[i + (choice2 * chunkSize)];
        RTAG[reg_dst][i + 12] = src_tags[i + (choice3 * chunkSize)];
    }

    if (isVex128)
    {
        for (size_t i = 16; i < 32; ++i)
        {
            RTAG[reg_dst][i] = tag_traits<tag_t>::cleared_val;
        }
    }
}

void ins_pshufd_op(INS ins) {
    REG reg_dst, reg_src;
    uint32_t imm = INS_OperandImmediate(ins, OP_2) & 0xff;
    uint32_t chunkSize = 4;
    if (INS_OperandIsMemory(ins, OP_1)) {
        reg_dst = INS_OperandReg(ins, OP_0);
        if (REG_is_xmm(reg_dst)) {
            INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR)m2r_pshufd_op,
                           IARG_FAST_ANALYSIS_CALL, IARG_THREAD_ID,
                           IARG_UINT32, REG_INDX(reg_dst),
                           IARG_MEMORYREAD_EA,
                           IARG_UINT32, imm,
                           IARG_UINT32, 16,
                           IARG_UINT32, chunkSize,
                           IARG_BOOL, false,
                           IARG_END);
        } else if (REG_is_ymm(reg_dst)) {
            INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR)m2r_pshufd_op,
                           IARG_FAST_ANALYSIS_CALL, IARG_THREAD_ID,
                           IARG_UINT32, REG_INDX(reg_dst),
                           IARG_MEMORYREAD_EA,
                           IARG_UINT32, imm,
                           IARG_UINT32, 32,
                           IARG_UINT32, chunkSize,
                           IARG_BOOL, false,
                           IARG_END);
        } else {
            xed_iclass_enum_t ins_indx = (xed_iclass_enum_t)INS_Opcode(ins);
            LOG(std::string(__func__) + ": unhandled opcode (opcode=" + decstr(ins_indx) + ")\n");
        }
    } else {
        reg_dst = INS_OperandReg(ins, OP_0);
        reg_src = INS_OperandReg(ins, OP_1);
        if (REG_is_xmm(reg_dst)) {
            INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR)r2r_pshufd_op,
                           IARG_FAST_ANALYSIS_CALL, IARG_THREAD_ID,
                           IARG_UINT32, REG_INDX(reg_dst),
                           IARG_UINT32, REG_INDX(reg_src),
                           IARG_UINT32, imm,
                           IARG_UINT32, 16,
                           IARG_UINT32, chunkSize,
                           IARG_BOOL, false,
                           IARG_END);
        } else if (REG_is_ymm(reg_dst)) {
            INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR)r2r_pshufd_op,
                           IARG_FAST_ANALYSIS_CALL, IARG_THREAD_ID,
                           IARG_UINT32, REG_INDX(reg_dst),
                           IARG_UINT32, REG_INDX(reg_src),
                           IARG_UINT32, imm,
                           IARG_UINT32, 32,
                           IARG_UINT32, chunkSize,
                           IARG_BOOL, false,
                           IARG_END);
        } else {
            xed_iclass_enum_t ins_indx = (xed_iclass_enum_t)INS_Opcode(ins);
            LOG(std::string(__func__) + ": unhandled opcode (opcode=" + decstr(ins_indx) + ")\n");
        }
    }
}

void ins_vpshufd_op(INS ins) {
    REG reg_dst, reg_src;
    uint32_t imm = INS_OperandImmediate(ins, OP_2) & 0xff;
    uint32_t chunkSize = 4;
    if (INS_OperandIsMemory(ins, OP_1)) {
        reg_dst = INS_OperandReg(ins, OP_0);
        if (REG_is_xmm(reg_dst)) {
            INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR)m2r_pshufd_op,
                           IARG_FAST_ANALYSIS_CALL, IARG_THREAD_ID,
                           IARG_UINT32, REG_INDX(reg_dst),
                           IARG_MEMORYREAD_EA,
                           IARG_UINT32, imm,
                           IARG_UINT32, 16,
                           IARG_UINT32, chunkSize,
                           IARG_BOOL, true,
                           IARG_END);
        } else if (REG_is_ymm(reg_dst)) {
            INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR)m2r_pshufd_op,
                           IARG_FAST_ANALYSIS_CALL, IARG_THREAD_ID,
                           IARG_UINT32, REG_INDX(reg_dst),
                           IARG_MEMORYREAD_EA,
                           IARG_UINT32, imm,
                           IARG_UINT32, 32,
                           IARG_UINT32, chunkSize,
                           IARG_BOOL, false,
                           IARG_END);
        } else {
            xed_iclass_enum_t ins_indx = (xed_iclass_enum_t)INS_Opcode(ins);
            LOG(std::string(__func__) + ": unhandled opcode (opcode=" + decstr(ins_indx) + ")\n");
        }
    } else {
        reg_dst = INS_OperandReg(ins, OP_0);
        reg_src = INS_OperandReg(ins, OP_1);
        if (REG_is_xmm(reg_dst)) {
            INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR)r2r_pshufd_op,
                           IARG_FAST_ANALYSIS_CALL, IARG_THREAD_ID,
                           IARG_UINT32, REG_INDX(reg_dst),
                           IARG_UINT32, REG_INDX(reg_src),
                           IARG_UINT32, imm,
                           IARG_UINT32, 16,
                           IARG_UINT32, chunkSize,
                           IARG_BOOL, true,
                           IARG_END);
        } else if (REG_is_ymm(reg_dst)) {
            INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR)r2r_pshufd_op,
                           IARG_FAST_ANALYSIS_CALL, IARG_THREAD_ID,
                           IARG_UINT32, REG_INDX(reg_dst),
                           IARG_UINT32, REG_INDX(reg_src),
                           IARG_UINT32, imm,
                           IARG_UINT32, 32,
                           IARG_UINT32, chunkSize,
                           IARG_BOOL, false,
                           IARG_END);
        } else {
            xed_iclass_enum_t ins_indx = (xed_iclass_enum_t)INS_Opcode(ins);
            LOG(std::string(__func__) + ": unhandled opcode (opcode=" + decstr(ins_indx) + ")\n");
        }
    }
}