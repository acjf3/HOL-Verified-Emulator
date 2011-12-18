
open HolKernel Parse boolLib bossLib; val _ = new_theory "comp_lang";

open wordsTheory wordsLib;
open mini_langTheory;


(* This script defines the language in which the ARM compiler is
   implemented. There are conflicting demands on this language: it
   ought to be easy to implement an ARM-to-MINI compiler in this
   language and, at the same time, it ought to be easy to
   compile-to-x86 compilers written in this language. (We need to
   compile the ARM compiler!)  Thus, the definition below is a
   compromise. *)


(* The compiler can evaluate expressions of the following form. *)

val _ = Hol_datatype `
  WORD_EXP = WORD_INSTRUCTION                         (* original instruction *)
           | WORD_IMM of word32                       (* any constant 32-bit word *)
           | WORD_LSL of WORD_EXP => num              (* left-shift *)
           | WORD_LSR of WORD_EXP => num              (* right-shift *)
           | WORD_AND of WORD_EXP => word32           (* word and with immediate *)
           | WORD_OR of WORD_EXP => word32            (* word or with immediate *)
           | WORD_BITS of WORD_EXP => num => num      (* or bits from instruction *)
           | WORD_SIGN_EXTEND of WORD_EXP => num      (* sign-extend from bit i *)
           | WORD_ROTATE of WORD_EXP => num           (* special word rotate right *)`;

val sign_extend_def = Define `
  sign_extend n (w:'a word) = w << (dimword(:'a) - n) >> (dimword(:'a) - n)`;

val arm_immediate_rotate_def = Define `
  arm_immediate_rotate n (w:word32) (e:word32) = e #>> (2 * w2n (w >> n && 15w))`;

val eval_word_exp_def = Define `
  (eval_word_exp w (WORD_INSTRUCTION) = w) /\
  (eval_word_exp w (WORD_IMM x) = x) /\
  (eval_word_exp w (WORD_LSR e n) = eval_word_exp w e >>> n) /\
  (eval_word_exp w (WORD_LSL e n) = eval_word_exp w e << n) /\
  (eval_word_exp w (WORD_AND e x) = eval_word_exp w e && x) /\
  (eval_word_exp w (WORD_OR e x) = eval_word_exp w e || x) /\
  (eval_word_exp w (WORD_BITS e i j) = eval_word_exp w e || (i -- j) w) /\
  (eval_word_exp w (WORD_SIGN_EXTEND e n) = sign_extend n (eval_word_exp w e)) /\
  (eval_word_exp w (WORD_ROTATE e n) = arm_immediate_rotate n w (eval_word_exp w e))`;

val e2n_def = Define `e2n w e = w2n (eval_word_exp w e)`;
val e2w_def = Define `e2w w e = w2w (eval_word_exp w e)`;
val e2b_def = Define `e2b w e = (eval_word_exp w e) ' 0`;


(* The compiler's purpose is to emit MINI instructions. *)

val _ = Hol_datatype `
  EMIT_EXP =
      EMIT_CONDITIONAL of WORD_EXP => WORD_EXP
    | EMIT_MARKER
    | EMIT_ASSERT of WORD_EXP
    | EMIT_MOVE of WORD_EXP => WORD_EXP
    | EMIT_IMM of WORD_EXP => WORD_EXP
    | EMIT_REG_READ of WORD_EXP => WORD_EXP
    | EMIT_REG_WRITE of WORD_EXP => WORD_EXP
    | EMIT_MEM_BYTE_READ of WORD_EXP
    | EMIT_MEM_WORD_READ of WORD_EXP
    | EMIT_MEM_BYTE_WRITE of WORD_EXP
    | EMIT_MEM_WORD_WRITE of WORD_EXP
    | EMIT_ADD_IMM of WORD_EXP => WORD_EXP
    | EMIT_BINOP of WORD_EXP => WORD_EXP`;

val eval_emit_exp_def = Define `
  (eval_emit_exp w (EMIT_CONDITIONAL w1 w2) = MINI_CONDITIONAL (e2w w w1) (e2w w w2)) /\
  (eval_emit_exp w (EMIT_MARKER) = MINI_MARKER) /\
  (eval_emit_exp w (EMIT_ASSERT w1) = MINI_ASSERT (num2assert (e2n w w1))) /\
  (eval_emit_exp w (EMIT_MOVE w1 w2) = MINI_MOVE (e2w w w1) (e2w w w2)) /\
  (eval_emit_exp w (EMIT_IMM w1 w2) = MINI_IMM (e2w w w1) (e2w w w2)) /\
  (eval_emit_exp w (EMIT_REG_READ w1 w2) = MINI_REG_READ (e2w w w1) (e2w w w2)) /\
  (eval_emit_exp w (EMIT_REG_WRITE w1 w2) = MINI_REG_WRITE (e2w w w1) (e2w w w2)) /\
  (eval_emit_exp w (EMIT_MEM_BYTE_READ w1) = MINI_MEM_BYTE_READ (e2w w w1)) /\
  (eval_emit_exp w (EMIT_MEM_WORD_READ w1) = MINI_MEM_WORD_READ (e2w w w1)) /\
  (eval_emit_exp w (EMIT_MEM_BYTE_WRITE w1) = MINI_MEM_BYTE_WRITE (e2w w w1)) /\
  (eval_emit_exp w (EMIT_MEM_WORD_WRITE w1) = MINI_MEM_WORD_WRITE (e2w w w1)) /\
  (eval_emit_exp w (EMIT_ADD_IMM w1 w2) = MINI_ADD_IMM (e2w w w1) (e2w w w2)) /\
  (eval_emit_exp w (EMIT_BINOP w1 w2) = MINI_BINOP (num2binop (e2n w w1)) (e2b w w2))`;


(* The main part of the compiler itself will consist of one (big)
   COMPILER_EXP, which describes how each ARM instruction is to be
   translated into a sequence of MINI instructions. *)

val _ = Hol_datatype `
  COMPILER_EXP =
      COMPILER_SKIP
    | COMPILER_SEQ of COMPILER_EXP => COMPILER_EXP
    | COMPILER_IF of WORD_EXP => word32 => COMPILER_EXP => COMPILER_EXP
    | COMPILER_TRY of COMPILER_EXP => COMPILER_EXP
    | COMPILER_EMIT of EMIT_EXP`;

val compiler_try_def = Define `
  compiler_try x y = let res = x in if res = [] then y else res`;

val eval_compiler_exp_def = Define `
  (eval_compiler_exp w (COMPILER_SKIP) = []) /\
  (eval_compiler_exp w (COMPILER_SEQ x y) =
     eval_compiler_exp w x ++ eval_compiler_exp w y) /\
  (eval_compiler_exp w (COMPILER_IF e w1 x y) =
     if eval_word_exp w e = w1 then eval_compiler_exp w x
                               else eval_compiler_exp w y) /\
  (eval_compiler_exp w (COMPILER_TRY x y) =
     compiler_try (eval_compiler_exp w x) (eval_compiler_exp w y)) /\
  (eval_compiler_exp w (COMPILER_EMIT z) = [eval_emit_exp w z])`;


(* A compiler is correct if the code it produces always simulates
   running the ARM code. The generated code is allowed to set ok to
   false and that way give up. *)

val ARM_OK_def = Define `
  ARM_OK state =
    (ARM_ARCH state = ARMv4) /\ (ARM_EXTENSIONS state = {}) /\
    (ARM_UNALIGNED_SUPPORT state) /\ (ARM_READ_EVENT_REGISTER state) /\
    ~(ARM_READ_INTERRUPT_WAIT state) /\ ~(ARM_READ_SCTLR sctlrV state) /\
    (ARM_READ_SCTLR sctlrA state) /\ ~(ARM_READ_SCTLR sctlrU state) /\
    (ARM_READ_IT state = 0w) /\ ~(ARM_READ_STATUS psrJ state) /\
    ~(ARM_READ_STATUS psrT state) /\ ~(ARM_READ_STATUS psrE state) /\
    (ARM_MODE state = 16w)`;

val ARM_ERASE_ACCESSES_def = Define `
  ARM_ERASE_ACCESSES s = s with accesses := []`;

val COMP_CORRECT_def = Define `
  COMP_CORRECT compiler =
    !instr. let code = eval_compiler_exp instr compiler in
              (code = []) \/
              !regs ok s. let (regs1,ok1,s1) = eval_mini_list code (regs,ok,s) in
                            (ARM_READ_MEM_WORD (ARM_READ_REG 15w s) s = instr) /\
                            aligned (ARM_READ_REG 15w s,2) /\ ARM_OK s /\ ok1 ==>
                            ?s2. (ARM_NEXT NoInterrupt s = SOME s2) /\ ARM_OK s2 /\
                                 (ARM_ERASE_ACCESSES s1 = ARM_ERASE_ACCESSES s2)`;

(* This property can be decomposed across COMPILER_TRY. *)

val COMP_CORRECT_TRY = store_thm("COMP_CORRECT_TRY",
  ``!x y. COMP_CORRECT x /\ COMP_CORRECT y ==> COMP_CORRECT (COMPILER_TRY x y)``,
  SIMP_TAC std_ss [COMP_CORRECT_def,eval_compiler_exp_def,
     LET_DEF,compiler_try_def] THEN METIS_TAC []);

(* The NOT_IMPLEMENTED assertion is always a correct compilation. *)

val COMP_CORRECT_EMIT_NOT_IMPLEMENTED = store_thm("COMP_CORRECT_EMIT_NOT_IMPLEMENTED",
  ``COMP_CORRECT (COMPILER_EMIT (EMIT_ASSERT (WORD_IMM 0w)))``,
  EVAL_TAC THEN SIMP_TAC std_ss []);

val _ = export_theory();
