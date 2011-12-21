
open HolKernel Parse boolLib bossLib; val _ = new_theory "comp_example";

open mini_langTheory comp_langTheory comp_langLib;

open wordsTheory wordsLib listTheory arithmeticTheory;
open arm_decoderTheory arm_opsemTheory arm_coretypesTheory armTheory armLib;
open arm_stepTheory arm_seq_monadTheory arm_encoderLib;


infix \\
val op \\ = op THEN


(* We start by defining a compiler that can produce MINI code for
   <data><cond> rd,rn,#<immediate>. The following is the encoding we
   compile. *)

val arm_data_imm_enc_tm =
  ``((1w << 25
      || w2w (opcode:word4) << 21
      || w2w (rn:word4) << 16
      || w2w (rd:word4) << 12
      || w2w (rotate_imm:word4) << 8
      || w2w (imm8:word8)
      || w2w (s:word1) << 20
      || w2w (cond:word4) << 28)):word32``

val cond_bits = ``(31 -- 28):word32->word32``
val opcode_bits = ``(24 -- 21):word32->word32``
val rn_bits = ``(19 -- 16):word32->word32``
val rd_bits = ``(15 -- 12):word32->word32``
val imm8_bits = ``(7 -- 0):word32->word32``
val rotate_imm_bits = ``(11 -- 8):word32->word32``
val s_bit = ``(w:word32) ' 20``

val select_lemma = blastLib.BBLAST_PROVE
  ``(^cond_bits ^arm_data_imm_enc_tm = w2w cond) /\
    (^opcode_bits ^arm_data_imm_enc_tm = w2w opcode) /\
    (^rn_bits ^arm_data_imm_enc_tm = w2w rn) /\
    (^rd_bits ^arm_data_imm_enc_tm = w2w rd) /\
    (^imm8_bits ^arm_data_imm_enc_tm = w2w imm8) /\
    (^rotate_imm_bits ^arm_data_imm_enc_tm = w2w rotate_imm) /\
    (^arm_data_imm_enc_tm ' 20 = (s:word1) ' 0)``

val w2w_lemma = blastLib.BBLAST_PROVE
  ``(w2w ((w2w w8):word32) = w8:word8) /\
    (w2w ((w2w w4):word32) = w4:word4) /\
    (w2w ((w2w w2):word32) = w2:word2)``


(* The mask with which we identify this instruction *)

val eval = rand o concl o EVAL

fun subst_words f g tm =
   let
      fun subst_word v =
         v |-> eval (f (wordsSyntax.dim_of v))
         handle HOL_ERR _ => ``v:num`` |-> ``v:num``
   in
      subst (map (subst_word) (g tm)) tm
   end

fun mk_word_0 ty = wordsSyntax.mk_n2w (``0n``, ty);

val max_words  = subst_words wordsSyntax.mk_word_T free_vars;
val zero_words = subst_words mk_word_0 free_vars;

val zero_lits =
   subst_words mk_word_0 (HolKernel.find_terms wordsSyntax.is_word_literal);

val mask =
   eval (wordsSyntax.mk_word_1comp (max_words (zero_lits arm_data_imm_enc_tm)))

val match = eval (zero_words arm_data_imm_enc_tm)

(* We prove that the mask is suffient. *)

val tm =
   list_mk_exists(free_vars arm_data_imm_enc_tm, ``w = ^arm_data_imm_enc_tm``)

(* This would have been a pain to prove without blast! *)

val mask_lemma = Q.prove(`!w. ((w:word32) && ^mask = ^match) ==> ^tm`,
  REPEAT STRIP_TAC
  \\ MAP_EVERY Q.EXISTS_TAC
     [`w2w (^cond_bits w)`,
      `$FCP (K ^s_bit)`,
      `w2w (^imm8_bits w)`,
      `w2w (^rotate_imm_bits w)`,
      `w2w (^rd_bits w)`,
      `w2w (^rn_bits w)`,
      `w2w (^opcode_bits w)`]
  \\ blastLib.FULL_BBLAST_TAC)


(* We use define_compiler_exp to define the compiling function. *)

val data_imm_compiler_thm = define_compiler_exp "data_imm_compiler"
  ``if (w:word32) && ^mask = ^match then
      if ^cond_bits w = 15w then (* cond must not be 15w *)
        [MINI_ASSERT ASSERT_UNPREDICTABLE]
      else
        (* check for conditional execution *)
        (if ^cond_bits w = 14w then [] else [MINI_CONDITIONAL (w2w (^cond_bits w)) 4w])
        ++
        (* bump pc forward *)
        [MINI_REG_READ 3w 15w;
         MINI_ADD_IMM 3w 4w;
         MINI_REG_WRITE 15w 3w]
        ++
        (* perform core operation *)
        [MINI_REG_READ 0w (w2w (^rn_bits w))] ++
        (if ^rn_bits w = 15w then [MINI_ADD_IMM 0w 4w] else []) ++
        [MINI_IMM 1w (arm_immediate_rotate 8 w (^imm8_bits w))] ++
        (if ^opcode_bits w = 4w then
           [MINI_BINOP BINOP_ADD ^s_bit]
         else if ^opcode_bits w = 2w then
           [MINI_BINOP BINOP_SUB ^s_bit]
         else
           [MINI_ASSERT ASSERT_NOT_IMPLEMENTED]) ++
        [MINI_REG_WRITE (w2w (^rd_bits w)) 0w]
    else []``

(* Note that the resulting data_imm_compiler_thm is of the form:

     eval_compiler_exp w data_imm_compiler =
       if (w:word32) && ^mask = ^match then ... else ...

   The define_compiler_exp function generates a deep embedding which
   it defines to have the given name, in this case "add_imm_compiler".
   The deep embedding is defined so that it has exactly the semantics
   of the supplied term (w.r.t. eval_compiler_exp). In other words,
   the user need never deal with the verbose deep embedding
   directly. If you're curious, type

     fetch "-" "data_imm_compiler"

   to see the deep embedding. *)


(* Now let's attempt to prove that this complier is correct. *)

val select_lemma2 = blastLib.BBLAST_PROVE
  ``(^arm_data_imm_enc_tm >> 8 && 15w) = w2w rotate_imm``

val (CHEAT_TAC:tactic) = fn x => ([],fn t => mk_thm x);

val data_imm_compiler_correct = store_thm("data_imm_compiler_correct",
  ``COMP_CORRECT data_imm_compiler``,
  SIMP_TAC std_ss [COMP_CORRECT_def,data_imm_compiler_thm,Once LET_DEF]
  \\ STRIP_TAC \\ REVERSE (Cases_on `(instr:word32) && ^mask = ^match`)
  THEN1 (FULL_SIMP_TAC std_ss []) \\ FULL_SIMP_TAC std_ss [] \\ DISJ2_TAC
  \\ IMP_RES_TAC mask_lemma \\ ASM_REWRITE_TAC [select_lemma,w2w_lemma]
  \\ Cases_on `w2w cond = 15w:word32` \\ FULL_SIMP_TAC std_ss []
  THEN1 (FULL_SIMP_TAC std_ss [eval_mini_list_def,LET_DEF,eval_mini_def,check_assert_def])
  \\ ASM_SIMP_TAC std_ss [select_lemma2,arm_immediate_rotate_def]
  (* ... *)
  \\ CHEAT_TAC);


val _ = export_theory();
