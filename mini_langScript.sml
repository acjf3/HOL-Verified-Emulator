
open HolKernel Parse boolLib bossLib; val _ = new_theory "mini_lang";

open wordsTheory wordsLib armTheory armLib listTheory arithmeticTheory;

(* This file defines the MINI language -- a language which can execute
   ARM machine code and, at the same time, is simple enough to be
   just-in-time compiled to 64-bit x86 code. *)


(* The state of the MINI language runtime consists of an ARM state
   extended with four 32-bit registers and an ok boolean. If ok is
   false then the ARM state is not represented by the x86
   state. Convention: we will call the extra four registers A, B, C
   and D, although their official names in the formalisation are 0w,
   1w, 2w and 3w. *)

val _ = type_abbrev("mini_reg",``:word2``);
val _ = type_abbrev("mini_state",``:(mini_reg -> word32) # bool # arm_state``);


(* === abstract syntax === *)

val _ = Hol_datatype `
  BINOP = BINOP_ADD 
        | BINOP_SUB 
        | BINOP_OR 
        | BINOP_XOR 
        | BINOP_AND`;
        (* TST and CMP not needed, since AND and SUB suffice *)

val _ = Hol_datatype `
  ASSERT = ASSERT_NOT_IMPLEMENTED
         | ASSERT_UNPREDICTABLE
         | ASSERT_ALIGNED_HALF
         | ASSERT_ALIGNED_WORD`;

val _ = Hol_datatype `
  MINI_INSTRUCTION =

    (* execute NOP and skip to next MINI_MARKER, in case condition not met *)
      MINI_CONDITIONAL of word4
    | MINI_MARKER (* execution of this has no effect *)

    (* assertions *)
    | MINI_ASSERT of ASSERT

    (* moving values between mini regs *)
    | MINI_MOVE of word2 => word2
    | MINI_IMM of word2 => word32

    (* accessing ARM regsiters *)
    | MINI_REG_READ of word2 => word4
    | MINI_REG_WRITE of word4 => word2

    (* accessing ARM memory *)
    | MINI_MEM_BYTE_READ of word32    (* B := memory[A+imm32] *)
    | MINI_MEM_WORD_READ of word32    (* B := memory[A+imm32] *)
    | MINI_MEM_BYTE_WRITE of word32   (* memory[A+imm32] := B *)
    | MINI_MEM_WORD_WRITE of word32   (* memory[A+imm32] := B *)

    (* arithmetic/logic *)
    | MINI_BINOP of BINOP => bool (* "s-flag" as in adds vs add *)
   (* MINI_MONOPs not needed as NOT x is XOR x 0w and NEG r is SUB 0, r *)`;


val num2binop_def = Define `
  num2binop n =
    if n = 0 then BINOP_ADD else
    if n = 1 then BINOP_SUB else
    if n = 2 then BINOP_OR else
    if n = 3 then BINOP_XOR else
    if n = 4 then BINOP_AND else BINOP_ADD`;

val num2assert_def = Define `
  num2assert n = 
    if n = 0 then ASSERT_NOT_IMPLEMENTED else
    if n = 1 then ASSERT_UNPREDICTABLE else
    if n = 2 then ASSERT_ALIGNED_HALF else
    if n = 3 then ASSERT_ALIGNED_WORD else ASSERT_UNPREDICTABLE`;


(* === semantics === *)

val arm_condition_passed_def = Define `
  arm_condition_passed (cond:word4) (n,z,c,v) =
    let result =
      (case (3 >< 1) cond : word3
       of 0b000w => z                (* EQ or NE *)
        | 0b001w => c                (* CS or CC *)
        | 0b010w => n                (* MI or PL *)
        | 0b011w => v                (* VS or VC *)
        | 0b100w => c /\ ~z          (* HI or LS *)
        | 0b101w => n = v            (* GE or LT *)
        | 0b110w => (n = v) /\ ~z    (* GT or LE *)
        | 0b111w => T)               (* AL       *)
    in
     if cond ' 0 /\ (cond <> 15w) then
       ~result
     else
       result`;

val ARM_READ_MEM_WORD_def = Define `
  ARM_READ_MEM_WORD a s = 
    word32 [ARM_READ_MEM a s; ARM_READ_MEM (a+1w) s; 
            ARM_READ_MEM (a+2w) s; ARM_READ_MEM (a+3w) s]`;

val ARM_WRITE_MEM_WORD_def = Define `
  ARM_WRITE_MEM_WORD a w s = 
    let bs = bytes (w,4) in
      (ARM_WRITE_MEM a (EL 0 bs) o 
       ARM_WRITE_MEM (a+1w) (EL 1 bs) o
       ARM_WRITE_MEM (a+2w) (EL 2 bs) o
       ARM_WRITE_MEM (a+3w) (EL 3 bs)) s`;

val ARM_READ_NZCV_def = Define `
  ARM_READ_NZCV s = 
    let cpsr = ARM_READ_CPSR s in
      (cpsr.N,cpsr.Z,cpsr.C,cpsr.V)`;

val ARM_WRITE_NZCV_def = Define `
  ARM_WRITE_NZCV (n,z,c,v) s = 
    ARM_WRITE_CPSR 
      (ARM_READ_CPSR s with <| N := n; Z := z; C := c; V := v |>) s`;  

val eval_binop_def = Define `
  (eval_binop BINOP_ADD regs (n,z,c,v) = add_with_carry(regs 0w, regs 1w, F)) /\
  (eval_binop BINOP_SUB regs (n,z,c,v) = add_with_carry(regs 0w, ~regs 1w, T)) /\
  (eval_binop BINOP_OR  regs (n,z,c,v) = (regs 0w || regs 1w, c, v)) /\
  (eval_binop BINOP_XOR regs (n,z,c,v) = (regs 0w ?? (regs (1w:word2)):word32, c, v)) /\
  (eval_binop BINOP_AND regs (n:bool,z:bool,c:bool,v:bool) = (regs 0w && regs 1w, c, v))`;

val check_assert_def = Define `
  (check_assert ASSERT_UNPREDICTABLE (regs:mini_reg -> word32) = F) /\ 
  (check_assert ASSERT_NOT_IMPLEMENTED regs = F) /\ 
  (check_assert ASSERT_ALIGNED_WORD regs = aligned (regs 0w, 2)) /\ 
  (check_assert ASSERT_ALIGNED_HALF regs = aligned (regs 0w, 1))`;


(* We define an auxilliary function:

     eval_mini: MINI_INSTRUCTION -> mini_state -> jump # mini_state

   Here jump is a boolean indicating whether the execution should skip
   forward to the next MINI_MARKER. *)

val eval_mini_def = Define `

  (eval_mini (MINI_CONDITIONAL cond) (regs,ok,s) = 
     if arm_condition_passed cond (ARM_READ_NZCV s) then
       (F,regs,ok,s)
     else
       (T,regs,ok,ARM_WRITE_REG 15w (ARM_READ_REG 15w s + 4w) s)) /\
  (eval_mini (MINI_MARKER) (regs,ok,s) = (F,regs,ok,s)) /\ 

  (eval_mini (MINI_MOVE a b) (regs,ok,s) = 
     (F,(a =+ regs b) regs,ok,s)) /\
  (eval_mini (MINI_IMM a imm32) (regs,ok,s) = 
     (F,(a =+ imm32) regs,ok,s)) /\

  (eval_mini (MINI_REG_READ a r) (regs,ok,s) = 
     (F,(a =+ ARM_READ_REG r s) regs,ok,s)) /\
  (eval_mini (MINI_REG_WRITE r a) (regs,ok,s) = 
     (F,regs,ok,ARM_WRITE_REG r (regs a) s)) /\

  (eval_mini (MINI_MEM_BYTE_READ imm32) (regs,ok,s) = 
     (F,(1w =+ w2w (ARM_READ_MEM (regs 0w + imm32) s)) regs,ok,s)) /\
  (eval_mini (MINI_MEM_WORD_READ imm32) (regs,ok,s) = 
     (F,(1w =+ ARM_READ_MEM_WORD (regs 0w + imm32) s) regs,ok,s)) /\
  (eval_mini (MINI_MEM_BYTE_WRITE imm32) (regs,ok,s) = 
     (F,regs,ok,ARM_WRITE_MEM (regs 0w + imm32) (w2w (regs 1w)) s)) /\
  (eval_mini (MINI_MEM_WORD_WRITE imm32) (regs,ok,s) = 
     (F,regs,ok,ARM_WRITE_MEM_WORD (regs 0w + imm32) (regs 1w) s)) /\

  (eval_mini (MINI_ASSERT asrt) (regs,ok,s) = 
     (F,regs,ok /\ check_assert asrt regs,s)) /\

  (eval_mini (MINI_BINOP binop s_flag) (regs,ok,s) =
     let (res,c,v) = eval_binop binop regs (ARM_READ_NZCV s) in 
       (F,(0w =+ res) regs,ok,
        if s_flag then ARM_WRITE_NZCV (word_msb res,res = 0w,c,v) s else s))`;


(* The effect of executing a list of MINI instructions. *)

val DROP_UNTIL_def = Define `
  (DROP_UNTIL p [] = []) /\
  (DROP_UNTIL p (x::xs) = if p x then x::xs else DROP_UNTIL p xs)`;

val LENGTH_DROP_UNTIL = prove( 
  ``!xs. LENGTH (DROP_UNTIL P xs) <= LENGTH xs``,
  Induct THEN SRW_TAC [] [DROP_UNTIL_def] THEN DECIDE_TAC);

val eval_mini_list_def = tDefine "eval_mini_list" `
  (eval_mini_list [] s = s) /\
  (eval_mini_list (x::xs) s = 
     let (stop,t) = eval_mini x s in
       if stop then eval_mini_list (DROP_UNTIL (\x. x = MINI_MARKER) xs) t 
               else eval_mini_list xs t)`
 (WF_REL_TAC `measure (LENGTH o FST)` 
  THEN SIMP_TAC std_ss [LENGTH] THEN REPEAT STRIP_TAC
  THEN MATCH_MP_TAC LESS_EQ_LESS_TRANS THEN Q.EXISTS_TAC `LENGTH xs`
  THEN ASM_SIMP_TAC std_ss [LENGTH_DROP_UNTIL]);

  
val _ = export_theory();

