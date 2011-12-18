structure comp_langLib :> comp_langLib =
struct

open HolKernel boolLib bossLib;
open wordsSyntax wordsTheory wordsLib arithmeticTheory listTheory combinTheory;
open mini_langTheory comp_langTheory;

infix $$
val op $$ = mk_comb

fun good_imm w =
  if type_of w = ``:word32`` andalso wordsSyntax.is_n2w w andalso
    numSyntax.is_numeral (rand w) then w
  else failwith("Bad immediate constant: " ^ term_to_string w)

fun good_index n =
  if numSyntax.is_numeral n andalso numSyntax.int_of_term n < 32 then n
   else failwith("Bad bit index constant: " ^ term_to_string n)

fun at_most_one_word32_free tm = let
  val vs = free_vars tm
  in (length (filter (fn v => type_of v <> ``:word32``) vs) = 0
     andalso length vs < 2) end;

fun binop1 tm = tm |> rator |> rand
fun binop2 tm = tm |> rand

local
  val word_instruction = ``WORD_INSTRUCTION``
  fun word_imm w = ``WORD_IMM`` $$ good_imm w
  fun word_lsl e n = ``WORD_LSL`` $$ e $$ good_index n
  fun word_lsr e n = ``WORD_LSR`` $$ e $$ good_index n
  fun word_and e w = ``WORD_AND`` $$ e $$ good_imm w
  fun word_or e w = ``WORD_OR`` $$ e $$ good_imm w
  fun word_bits e i j = ``WORD_BITS`` $$ e $$ good_index i $$ good_index j
  fun word_sign_extend e i = ``WORD_SIGN_EXTEND`` $$ e $$ good_index i
  fun word_rotate e i = ``WORD_ROTATE`` $$ e $$ good_index i
  val bits_pattern1 = ``w || (m -- n) (v:word32)``
  val bits_pattern2 = ``(m -- n) (v:word32)``
  val sign_extend_pattern = ``sign_extend n (w:word32)``
  fun is_sign_extend tm = can (match_term sign_extend_pattern) tm
  val rotate_pattern = ``arm_immediate_rotate n w e``
  fun is_rotate tm = can (match_term rotate_pattern) tm
  fun mk_word_fail tm = failwith("WORD_EXP conversion failed: " ^ term_to_string tm)
  fun aux tm =
    if is_var tm andalso type_of tm = ``:word32`` then word_instruction else
    if is_n2w tm then word_imm tm else
    if is_word_lsr tm then word_lsr (aux (binop1 tm)) (binop2 tm) else
    if is_word_lsl tm then word_lsl (aux (binop1 tm)) (binop2 tm) else
    if can (match_term bits_pattern1) tm then
      word_bits (aux (binop1 tm))
                (tm |> binop2 |> rator |> binop1)
                (tm |> binop2 |> rator |> binop2) else
    if can (match_term bits_pattern2) tm then
      word_bits (word_imm ``0w:word32``)
                (tm |> rator |> binop1)
                (tm |> rator |> binop2) else
    if is_word_and tm then word_and (aux (binop1 tm)) (binop2 tm) else
    if is_word_or tm then word_or (aux (binop1 tm)) (binop2 tm) else
    if is_rotate tm then
      word_rotate (aux (binop2 tm)) (binop1 (tm |> rator)) else
    if is_sign_extend tm then
      word_sign_extend (aux (binop2 tm)) (binop1 tm)
    else mk_word_fail tm
in
  fun mk_word_exp tm =
    if at_most_one_word32_free tm then aux tm else mk_word_fail tm
end;

local
  val word_select_0_pattern = ``(w:word32) ' 0``
  val word_select_pattern = ``(w:word32) ' n``
  val silly_w2w_pattern = ``(w2w:word32->word32) w``
  fun binop1 tm = tm |> rator |> rand
  fun binop2 tm = tm |> rand
  fun arg2exp_fail tm = failwith("Unable to translate: " ^ term_to_string tm)
  fun arg2exp tm =
    if is_n2w tm then
      ``WORD_IMM`` $$ (mk_n2w(fst (dest_n2w tm),``:32``)) else
    if can (match_term silly_w2w_pattern) tm then arg2exp (rand tm) else
    if type_of tm = ``:word32`` then mk_word_exp tm else
    if tm = ``F`` then ``WORD_IMM 0w`` else
    if tm = ``T`` then ``WORD_IMM 1w`` else
    if can (match_term word_select_0_pattern) tm then mk_word_exp (binop1 tm) else
    if can (match_term word_select_pattern) tm then
      ``WORD_LSR`` $$ (mk_word_exp (binop1 tm)) $$ good_index (binop2 tm) else
    if is_w2w tm then mk_word_exp (rand tm) else let
      val n = REWRITE_CONV [GSYM num2binop_thm, GSYM num2assert_thm] tm
              |> concl |> rand |> rand
      val _ = numSyntax.is_numeral n orelse fail()
      in ``WORD_IMM`` $$ (mk_n2w(n,``:32``)) end
      handle UNCHANGED => arg2exp_fail tm
  fun get_args tm = if not (is_comb tm) then [] else
                      get_args (rator tm) @ [arg2exp (rand tm)]
  fun mk_fun_ty [] ty = ty
    | mk_fun_ty (x::xs) ty = mk_type("fun",[x,mk_fun_ty xs ty])
in
  fun mk_emit_exp tm = let
    val base = tm |> repeat rator |> dest_const
    val base_name = base |> fst |> explode |> tl |> tl |> tl |> tl |> implode
    val emit_name = "EMIT" ^ base_name
    val args = get_args tm
    val ty = mk_fun_ty (map type_of args) ``:EMIT_EXP``
    val res = mk_const(emit_name,ty)
    in foldl (fn (x,y) => y $$ x) res args end
end;

local
  fun aux tm =
    if tm = ``[]:MINI_INSTRUCTION list`` then ``COMPILER_SKIP`` else
    if listSyntax.is_cons tm then let
      val (x,y) = listSyntax.dest_cons tm
      val x1 = mk_emit_exp x
      val y1 = aux y
      val emit = ``COMPILER_EMIT`` $$ x1
      in if y1 = ``COMPILER_SKIP`` then emit else
           ``COMPILER_SEQ`` $$ emit $$ y1 end else
    if listSyntax.is_append tm then
      ``COMPILER_SEQ`` $$ aux (binop1 tm) $$ aux (binop2 tm) else
    if is_cond tm then let
      val (x1,x2,x3) = dest_cond tm
      val (x1,y1) = dest_eq x1
      in ``COMPILER_IF`` $$ mk_word_exp x1 $$ good_imm y1 $$
           aux x2 $$ aux x3 end else fail()
in
  fun mk_compiler_exp tm =
    aux (tm |> QCONV (SIMP_CONV std_ss [APPEND,word_extract_def,o_DEF]) |> concl |> rand)
end;

val LSR_SELECT_0 = prove(
  ``!(w:word32) n. n < 32 ==> ((w >>> n) ' 0 = w ' n)``,
  SIMP_TAC (std_ss++SIZES_ss) [word_lsr_def,fcpTheory.FCP_BETA]);

val CONST_SELECT_LEMMA =
  LIST_CONJ [EVAL ``(1w:word32) ' 0``,EVAL ``(0w:word32) ' 0``]

fun define_compiler_exp name tm = let
  val _ = at_most_one_word32_free tm orelse failwith("Only one word32 var allowed.")
  val compiler_exp = mk_compiler_exp tm
  val def = new_definition(name,mk_eq(mk_var(name,``:COMPILER_EXP``),compiler_exp))
  val c = def |> GSYM |> concl |> rand
  val v = hd (free_vars tm @ [mk_var("instr",``:word32``)])
  val t = ``eval_compiler_exp`` $$ v $$ c
  val goal = mk_eq(t,tm)
  val lemma = prove(goal,
    SIMP_TAC (std_ss++SIZES_ss) [def,eval_compiler_exp_def,eval_emit_exp_def,
      eval_word_exp_def,e2w_def,e2n_def,e2b_def,num2assert_thm,w2n_n2w,
      num2binop_thm,LSR_SELECT_0,APPEND,w2w_id,WORD_OR_CLAUSES,w2w_n2w,
      word_extract_def,o_DEF,CONST_SELECT_LEMMA])
  in lemma end;

end;
