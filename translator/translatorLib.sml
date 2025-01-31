structure translatorLib =
struct

open hardwarePreamble;

open verilogTheory;

open translatorTheory;
open translatorCoreLib translatorExpLib translatorStmLib;

(* Test:
open avgCircuitTheory;
val module_def = avg_def;
val outputs = ["avg"];
val comms = ["h0", "h1", "h2", "h3"];

open pulseCounterCircuitTheory;
val module_def = pcounter_def;
val outputs = ["done"];
val comms = ["count"];

val tm = “s' with done := T”

val s = “s:state”
val s' = “s':state”
*)

fun build_state_rel_var comms (field, field_data : TypeBase.rcd_fieldinfo) = let
 val fieldHOL = fromMLstring field
 val accessf = #accessor field_data
 val pred = accessf |> type_of |> dom_rng |> snd |> predicate_for_type
in
 if mem field comms then
  ``state_rel_cvar hol_s hol_s' ver_s ^fieldHOL ^pred ^accessf``
 else
  ``state_rel_var hol_s' ver_s ^fieldHOL ^pred ^accessf``
end;

fun build_module_state_rel_var (field, field_data : TypeBase.rcd_fieldinfo) = let
 val fieldHOL = fromMLstring field
 val accessf = #accessor field_data
 val pred = accessf |> type_of |> dom_rng |> snd |> predicate_for_type
in
  ``module_state_rel_var hol_s ver_s ^fieldHOL ^pred ^accessf``
end;

fun build_fextv_var (field, field_data : TypeBase.rcd_fieldinfo) = let
 val fieldHOL = fromMLstring field
 val accessf = #accessor field_data
 val pred = accessf |> dest_const |> snd |> dom_rng |> snd |> hol2ver_for_type
in
 ``fextv ^fieldHOL = INR (^pred (^accessf fext))``
end;

fun build_fextv_others vars = let
 val vars = pred_setSyntax.mk_set vars
 val tm = ``!var. var ∉ ^vars ⇒ fextv var = INL UnknownVariable``
in
 inst [ alpha |-> value_ty ] tm
end;

fun get_def theory tm = let
 val name = tm |> dest_const |> fst
in
 case total (fetch theory) (name ^ "_trans") of
    NONE => fetch theory (name ^ "_def")
  | SOME def => def
end;

fun procs2hardware tstate theory procs = let
 val procs = procs |> dest_comb |> snd |> listSyntax.dest_list |> fst |> rev
 val trans = map (step2hardware tstate o get_def theory) procs
in
 case trans of
  [] => ISPECL [#fext_rel tstate, #rel tstate] Eval_list_nil
  | [t] => MATCH_MP Eval_Eval_list_base t
  | t::ts => foldr (fn (t, th) => MATCH_MP Eval_Eval_list_step (CONJ t th))
                   (MATCH_MP Eval_Eval_list_base t)
                   ts
end;

fun build_fextty (field, field_data : TypeBase.rcd_fieldinfo) =
 pairSyntax.mk_pair(fromMLstring field, field_data |> #ty |> verty_for_type);

fun build_decl outputs oracle (field, v) = let
 fun lift_option_value opt =
  case opt of
    NONE => optionSyntax.mk_none value_ty
  | SOME v => optionSyntax.mk_some v

 val ty = type_of v
 val v' = if free_in oracle v then
           optionSyntax.mk_none value_ty
          else
           optionSyntax.mk_some (mk_comb(hol2ver_for_type ty, v))
 (*val v_opt = lookup_opt field init_values
             |> Option.map (fn v => mk_comb(hol2ver_for_type ty, v))
             |> lift_option_value*)

 val decl = TypeBase.mk_record (“:var_metadata”, [("output", if mem field outputs then T else F),
                                                  ("type", verty_for_type ty),
                                                  ("init", v')])
 val decl = pairSyntax.mk_pair(fromMLstring field, decl)
in
 decl
end;

(* Too simple but works for now... *)
fun build_module_rel_init module_rel init decls =
	prove(“^module_rel ^init (SND (run_decls fbits ^decls []))”, EVAL_TAC \\ simp []);

(* Expected input format: name = mk_cirucit (procs seqs) (procs combs) init *)
fun module2hardware module_def outputs comms = let
 val (module, def) = module_def |> concl |> dest_eq
 val module_name = module |> dest_const |> fst

 fun new_module_definition name tm = let
  val name = concat $ module_name :: (if name = "" then ["_v"] else ["_v_", name])
  val def = new_definition(name ^ "_def", mk_icomb(mk_comb(equality, mk_var(name, alpha)), tm))
  val _ = computeLib.add_funs [def]
 in
  def
 end

 val theory = module |> dest_thy_const |> #Thy
 val state_ty = module |> dest_const |> snd |> dom_rng |> snd |> dom_rng |> snd |> dom_rng |> snd
 val fext_ty = module |> dest_const |> snd |> dom_rng |> fst |> dom_rng |> snd

 (* Build tstate... *)

 (* TODO: Name... *)
 val state_rel_def =
 TypeBase.fields_of state_ty
 |> map (build_state_rel_var comms)
 |> list_mk_conj
 |> (fn tm => Define `state_rel (hol_s:^(ty_antiq state_ty)) (hol_s':^(ty_antiq state_ty)) ver_s = ^tm`);

 (* TODO: Name... *)
 val module_state_rel_def =
 TypeBase.fields_of state_ty
 |> map (build_module_state_rel_var)
 |> list_mk_conj
 |> (fn tm => Define `module_state_rel hol_s ver_s = ^tm`);

 val fextv_vars =
 TypeBase.fields_of fext_ty
 |> map build_fextv_var;

 (* This was needed for Silver at some point to hide fext lifting from theorems,
    would have otherwise not have been needed. *)
 val fextv_others =
 TypeBase.fields_of fext_ty
 |> map (fromMLstring o fst)
 |> build_fextv_others;

 (* TODO: Name... *)
 val fextv_rel_def =
 fextv_vars @ [fextv_others]
 |> list_mk_conj
 |> inst [ alpha |-> ``:error`` ]
 |> (fn tm => Define `fextv_rel fextv fext = ^tm`);

 val tstate = build_tstate fextv_rel_def state_rel_def module_state_rel_def comms fext_ty state_ty

 (* Build the Verilog module... *)

 val (_, [seqs, combs, init]) = strip_comb def
 val seqs = procs2hardware tstate theory seqs |> GEN_ALL
 val seqs_v_def = new_module_definition "seqs" (seqs |> concl |> strip_forall |> snd |> rand)
 val seqs = REWRITE_RULE [GSYM seqs_v_def] seqs

 val combs = procs2hardware tstate theory combs |> GEN_ALL
 val combs_v_def = new_module_definition "combs" (combs |> concl |> strip_forall |> snd |> rand)
 val combs = REWRITE_RULE [GSYM combs_v_def] combs

 val th = MATCH_MP Eval_lists_mrun (LIST_CONJ [seqs, combs, #module_rel_rel tstate, #rel_module_rel tstate])
 val precond = th |> concl |> strip_forall |> snd |> dest_imp |> fst |> EVAL_PROVE
 val th = MATCH_MP th precond

 val fextty_tm = TypeBase.fields_of fext_ty
                 |> map build_fextty
                 |> (fn l => listSyntax.mk_list (l, “:string # vertype”))

 val init_def = get_def theory init
 val (init, init_values) = init_def |> concl |> strip_forall |> snd |> dest_eq
 val init_values = init_values |> TypeBase.dest_record |> snd

 (* Hack for now: *)
 val expected_oracle = “fbits : num -> bool”
 val decls_tm = map (build_decl outputs expected_oracle) init_values
                |> (fn l => listSyntax.mk_list (l, “:string # var_metadata”))
 val decls_def = new_module_definition "decls" decls_tm

 val precond = build_module_rel_init (#module_rel tstate) init (decls_def |> concl |> lhs)
 val th = MATCH_MP th precond

 val module_tm = TypeBase.mk_record (“:module”, [("fextty", fextty_tm),
                                                 ("decls", decls_def |> concl |> lhs),
                                                 ("ffs", seqs_v_def |> concl |> lhs),
                                                 ("combs", combs_v_def |> concl |> lhs)])
 val module_v_def = new_module_definition "" module_tm

 val th = MATCH_MP mk_circuit_to_mk_module (th |> SPEC_ALL |> UNDISCH_ALL |> GEN_ALL)
 val th = SPEC (module_v_def |> concl |> lhs) th
 val th = EVAL_MP th
 val th = th |> DISCH_ALL |> GEN_ALL
 val th = PURE_REWRITE_RULE [GSYM module_def] th
in
 th
end;

end
