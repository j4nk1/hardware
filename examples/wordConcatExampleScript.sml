open hardwarePreamble;

open translatorTheory translatorCoreLib;
(* val _ = new_theory "wordExtractExampleCircuit"; *)

val _ = prefer_num ();

Datatype:
  state = <| out : word8 |>
End

Datatype:
  ext_state = <| inp : word4 |>
End

(* turn on word length guessing so we don't have to manually specify *)
(* wordsLib.guessing_word_lengths:=true; *)

Definition wordConcatExample_comb_def:
  wordConcatExample_comb (fext:ext_state) (s:state) (s':state) = s' with out := ((fext.inp @@ (0w : word4)) : word8)
End

val init_tm = add_x_inits “<| out := 0w : word8 |>”;

Definition wordConcatExample_init_def:
  wordConcatExample_init (fbits : num -> bool) = ^init_tm
End

Definition wordConcatExample_def:
  wordConcatExample = mk_module (procs []) (procs [wordConcatExample_comb]) wordConcatExample_init
End

(* TODO: proofs *)
    
(* val _ = export_theory(); *)

(* TODO put in separate file *)
open translatorLib;
open compileLib;
val trans_thm = module2hardware wordConcatExample_def ["inp"] ["out"]; (* works *)
val (circuit, circuit_correct) = compile (definition "wordConcatExample_v_def") (* fails *)
