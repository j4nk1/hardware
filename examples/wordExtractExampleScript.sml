(* Just a simple script to test a wordExtraction circuit *)
(* Will top4isT=T if the top 4 bits of the word8 input are Ts*)
   
open hardwarePreamble;

open translatorTheory translatorCoreLib;
val _ = new_theory "wordExtractExampleCircuit";

val _ = prefer_num ();

Datatype:
  state = <| top4isT : bool |>
End

Datatype:
  ext_state = <| inp : word8 |>
End

(* turn on word length guessing so we don't have to manually specify *)
(* wordsLib.guessing_word_lengths:=true; *)
    
(* Definition wordExtractExample_comb_def: *)
(*   wordExtractExample_comb (fext:ext_state) (s:state) (s':state) = *)
(*   if (((7 >< 4) fext.inp = 15w : word4)) then *)
(*     s' with top4isT := T *)
(*   else *)
(*     s' with top4isT := F *)
(* End *)

Definition wordExtractExample_comb_def:
  wordExtractExample_comb (fext:ext_state) (s:state) (s':state) =
  if ((7 >< 4) fext.inp = (15w : word4)) then
    s' with top4isT := T
  else
    s' with top4isT := F
End

val init_tm = add_x_inits “<| top4isT := F |>”;

Definition wordExtractExample_init_def:
  wordExtractExample_init (fbits : num -> bool) = ^init_tm
End

Definition wordExtractExample_def:
  wordExtractExample = mk_module (procs [wordExtractExample_comb]) (procs []) wordExtractExample_init
End

(* TODO: proofs *)
    
val _ = export_theory();

(* TODO put in separate file *)
open translatorLib;
open compileLib;
val trans_thm = module2hardware wordExtractExample_def ["inp"] ["top4isT"]; (* works *)
val (circuit, circuit_correct) = compile (definition "wordExtractExample_v_def") (* fails *)

                                         (*Testing compiler ...*)

(* val module_def = definition "wordExtractExample_v_def"; *)

                                          
