(* Just a simple script to test a zeroExtendion circuit *)
(* Will top4isT=T if the top 4 bits of the word8 input are Ts*)
   
open hardwarePreamble;

open translatorTheory translatorCoreLib;
(* val _ = new_theory "zeroExtendExampleCircuit"; *)

val _ = prefer_num ();

Datatype:
  state = <| out : word8|>
End

Datatype:
  ext_state = <| inp : word4 |>
End

Definition zeroExtendExample_comb_def:
  zeroExtendExample_comb (fext:ext_state) (s:state) (s':state) =
  s' with out := w2w (fext.inp):word8
End

val init_tm = add_x_inits “<| out := 0w:word8 |>”;

Definition zeroExtendExample_init_def:
  zeroExtendExample_init (fbits : num -> bool) = ^init_tm
End

Definition zeroExtendExample_def:
  zeroExtendExample = mk_module (procs []) (procs [zeroExtendExample_comb]) zeroExtendExample_init
End

(* TODO: proofs *)
    
(* val _ = export_theory(); *)

(* TODO put in separate file *)
open translatorLib;
open compileLib;
val trans_thm = module2hardware zeroExtendExample_def ["out"] []; (* works *)
val (circuit, circuit_correct) = compile (definition "zeroExtendExample_v_def") (* fails *)

                                         (*Testing compiler ...*)

(* val module_def = definition "zeroExtendExample_v_def"; *)

                                          
