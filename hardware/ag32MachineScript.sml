open hardwarePreamble;

val _ = new_theory "ag32Machine";

prefer_num ();
guess_lengths ();

val _ = Datatype `
 state_circuit = <| (** Cpu **)
                state : word3;

                PC : word32;
                R : word6 -> word32;

                CarryFlag : bool;
                OverflowFlag : bool;

                (* Decoding and related *)
                i : word32; (* Latest instruction fetched from inst mem *)
                instruction : word6; (* Decoded instruction op code *)

                ALU_res : word32;

                delay_write : word6;
                do_delay_write : word3;

                data_out : word10; (* LEDs: 3 + 3 + 1 + 1 + 1 + 1 *)
                data_in : word2;

                acc_arg : word32;
                acc_arg_ready : bool;

                mem_start : word32;
                interrupt_req : bool;
                do_interrupt : bool;

                (* Data mem *)
                command : word3;
                data_addr : word32;
                data_wdata : word32;
                data_wstrb : word4;

                (** Acc **)
                (* Cpu interface *)
                acc_res_ready : bool;
                acc_res : word32;

                (* Internal state *)
                acc_state : word2
              |>`;

val _ = Datatype `
 interrupt_state = InterruptReady | InterruptWorking | InterruptAck`;

(* External inputs, and model of relevant part of world (i.e., contents of memory) *)
val _ = Datatype `
 ext = <| (* in state_circuit for now, but "should" be here...
             but we do not have ext in specification generated by L3: *)
          (*data_in : word32;*)

          (* Memory *)
          mem : word32 -> word8;
          error : word2;
          ready : bool;
          data_rdata : word32;
          inst_rdata : word32;

          (* Start of mem *)
          mem_start_ready : bool;
          mem_start_input : word32;

          (* Interrupt *)
          interrupt_state : interrupt_state;
          interrupt_ack : bool;
          io_events : (word32 -> word8) list
        |>`;

(** Memory specification **)

val mem_update_def = Define `
 mem_update mem addr wdata wstrb =
  let mem = if word_bit 0 wstrb then (addr      =+ ((7 >< 0) wdata)) mem else mem;
      mem = if word_bit 1 wstrb then (addr + 1w =+ ((15 >< 8) wdata)) mem else mem;
      mem = if word_bit 2 wstrb then (addr + 2w =+ ((23 >< 16) wdata)) mem else mem in
            if word_bit 3 wstrb then (addr + 3w =+ ((31 >< 24) wdata)) mem else mem`;

(* TODO: Consider using alignmentTheory instead *)
val align_addr_def = Define `
 align_addr (addr:word32) = ((31 >< 2) addr @@ (0w:word2)):word32`;

(* TODO: Move up to separate theory? *)
val _ = Datatype `
 fext_accessor = <|
  get_command : 'a -> word3;
  get_PC : 'a -> word32;
  get_data_addr : 'a -> word32;
  get_data_wdata : 'a -> word32;
  get_data_wstrb : 'a -> word4;

  get_interrupt_req : 'a -> bool
  |>`;

val fext_accessor_circuit_def = Define `
 fext_accessor_circuit =
  <| get_command := state_circuit_command;
     get_PC := state_circuit_PC;
     get_data_addr := state_circuit_data_addr;
     get_data_wdata := state_circuit_data_wdata;
     get_data_wstrb := state_circuit_data_wstrb;

     get_interrupt_req := state_circuit_interrupt_req |>`;

val word_at_addr_def = Define `
 word_at_addr (mem : word32 -> word8) addr =
  (mem (addr + 3w) @@ (mem (addr + 2w) @@ (mem (addr + 1w) @@ mem addr):word16):word24):word32`;

(* TODO: Should maybe add that errors are not allowed to occur, i.e. non-error implies this ... *)
(* TODO: Would make more sense to have alignment preconds, rather than doing alignment "automatically" *)
val is_mem_def = Define `
 is_mem accessors step fext =
  !n.
  (* Mem data semantics *)

  (* Nothing *)
  (accessors.get_command (step n) = 0w /\ (fext n).ready ==>
   (fext (SUC n)).mem = (fext n).mem /\
   (fext (SUC n)).ready = (fext n).ready) /\

  (* Read instruction *)
  (accessors.get_command (step n) = 1w /\ (fext n).ready ==>
   ?m. (!p. p < m ==> (fext (SUC (n + p))).mem = (fext n).mem /\ ~(fext (SUC (n + p))).ready) /\
       (fext (SUC (n + m))).mem = (fext n).mem /\
       (fext (SUC (n + m))).inst_rdata = word_at_addr (fext n).mem (align_addr (accessors.get_PC (step n))) /\
       (fext (SUC (n + m))).ready) /\

  (* Read instruction + read data *)
  (accessors.get_command (step n) = 2w /\ (fext n).ready ==>
    ?m. (!p. p < m ==> (fext (SUC (n + p))).mem = (fext n).mem /\ ~(fext (SUC (n + p))).ready) /\
        (fext (SUC (n + m))).mem = (fext n).mem /\
        (fext (SUC (n + m))).data_rdata = word_at_addr (fext n).mem (align_addr (accessors.get_data_addr (step n))) /\
        (fext (SUC (n + m))).inst_rdata = word_at_addr (fext n).mem (align_addr (accessors.get_PC (step n))) /\
        (fext (SUC (n + m))).ready) /\

  (* Read instruction + write data, note that the current unverified cache layer do not allow inst read addr and
                                    data write addr to be the same... *)
  (accessors.get_command (step n) = 3w /\ (fext n).ready ==>
    ?m. (!p. p < m ==> (fext (SUC (n + p))).mem = (fext n).mem /\ ~(fext (SUC (n + p))).ready) /\
        (let newmem = mem_update (fext n).mem (align_addr (accessors.get_data_addr (step n))) (accessors.get_data_wdata (step n)) (accessors.get_data_wstrb (step n)) in
         (fext (SUC (n + m))).mem = newmem /\
         (fext (SUC (n + m))).inst_rdata = word_at_addr newmem (align_addr (accessors.get_PC (step n))) /\
         (fext (SUC (n + m))).ready)) /\

 (* Clear cache block used for printing ... exactly the same semantics as "read instruction" *)
 (accessors.get_command (step n) = 4w /\ (fext n).ready ==>
   ?m. (!p. p < m ==> (fext (SUC (n + p))).mem = (fext n).mem /\ ~(fext (SUC (n + p))).ready) /\
       (fext (SUC (n + m))).mem = (fext n).mem /\
       (fext (SUC (n + m))).inst_rdata = word_at_addr (fext n).mem (align_addr (accessors.get_PC (step n))) /\
       (fext (SUC (n + m))).ready)`;

(** Accelerator specification **)

val is_acc_def = Define `
 is_acc f circuit =
  ?k. !n.
   (circuit n).acc_arg_ready
   ==>
   (k <> 0 ==> ~(circuit (SUC n)).acc_res_ready) /\
   (!l. l < k /\ (!m. m <> 0 /\ m <= l ==> ~(circuit (n + m)).acc_arg_ready) ==>
        ~(circuit (SUC (n + l))).acc_res_ready) /\
   ((!m. m < k ==> ~(circuit (SUC (n + m))).acc_arg_ready /\ (circuit (SUC (n + m))).acc_arg = (circuit n).acc_arg) ==>
    (circuit (SUC (n + k))).acc_res_ready /\
    ((circuit (SUC (n + k))).acc_res = f (circuit n).acc_arg))`;

(** Start of mem interface **)

val is_mem_start_interface_def = Define `
 is_mem_start_interface fext mem_start =
  ?n. (!m. m < n ==> ~(fext m).mem_start_ready) /\ (fext n).mem_start_ready /\ (fext n).mem_start_input = mem_start`;

(** Interrupt interface **)

(* This is a little difficult to model properly because the interrupt interface is async. *)
val is_interrupt_interface_def = Define `
 is_interrupt_interface accessors step fext =
  ((fext 0).io_events = [] /\
  (fext 0).interrupt_state = InterruptReady /\
  !n. case (fext n).interrupt_state of
         InterruptReady =>
          if accessors.get_interrupt_req (step n) then
           ?m. (!p. p < m ==> ~(fext (SUC (n + p))).interrupt_ack) /\
               (fext (SUC (n + m))).interrupt_state = InterruptAck /\
               (* This assumes that memory is not changed during interrupts,
                  this assumption could be added as a precondition. *)
               (fext (SUC (n + m))).io_events = SNOC (fext n).mem (fext n).io_events /\
               (fext (SUC (n + m))).interrupt_ack
          else
           (fext (SUC n)).interrupt_state = InterruptReady /\
           (fext (SUC n)).io_events = (fext n).io_events /\
           ~(fext (SUC n)).interrupt_ack
       | InterruptWorking => T
       | InterruptAck =>
         (fext (SUC n)).interrupt_state = InterruptReady /\
         (fext (SUC n)).io_events = (fext n).io_events /\
         ~(fext (SUC n)).interrupt_ack)`;

(** Cpu implementation **)

val decode_instruction_def = Define `
 decode_instruction s =
  if word_bit 24 s.i then
    if word_bit 31 s.i then s with instruction := 13w
    else if (23 >< 9) s.i = 0w then s with instruction := 14w
    else s with instruction := 15w
  else if (5 >< 0) s.i = 10w \/ (5 >< 0) s.i = 11w \/ (5 >< 0) s.i = 12w then
    s with instruction := (5 >< 0) s.i
  else if word_bit 31 s.i then
    s with instruction := 15w
  else if (5 >< 0) s.i <+ 10w then
    s with instruction := (5 >< 0) s.i
  else
    s with instruction := 15w`;

(* sw2sw around R is needed to be able to extract to Verilog *)
val DecodeReg_imm_def = Define `
 DecodeReg_imm (flag, v) s = (if flag then sw2sw v else sw2sw (s.R v)):word32`;

val ALU_def = Define `
 ALU ((func:word4), ALU_fst, ALU_snd) s =
  (let ALU_sum = (w2w ALU_fst + w2w ALU_snd + (if func = 1w then v2w [s.CarryFlag] else 0w)):33 word;
       ALU_prod = (w2w ALU_fst * w2w ALU_snd):word64 in
     case func of
      0w => s with <|OverflowFlag := ((word_bit 31 ALU_fst = word_bit 31 ALU_snd) /\
                                      (word_bit 31 ALU_sum <> word_bit 31 ALU_fst));
                     CarryFlag := word_bit 32 ALU_sum;
                     ALU_res := (31 >< 0) ALU_sum|>
    | 1w => s with <|CarryFlag := word_bit 32 ALU_sum;
                     ALU_res := (31 >< 0) ALU_sum|>
    | 2w => (let
              (* TODO: Can reuse ALU_sum here... *)
              ALU_sub = ALU_fst − ALU_snd
            in
              s with <|ALU_res := ALU_sub;
                       OverflowFlag := ((word_bit 31 ALU_fst <> word_bit 31 ALU_snd) /\
                                       (word_bit 31 ALU_sub <> word_bit 31 ALU_fst))|>)
    | 3w => s with ALU_res := v2w [s.CarryFlag]
    | 4w => s with ALU_res := v2w [s.OverflowFlag]
    | 5w => s with ALU_res := ALU_fst + 1w
    | 6w => s with ALU_res := ALU_fst − 1w
    | 7w => s with ALU_res := (31 >< 0) ALU_prod
    | 8w => s with ALU_res := (63 >< 32) ALU_prod
    | 9w => s with ALU_res := (ALU_fst && ALU_snd)
    | 10w => s with ALU_res := (ALU_fst ‖ ALU_snd)
    | 11w => s with ALU_res := (ALU_fst ⊕ ALU_snd)
    | 12w => s with ALU_res := v2w [ALU_fst = ALU_snd]
    | 13w => s with ALU_res := v2w [ALU_fst < ALU_snd]
    | 14w => s with ALU_res := v2w [ALU_fst <₊ ALU_snd]
    | 15w => s with ALU_res := ALU_snd)`;

val shift_def = Define `
 shift (shiftOp:word2) w a b s =
  case shiftOp of
     0w => s with R := (w =+ a <<~ b) s.R
   | 1w => s with R := (w =+ a >>>~ b) s.R
   | 2w => s with R := (w =+ a >>~ b) s.R
   | 3w => let shift_sh = word_mod b 32w in
            s with R := (w =+ (a >>>~ shift_sh || a <<~ (32w - shift_sh))) s.R`;

val execute_instruction_def = Define `
 execute_instruction wV aV bV PC_next fext s =
  case s.instruction of
    (* Normal *)
    0w => s with <|state := 1w; command := 1w; PC := PC_next;
                   R := ((30 >< 25) s.i =+ s.ALU_res) s.R|>

    (* Shift *)
  | 1w => let s = shift ((7 >< 6) s.i) ((30 >< 25) s.i) aV bV s in
          s with <|state := 1w; command := 1w; PC := PC_next|>

    (* StoreMEM *)
  | 2w => s with <|state := 1w; command := 3w; PC := PC_next;
                   data_addr := bV; data_wdata := aV; data_wstrb := 15w|>

    (* StoreMEMByte *)
    (* TODO: Can reuse shifter here? *)
  | 3w => (let s = s with <|state := 1w; command := 3w; PC := PC_next;
                            data_addr := bV; data_wstrb := 1w <<~ w2w ((1 >< 0) bV)|> in
             (case (1 >< 0) bV of
               0w => s with data_wdata := bit_field_insert 7 0 ((7 >< 0) aV) s.data_wdata
             | 1w => s with data_wdata := bit_field_insert 15 8 ((7 >< 0) aV) s.data_wdata
             | 2w => s with data_wdata := bit_field_insert 23 16 ((7 >< 0) aV) s.data_wdata
             | 3w => s with data_wdata := bit_field_insert 31 24 ((7 >< 0) aV) s.data_wdata))

    (* LoadMEM *)
  | 4w => s with <|state := 1w; command := 2w; PC := PC_next;
                   data_addr := aV; do_delay_write := 4w; delay_write := (30 >< 25) s.i|>

    (* LoadMEMByte *)
  | 5w => s with <|state := 1w; command := 2w; PC := PC_next;
                   data_addr := aV; do_delay_write := w2w ((1 >< 0) aV);
                   delay_write := (30 >< 25) s.i|>

    (* Out *)
  | 6w => s with <|state := 1w; command := 1w; PC := PC_next;
                   data_out := (9 >< 0) s.ALU_res; R := ((30 >< 25) s.i =+ s.ALU_res) s.R|>

    (* In *)
  | 7w => s with <|state := 1w; command := 1w; PC := PC_next;
                   R := ((30 >< 25) s.i =+ w2w s.data_in) s.R|>

    (* Accelerator *)
  | 8w => s with <|state := 2w; PC := PC_next;
                   acc_arg_ready := T; acc_arg := aV; delay_write := (30 >< 25) s.i|>

    (* Jump *)
  | 9w => s with <|state := 1w; command := 1w; PC := s.ALU_res;
                   R := ((30 >< 25) s.i =+ PC_next) s.R|>

    (* JumpIfZero *)
  | 10w => (if s.ALU_res = 0w then s with PC := s.PC + wV else s with PC := PC_next)
           with <|state := 1w; command := 1w|>

    (* JumpIfNotZero *)
  | 11w => (if s.ALU_res <> 0w then s with PC := s.PC + wV else s with PC := PC_next)
           with <|state := 1w; command := 1w|>

    (* Interrupt *)
  | 12w => s with <|state := 1w; command := 4w; data_addr := s.mem_start; do_interrupt := T; PC := PC_next|>

    (* LoadConstant, TODO: can reuse ALU here *)
  | 13w => (if word_bit 23 s.i then
              s with R := ((30 >< 25) s.i =+ 0w − w2w ((22 >< 0) s.i)) s.R
            else
              s with R := ((30 >< 25) s.i =+ w2w ((22 >< 0) s.i)) s.R)
            with <|state := 1w; command := 1w; PC := PC_next|>

    (* LoadUpperConstant *)
  | 14w => let x = (30 >< 25) s.i in
            s with <|state := 1w; command := 1w; PC := PC_next;
                     R := (x =+ bit_field_insert 31 23 ((8 >< 0) s.i) (s.R x)) s.R|>

  | _ => s`;

(* TODO: Can be replaced by multiplication (edit: no, need support for +: (:+?) syntax in Verilog for that)...
   TODO: do_delay_write should never be 5w here...? *)
val delay_write_Next_def = Define `
 delay_write_Next fext s =
  case s.do_delay_write of
   0w => s with R := (s.delay_write =+ w2w ((7 >< 0) fext.data_rdata)) s.R
 | 1w => s with R := (s.delay_write =+ w2w ((15 >< 8) fext.data_rdata)) s.R
 | 2w => s with R := (s.delay_write =+ w2w ((23 >< 16) fext.data_rdata)) s.R
 | 3w => s with R := (s.delay_write =+ w2w ((31 >< 24) fext.data_rdata)) s.R
 | 4w => s with R := (s.delay_write =+ fext.data_rdata) s.R
 | _ => s`;

val cpu_Next_0w_def = Define `
 cpu_Next_0w fext s =
  let s = decode_instruction s;
      wV = DecodeReg_imm (word_bit 31 s.i, (30 >< 25) s.i) s;
      aV = DecodeReg_imm (word_bit 23 s.i, (22 >< 17) s.i) s;
      bV = DecodeReg_imm (word_bit 16 s.i, (15 >< 10) s.i) s;
      func = if s.instruction = 0w ∨ s.instruction = 6w ∨
                s.instruction = 9w ∨ s.instruction = 10w ∨
                s.instruction = 11w then
               (9 >< 6) s.i
             else
               9w;
      ALU_fst = if s.instruction = 9w then s.PC else aV;
      ALU_snd = if s.instruction = 9w then aV else bV;
      s = ALU (func, ALU_fst, ALU_snd) s;
      PC_next = s.PC + 4w in
      execute_instruction wV aV bV PC_next fext s`;

val cpu_Next_1w_def = Define `
 cpu_Next_1w fext s =
  let s =
   (if fext.ready /\ s.command = 0w then
    let s = delay_write_Next fext s;
        s = s with <| i := fext.inst_rdata; do_delay_write := 5w |> in
     if s.do_interrupt then s with <| interrupt_req := T; do_interrupt := F; state := 4w |> else s with state := 0w
   else
    s) in
   s with command := 0w`;

val cpu_Next_2w_def = Define `
 cpu_Next_2w fext s =
  let s = if s.acc_res_ready /\ ~s.acc_arg_ready then
           s with <| state := 1w; command := 1w; R := (s.delay_write =+ s.acc_res) s.R |>
          else
           s in
   s with acc_arg_ready := F`;

val cpu_Next_3w_def = Define `
 cpu_Next_3w fext s =
  if fext.mem_start_ready then
   (* Could maybe use ALU here rather than separate addition *)
   (* R separated from rest for workaround for translator *)
   let s = s with R := (0w =+ fext.mem_start_input) s.R in
   s with <| state := 1w;
             command := 1w;
             mem_start := fext.mem_start_input;
             PC := fext.mem_start_input + 64w |>
  else
   s`;

val cpu_Next_4w_def = Define `
 cpu_Next_4w fext s =
  if fext.interrupt_ack then
    s with <| state := 0w; interrupt_req := F |>
  else
    s`;

val cpu_Next_def = Define `
 cpu_Next fext (s:state_circuit) =
  if fext.error = 0w then
   case s.state of
    0w (* execute *) =>
     cpu_Next_0w fext s
  | 1w (* wait for mem *) =>
     cpu_Next_1w fext s
  | 2w (* wait for acc *) =>
     cpu_Next_2w fext s
  | 3w (* wait for start of mem *) =>
     cpu_Next_3w fext s
  | 4w (* wait for interrupt *) =>
     cpu_Next_4w fext s
  | _ (* error states, do nothing forever *) =>
     s
  else
   s with state := 5w`;

val circuit_def = Define `
 (circuit _ init _ 0 = init) /\
 (circuit facc init fext (SUC n) = let s = circuit facc init fext n;
                                       sCpu = cpu_Next (fext n) s;
                                       sAcc = facc s in
                                      sCpu with <| acc_res_ready := sAcc.acc_res_ready;
                                                   acc_res := sAcc.acc_res;
                                                   acc_state := sAcc.acc_state |>)`;

val _ = export_theory ();
