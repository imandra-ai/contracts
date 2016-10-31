(* A formal model of the Ethereum Virtual Machine in ImandraML         *)
(* (c)Copyright Aesthetic Integration, Ltd., 2016                      *)
(* All rights reserved.                                                *)
(*                                                                     *)
(* Released under Apache 2.0 license as described in the file LICENSE. *)
(*                                                                     *)
(* Contributors:                                                       *)
(*  Grant Olney Passmore (grant@aestheticintegration.com)              *)
(*                                                                     *)

:load Word256.ml
:load Instructions.ml
:load Environment.ml
:load Gas.ml
:load State.ml
:load Exceptions.ml
:load Semantics.ml

let next_inst s =
  index_into_program (s.pc, s.program)
;;

(* From a given state, execute a given EVM instruction *)

let do_inst (s, inst : state * instruction) =

  if s.pc >= program_length(s.program) then
    raise_exception (s, Code_out_of_range)
  else if Z.(base_cost_of_inst(inst) > s.gas) then
    raise_exception (s, Out_of_gas)
  else if num_in_args(inst) > List.length s.stack then
    raise_exception (s, Insufficient_stack)
  else if (List.length s.stack - num_in_args(inst) + num_out_args(inst) > 1024) then
    raise_exception (s, Stack_size_limit_exceeded)

  else

    let s = { s with gas = Z.(s.gas - base_cost_of_inst(inst)) }
    in

    match inst with

    (* Stop and arithmetic *)

    | Stop           -> exec_Stop (s)
    | Add            -> exec_Add (s)
    | Mul            -> exec_Mul (s)
    | Sub            -> exec_Sub (s)
    | Div            -> exec_Div (s)
    | SDiv           -> exec_SDiv (s)
    | Mod            -> exec_Mod (s)
    | SMod           -> exec_SMod (s)
    | AddMod         -> exec_AddMod (s)
    | MulMod         -> exec_MulMod (s)
    | Exp            -> exec_Exp (s)
    | SignExtend     -> exec_SignExtend (s)

    (* Comparison and bitwise logical operations *)

    | Lt             -> exec_Lt (s)
    | Gt             -> exec_Gt (s)
    | Slt            -> exec_Slt (s)
    | Sgt            -> exec_Sgt (s)
    | Eq             -> exec_Eq (s)
    | IsZero         -> exec_IsZero (s)
    | BitAnd         -> exec_BitAnd (s)
    | BitOr          -> exec_BitOr (s)
    | BitXor         -> exec_BitXor (s)
    | BitNot         -> exec_BitNot (s)
    | Byte           -> exec_Byte (s)

    (* SHA3 *)

    | SHA3           -> exec_SHA3 (s)

    (* Environment *)

    | Address        -> exec_Address (s)
    | Balance        -> exec_Balance (s)
    | Origin         -> exec_Origin (s)
    | Caller         -> exec_Caller (s)
    | CallValue      -> exec_CallValue (s)
    | CallDataLoad   -> exec_CallDataLoad (s)
    | CallDataSize   -> exec_CallDataSize (s)
    | CallDataCopy   -> exec_CallDataCopy (s)
    | CodeSize       -> exec_CodeSize (s)
    | CodeCopy       -> exec_CodeCopy (s)
    | GasPrice       -> exec_GasPrice (s)
    | ExtCodeSize    -> exec_ExtCodeSize (s)
    | ExtCodeCopy    -> exec_CodeCopy (s)

    (* Block information *)

    | BlockHash      -> exec_BlockHash (s)
    | CoinBase       -> exec_CoinBase (s)
    | TimeStamp      -> exec_TimeStamp (s)
    | Number         -> exec_Number (s)
    | Difficulty     -> exec_Difficulty (s)
    | GasLimit       -> exec_GasLimit (s)

    (* Stack, memory, storage and flow operations *)

    | Pop            -> exec_Pop (s)
    | MLoad          -> exec_MLoad (s)
    | MStore         -> exec_MStore (s)
    | MStore8        -> exec_MStore8 (s)
    | SLoad          -> exec_SLoad (s)
    | SStore         -> exec_SStore (s)
    | Jump           -> exec_Jump (s)
    | JumpI          -> exec_JumpI (s)
    | Pc             -> exec_Pc (s)
    | MSize          -> exec_MSize (s)
    | Gas            -> exec_Gas (s)
    | JumpDest       -> exec_JumpDest (s)

    (* Push operations *)
    (* We use (Push ...) for Push1 ... Push32,
       determining which we have by the length of byte list. *)

    | Push w         -> exec_Push (s, w)

    (* Duplication operations *)

    | Dup k          -> exec_Dup (s, k)

    (* Exchange operations *)

    | Swap k         -> exec_Swap (s, k)

    (* Log operations *)

    | Log k          -> exec_Log (s, k)

    (* System operations *)

    | Create         -> exec_Create (s)
    | Call           -> exec_Call (s)
    | CallCode       -> exec_CallCode (s)
    | Return         -> exec_Return (s)
    | DelegateCall   -> exec_DelegateCall (s)
    | Suicide        -> exec_Suicide (s)
;;

(* Step a state *)

let step (s) =
  do_inst (s, next_inst s)
;;

(* From a given state, run the EVM k steps.

   @meta[measure : run]
    let measure_run (s, k : _ * int) = k
   @end
*)

let rec run (s, k) =
  if k <= 0 then s
  else
    match s.pending_call with
      Some m ->
      let s_c  = init_call_state (s,m) in
      let s_c' = run(s_c, k-1) in
      let s    = recover_state_from_call (s, s_c') in
      run (step s, k-1)
    | None -> run (step s, k-1)
;;

(* Register `run' as the entry point to our semantic machine model.

   This instructs Imandra to give special treatment to the expansion and
   simplification of instances of the (recursive) `run' function.

   The result is a bytecode analysis engine combining staged symbolic execution
   with inductive proof, automatically derived from the formal operational
   semantics given by the body of `run.'
*)

:machine run 10000
