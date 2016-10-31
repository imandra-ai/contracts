(* A formal model of the Ethereum Virtual Machine in ImandraML         *)
(* (c)Copyright Aesthetic Integration, Ltd., 2016                      *)
(* All rights reserved.                                                *)
(*                                                                     *)
(* Released under Apache 2.0 license as described in the file LICENSE. *)
(*                                                                     *)
(* Contributors:                                                       *)
(*  Grant Olney Passmore (grant@aestheticintegration.com)              *)
(*                                                                     *)

(* EVM machine state *)

type state =
  { stack           : word list;
    memory          : memory;
    program         : program;
    pc              : word;
    storage         : storage;
    balance         : balance;
    ext             : ext;
    msg             : msg;
    gas             : word;
    substate        : substate;
    halted          : halt_status;
    pending_call    : call_status;
  }
;;

(* Initialise EVM machine state with a program *)

let init_state (storage, balance, program, gas, msg, ext) =
  Z.({ stack        = [];
       memory       = empty_mem;
       program      = program;
       pc           = 0;
       storage      = storage;
       balance      = balance;
       ext          = ext;
       msg          = msg;
       gas          = gas;
       substate     = empty_substate;
       halted       = None;
       pending_call = None;
     })
;;

let stack_top s =
  match s.stack with
    [] -> None
  | x :: _ -> Some x
;;

let stack_size s =
  Z.of_int (List.length s.stack)
;;

(* A simple example initial state *)

let example_init_state =
  init_state Z.([],
                [],
                [Push [10]; Push [20]; Add],
                100,
                empty_msg,
                empty_ext)
;;

(* Initialise a call state *)

let init_call_state (s, m) =
  let code_loc = m.code_address in
  let program  = get_code_map (s.ext.code_repository, code_loc) in
  { s with
    pc = Z.(0);
    stack = [];
    msg = m;
    gas = m.msg_gas;
    program = program;
    memory = empty_mem;
    pending_call = None }
;;

(* Merge final state of call with parent state *)

let recover_state_from_call (s, s') =
  match s'.halted with
    Some (Exception _) ->
    { s with
      stack = Z.(0) :: s.stack }
  | Some (Exit e) ->
    (* TODO: Copy proper data subsequence here *)
    { s with
      stack  = Z.(1) :: s.stack;
      memory = { s.memory with data = e.e_data} }
  | None -> s'
;;

(* Make call_data from memory *)

let mk_call_data (mem, mem_start, mem_size) =
  (* We're currently ignoring the fun_selector *)
  let d = mem_range (mem, mem_start, mem_size) in
  { fun_selector = None;
    call_args    = d }
;;

let rec set_mem_range (mstart, data, mem) =
  Z.(match data with
        [] -> mem
      | d :: ds ->
        let new_mem = set_mem (mstart, d, mem) in
        set_mem_range (mstart + 1, ds, new_mem))
;;

let copy_call_data_to_mem (mem, msg_data, mstart, dstart, size) =
  let d = subseq (msg_data.call_args, dstart, size) in
  set_mem_range (mstart, d, mem)
;;

let rec program_to_word_list (p : program) : word list =
  match p with
    [] -> []
  | i :: is ->
    (bytes_of_inst i) @ (program_to_word_list is)
;;

let copy_code_to_mem (mem, code_start, program, mstart, size) =
  let prg_data = program_to_word_list program in
  let d = subseq (prg_data, code_start, size) in
  set_mem_range (mstart, d, mem)
;;
