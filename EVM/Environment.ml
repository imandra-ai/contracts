(* A formal model of the Ethereum Virtual Machine in ImandraML         *)
(* (c)Copyright Aesthetic Integration, Ltd., 2016                      *)
(* All rights reserved.                                                *)
(*                                                                     *)
(* Released under Apache 2.0 license as described in the file LICENSE. *)
(*                                                                     *)
(* Contributors:                                                       *)
(*  Grant Olney Passmore (grant@aestheticintegration.com)              *)
(*                                                                     *)

(* Core environmental data structures and lemmata (ABI compliant) *)

type exit_explanation =
    Code_out_of_range
  | Stop_instruction
  | Return_instruction
  | Out_of_gas
  | Insufficient_stack
  | Stack_size_limit_exceeded
  | Oog_exponent
  | Oog_paying_for_SHA3
  | Oog_extending_memory
  | Oog_copy_data
  | Bad_jumpdest
  | Intentional_suicide
;;

type exit_data = { e_flag : bool;
                   e_gas  : word;
                   e_data : word list;
                   e_desc : exit_explanation }
;;

type halt_reason =
    Exit of exit_data
  | Exception of exit_data
;;

type halt_status = halt_reason option
;;

(* Call data *)

type call_data =
  { fun_selector : fun_id option;
    call_args    : word list }
;;

let empty_call_data =
  { fun_selector = None;
    call_args    = [] }
;;

let offset_of_call_data d =
  match d.fun_selector with
    Some _ -> Z.(4)
  | None   -> Z.(0)
;;

let rec word_of_call_data (d, loc) =
  let m = offset_of_call_data d in
  let l = Z.((loc - m) / 32) in
  let call_arg = List.nth d.call_args (Z.to_int l) in
  call_arg
;;

let size_of_call_data d =
  let m = offset_of_call_data d in
  Z.(m + (32 * of_int(List.length d.call_args)))
;;

(* Memory *)

type memory =
    { data       : word list;
      cur_size   : word;
      peek       : word }
;;

let empty_mem = Z.({ data = []; cur_size = 0; peek = 0 });;

let round_up_word_index (max_index, i) =
  Z.(max max_index (ceiling(i + 32, 32)))
;;

(* @meta[measure : k_zeroes]
    let measure_k_zeroes (k : int) = k
   @end
 *)

let rec k_zeroes (k) =
  Z.(if k <= 0 then []
     else 0 :: k_zeroes (k-1))
;;

let pad_mem_up_to (data, from, upto) =
  Z.(let d = List.rev data in
     let z = k_zeroes (upto - from) in
     List.rev (z @ d))
;;

(* Note: get_mem is currently for word boundary reads, byte-addressable *)

let get_mem (i, mem : word * memory) =
  Z.(let k = mem.cur_size in
     if i < k*32 then
       let v = List.nth mem.data (Z.to_int (i/32)) in
       { mem with peek = v }
     else
       let new_size = round_up_word_index (mem.cur_size, i) in
       let data' = pad_mem_up_to(mem.data, mem.cur_size, new_size) in
       { cur_size = new_size;
         data = data';
         peek = 0 })
;;

(* @meta[measure : drop_fst]
    let measure_drop_fst (lst, n : _ * int) = n
   @end
 *)

let rec drop_fst (lst, n) =
  Z.(if n <= 0 || lst = [] then lst
     else drop_fst (List.tl lst, n-1))
;;

let rec take (lst, n) =
  Z.(if n <= 0 || lst = [] then []
     else List.hd lst :: (take (List.tl lst, n-1)))
;;

let subseq (lst, base, len) =
  Z.(let new_lst = drop_fst (lst, base) in
     take (new_lst, len))
;;

let rec replace_nth (lst, i, v) =
  Z.(match lst with
       [] -> []
     | x::xs -> if i = 0 then
                  v :: xs
                else x :: replace_nth (xs, i-1, v))
;;

(* Set on word boundaries *)

let set_mem (i, v, mem : word * word * memory) =
   Z.(if (i / 32) >= mem.cur_size then
       let new_size = round_up_word_index (mem.cur_size, i) in
       let data' = pad_mem_up_to(mem.data, mem.cur_size, new_size) in
       let data'' = replace_nth(data', i / 32, v) in
       { mem with cur_size  = new_size;
                  data      = data'' }
     else
       let data' = replace_nth(mem.data, i / 32, v) in
       { mem with data = data';
                  cur_size = round_up_word_index (mem.cur_size, i) })
;;

let subseq_32 (lst, base) =
  subseq (lst, base, Z.(32))
;;

(* Return a range of memory - endpoints must be word boundaries *)

let mem_range (mem, from_idx, len) =
  Z.(if len = 0 then []
     else subseq (mem.data, from_idx / 32, len / 32))
;;

(* Set a byte in memory *)

let set_byte (idx, v, mem : word * byte * memory) =
  Z.(let w_idx = idx / 32 in
     let w     =
       if w_idx < mem.cur_size then
         List.nth mem.data (to_int w_idx)
       else 0 in
     let b_idx = w mod 32 in
     let bytes = mk_32_bytes w in
     let bytes = replace_nth(bytes, b_idx, v) in
     let w     = word_of_bytes bytes in
     set_mem (w_idx, w, mem))
;;

(* Various concrete maps *)

type located_word = { w_loc : address; w_val : word };;

type word_map = located_word list;;

let rec get_word_map (w_map, w_loc) =
  match w_map with
    [] -> Z.(0)
  | x :: xs ->
    if x.w_loc = w_loc then x.w_val
    else get_word_map (xs, w_loc)
;;

type located_code = { c_loc : address; c_val : program };;

type code_map = located_code list;;

let rec get_code_map (c_map, c_loc) =
  match c_map with
    [] -> []
  | x :: xs ->
    if x.c_loc = c_loc then x.c_val
    else get_code_map (xs, c_loc)
;;

let rec code_acct_exists (c_map, c_loc) =
  match c_map with
    [] -> false
  | x :: xs ->
    x.c_loc = c_loc
    || code_acct_exists (xs, c_loc)
;;

type ext =
  { tx_origin        : address;
    tx_gas_price     : word;
    block_hashes     : word_map;
    block_coinbase   : word;
    block_timestamp  : word;
    block_number     : word;
    block_difficulty : word;
    block_gas_limit  : word;
    code_repository  : code_map;
  }
;;

let empty_ext =
  Z.({ tx_origin        = 0;
       tx_gas_price     = 0;
       block_hashes     = [];
       block_coinbase   = 0;
       block_timestamp  = 0;
       block_number     = 0;
       block_difficulty = 0;
       block_gas_limit  = 0;
       code_repository  = []})
;;

(* Get external code *)

let get_ext_code (addr, ext) =
  get_code_map (ext.code_repository, addr)
;;

let account_exists (addr, ext) =
  code_acct_exists (ext.code_repository, addr)
;;

(* Balance *)

type balance_entry =
  { bal_loc : address;
    bal_val : word }
;;

type balance = balance_entry list;;

(* Call return *)

type return_result =
  { return_data    : byte list;
    return_balance : balance }
;;

(* Storage *)

type storage_entry = { storage_loc : word;
                       storage_val : word }
;;

type storage = storage_entry list;;

(* Balance manipulation *)

let set_balance (a,n,b : address * word * balance) =
  { bal_loc = a; bal_val = n } :: b
;;

let rec get_balance (a,b : address * balance) =
  match b with
    [] -> Z.zero
  | b :: bs ->
    if b.bal_loc = a then b.bal_val
    else get_balance (a, bs)
;;

theorem[rw] set_balance_works (a,n,b) =
  get_balance(a, set_balance(a,n,b)) = n
;;

theorem[rw] set_balance_stable (a1,a2,b1,b2,bals) =
  (a1 <> a2)
   ==>
   (get_balance(a1, set_balance(a2,b2,bals))
    =
    get_balance(a1, bals))
;;

:disable get_balance set_balance

(* Simple example lemma *)

lemma _ (b) = Z.(get_balance (10, set_balance(10, 5, b)) = 5);;

(* Storage *)

let set_storage (a,v,store : address * word * storage) =
  { storage_loc = a; storage_val = v } :: store
;;

let rec get_storage (a,store : address * storage) =
  match store with
    [] -> Z.zero
  | e :: es ->
    if e.storage_loc = a then e.storage_val
    else get_storage (a, es)
;;

theorem[rw] set_storage_works (a,v,store) =
  get_storage(a, set_storage(a,v,store)) = v
;;

theorem[rw] set_storage_stable (a1,a2,v1,v2,store) =
  (a1 <> a2)
   ==>
   (get_storage(a1, set_storage(a2,v2,store))
    =
    get_storage(a1, store))
;;

:disable get_storage set_storage

(* Substate: Suicides, Logs, Refund balance *)

type log_entry =
  { topics     : word list;
    logged_mem : word list }
;;

type substate =
  { suicides   : address list;
    logs       : log_entry list;
    refund     : word }
;;

let empty_substate =
  { suicides = [];
    logs     = [];
    refund   = Z.(0) }
;;

(* Note: We store logs in reverse chronological order. *)

let add_log (substate, topics, mem : substate * word list * word list) =
  let l = { topics     = topics;
            logged_mem = mem } in
  { substate with logs = l :: substate.logs }
;;

let add_suicide (substate, target : substate * address) =
  { substate with suicides = target :: substate.suicides }
;;

(* Messages *)

type msg =
  { recipient       : address;
    sender          : address;
    value           : word;
    msg_gas         : word;
    msg_data        : call_data;
    depth           : word;
    msg_logs        : log_entry list;
    code_address    : address;
    is_create       : bool;
    transfers_value : bool }
;;

type call_status = msg option
;;

let empty_msg =
  Z.({ recipient       = 0;
       sender          = 0;
       value           = 0;
       msg_gas         = 0;
       msg_data        = empty_call_data;
       depth           = 0;
       msg_logs        = [];
       code_address    = 0;
       is_create       = false;
       transfers_value = false
       })
;;

let mk_basic_msg (call_data) =
  { empty_msg with msg_data = call_data }
;;

