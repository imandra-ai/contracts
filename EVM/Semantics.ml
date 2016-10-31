(* A formal model of the Ethereum Virtual Machine in ImandraML         *)
(* (c)Copyright Aesthetic Integration, Ltd., 2016                      *)
(* All rights reserved.                                                *)
(*                                                                     *)
(* Released under Apache 2.0 license as described in the file LICENSE. *)
(*                                                                     *)
(* Contributors:                                                       *)
(*  Grant Olney Passmore (grant@aestheticintegration.com)              *)
(*                                                                     *)

(* Executable operational semantics for the EVM ISA *)

let exec_Stop (s) =
  peaceful_exit (s, Stop_instruction, [])
;;

let exec_Push (s, bytes) =
  { s with
    stack = (word_of_bytes (List.rev bytes)) :: s.stack;
    pc = Z.(s.pc + (of_int (List.length bytes)) + 1) }
;;

let exec_CallDataLoad (s) =
  let loc   = List.hd s.stack in
  let data  = word_of_call_data (s.msg.msg_data, loc) in
  { s with
    stack = data :: (List.tl s.stack);
    pc = Z.(s.pc + 1) }
;;

let exec_CallDataSize (s) =
  let size = size_of_call_data s.msg.msg_data in
  { s with
    stack = size :: s.stack;
    pc = Z.(s.pc + 1) }
;;

let exec_CodeSize (s) =
  let size = Z.of_int (List.length s.program) in
  { s with
    stack = size :: s.stack;
    pc = Z.(s.pc + 1) }
;;

let exec_SLoad (s) =
  let loc = List.hd s.stack in
  let v   = get_storage (loc, s.storage) in
  { s with
    stack = v :: (List.tl s.stack);
    pc = Z.(s.pc + 1) }
;;

let exec_SStore (s) =
  let loc = List.hd s.stack in
  let v   = List.hd (List.tl s.stack) in
  { s with
    stack = List.tl (List.tl s.stack);
    storage = set_storage(loc, v, s.storage);
    pc = Z.(s.pc + 1) }
;;

let exec_BitAnd (s) =
  let v1 = List.hd s.stack in
  let v2 = List.hd (List.tl s.stack) in
  let new_v = Z.(logand v1 v2) in
  { s with
    stack = new_v :: (List.tl (List.tl s.stack));
    pc = Z.(s.pc + 1) }
;;

let exec_BitNot (s) =
  let v = List.hd s.stack in
  let new_v = u256(Z.lognot v) in
  { s with
    stack = new_v :: (List.tl s.stack);
    pc = Z.(s.pc + 1) }
;;

let exec_BitOr (s) =
  let v1 = List.hd s.stack in
  let v2 = List.hd (List.tl s.stack) in
  let new_v = fix_word(Z.logor v1 v2) in
  { s with
    stack = new_v :: (List.tl (List.tl s.stack));
    pc = Z.(s.pc + 1) }
;;

let exec_BitXor (s) =
  let v1 = List.hd s.stack in
  let v2 = List.hd (List.tl s.stack) in
  let new_v = fix_word(Z.logxor v1 v2) in
  { s with
    stack = new_v :: (List.tl (List.tl s.stack));
    pc = Z.(s.pc + 1) }
;;

(* Control flow *)

let exec_JumpI (s) =
  let new_pc = List.hd s.stack in
  let test   = List.hd (List.tl s.stack) in
  if test <> Z.(0) then
    { s with stack = List.tl (List.tl s.stack);
             pc = new_pc }
  else
    { s with stack = List.tl (List.tl s.stack);
             pc = Z.(s.pc + 1) }
;;

let exec_Jump (s) =
  let a1 = List.hd s.stack in
  { s with stack = List.tl s.stack;
           pc = a1 }
;;

let exec_JumpDest (s) =
  { s with pc = Z.(s.pc + 1) }
;;

(* Arithmetic *)

let exec_Add (s) =
  let x1 = List.hd s.stack in
  let x2 = List.hd (List.tl s.stack) in
  let v  = fix_word Z.(x1 + x2) in
  let st = List.tl (List.tl s.stack) in
  { s with stack = v :: st;
           pc = Z.(s.pc + 1) }
;;

let exec_Sub (s) =
  let x1 = List.hd s.stack in
  let x2 = List.hd (List.tl s.stack) in
  let v  = fix_word Z.(x1 - x2) in
  let st = List.tl (List.tl s.stack) in
  { s with stack = v :: st;
           pc = Z.(s.pc + 1) }
;;

let exec_Mul (s) =
  let x1 = List.hd s.stack in
  let x2 = List.hd (List.tl s.stack) in
  let v  = fix_word Z.(x1 * x2) in
  let st = List.tl (List.tl s.stack) in
  { s with stack = v :: st;
           pc = Z.(s.pc + 1) }
;;

let exec_Div (s) =
  let x1 = List.hd s.stack in
  let x2 = List.hd (List.tl s.stack) in
  let v  = if x2 = Z.(0) then Z.(0) else
            fix_word Z.(x1 / x2) in
  let st = List.tl (List.tl s.stack) in
  { s with stack = v :: st;
           pc = Z.(s.pc + 1) }
;;

let exec_SDiv (s) =
  let x1 = List.hd s.stack in
  let x2 = List.hd (List.tl s.stack) in
  let v  =
    let open Z in
    if x2 = zero then zero else
    if x2 = minus_one && x1 = neg pow_2_255
    then pow_2_255 else
      let q = (x1 / x2) in
      let sgn = if q < zero then minus_one else
                if q = zero then zero else
                one
      in
      sgn * fix_word(x1 / x2)
  in
  let st = List.tl (List.tl s.stack) in
  { s with stack = v :: st;
           pc = Z.(s.pc + 1) }
;;

let exec_Mod (s) =
  let x1 = List.hd s.stack in
  let x2 = List.hd (List.tl s.stack) in
  let v  =
    let open Z in
    if x2 = zero then zero else
            fix_word (x1 mod x2) in
  let st = List.tl (List.tl s.stack) in
  { s with stack = v :: st;
           pc = Z.(s.pc + 1) }
;;

let exec_SMod (s) =
  let x1 = List.hd s.stack in
  let x2 = List.hd (List.tl s.stack) in
  let v  =
    let open Z in
    if x1 < zero then neg(abs(x1) mod abs(x2))
    else (abs(x1) mod abs(x2)) in
  let v  = fix_word v in
  let st = List.tl (List.tl s.stack) in
  { s with stack = v :: st;
           pc = Z.(s.pc + 1) }
;;

let exec_AddMod (s) =
  let x1 = List.hd s.stack in
  let x2 = List.hd (List.tl s.stack) in
  let x3 = List.hd (List.tl (List.tl s.stack)) in
  let v  = Z.(fix_word ((x1 + x2) mod x3)) in
  let st = List.tl (List.tl (List.tl s.stack)) in
  { s with stack = v :: st;
           pc = Z.(s.pc + 1) }
;;

let exec_MulMod (s) =
  let x1 = List.hd s.stack in
  let x2 = List.hd (List.tl s.stack) in
  let x3 = List.hd (List.tl (List.tl s.stack)) in
  let v  = Z.(fix_word ((x1 * x2) mod x3)) in
  let st = List.tl (List.tl (List.tl s.stack)) in
  { s with stack = v :: st;
           pc = Z.(s.pc + 1) }
;;

let exec_Exp (s) =
  let x1 = List.hd s.stack in
  let x2 = List.hd (List.tl s.stack) in
  let v  = Z.(fix_word (pow x1 (to_int x2))) in
  let st = List.tl (List.tl s.stack) in
  { s with stack = v :: st;
           pc = Z.(s.pc + 1) }
;;

(* Comparison operations *)

let exec_Lt (s) =
  let x1 = List.hd s.stack in
  let x2 = List.hd (List.tl s.stack) in
  let v  = Z.(if x1 < x2 then 1 else 0) in
  let st = List.tl (List.tl s.stack) in
  { s with stack = v :: st;
           pc = Z.(s.pc + 1) }
;;

let exec_Gt (s) =
  let x1 = List.hd s.stack in
  let x2 = List.hd (List.tl s.stack) in
  let v  = Z.(if x1 > x2 then 1 else 0) in
  let st = List.tl (List.tl s.stack) in
  { s with stack = v :: st;
           pc = Z.(s.pc + 1) }
;;

let exec_Slt (s) =
  let x1 = List.hd s.stack in
  let x2 = List.hd (List.tl s.stack) in
  let v  = Z.(if x1 < x2 then 1 else 0) in
  let st = List.tl (List.tl s.stack) in
  { s with stack = v :: st;
           pc = Z.(s.pc + 1) }
;;

let exec_Sgt (s) =
  let x1 = List.hd s.stack in
  let x2 = List.hd (List.tl s.stack) in
  let v  = Z.(if x1 > x2 then 1 else 0) in
  let st = List.tl (List.tl s.stack) in
  { s with stack = v :: st;
           pc = Z.(s.pc + 1) }
;;

let exec_SignExtend (s) =
  let byte_num = List.hd s.stack in
  let sign_bit_index = Z.(byte_num * 8) in
  let word = List.hd (List.tl s.stack) in
  let v  = sign_extend_from_bit(word, sign_bit_index) in
  let st = List.tl (List.tl s.stack) in
  { s with stack = v :: st;
           pc = Z.(s.pc + 1) }
;;

let exec_Byte (s) =
  let byte_num = List.hd s.stack in
  let word = List.hd (List.tl s.stack) in
  let v  = get_byte(word, 32 - Z.(to_int byte_num)) in
  let st = List.tl (List.tl s.stack) in
  { s with stack = v :: st;
           pc = Z.(s.pc + 1) }
;;

let exec_Eq (s) =
  let x1 = List.hd s.stack in
  let x2 = List.hd (List.tl s.stack) in
  let v  = Z.(if x1 = x2 then 1 else 0) in
  let st = List.tl (List.tl s.stack) in
  { s with stack = v :: st;
           pc = Z.(s.pc + 1) }
;;

let exec_IsZero (s) =
  let x1 = List.hd s.stack in
  let v  = Z.(if x1 = zero then 1 else 0) in
  let st = List.tl s.stack in
  { s with stack = v :: st;
           pc = Z.(s.pc + 1) }
;;

let exec_Pop (s) =
  { s with stack = List.tl s.stack;
           pc = Z.(s.pc + 1) }
;;

let exec_Pc (s) =
  let pc = s.pc in
  { s with stack = pc :: s.stack;
           pc = Z.(s.pc + 1) }
;;

let exec_Gas (s) =
  let g = s.gas in
  { s with stack = g :: s.stack;
           pc = Z.(s.pc + 1) }
;;

let exec_Dup (s, k) =
  let i = List.nth s.stack k in
  { s with stack = i :: s.stack;
           pc = Z.(s.pc + 1) }
;;

let swap_k (stack, k : word list * int) =
  if k = 1 then
    match stack with
      x0 :: x1 :: rst ->
      x1 :: x0 :: rst
    | _ -> stack
  else if k = 2 then
    match stack with
      x0 :: x1 :: x2 :: rst ->
      x2 :: x1 :: x0 :: rst
    | _ -> stack
  else if k = 3 then
    match stack with
      x0 :: x1 :: x2 :: x3 :: rst ->
      x3 :: x1 :: x2 :: x0 :: rst
    | _ -> stack
  else if k = 4 then
    match stack with
      x0 :: x1 :: x2 :: x3 :: x4 :: rst ->
      x4 :: x1 :: x2 :: x3 :: x0 :: rst
    | _ -> stack
  else if k = 5 then
    match stack with
      x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: rst ->
      x5 :: x1 :: x2 :: x3 :: x4 :: x0 :: rst
    | _ -> stack
  else if k = 6 then
    match stack with
      x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: rst ->
      x6 :: x1 :: x2 :: x3 :: x4 :: x5 :: x0 :: rst
    | _ -> stack
  else if k = 7 then
    match stack with
      x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: rst ->
      x7 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x0 :: rst
    | _ -> stack
  else if k = 8 then
    match stack with
      x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: rst ->
      x8 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x0 :: rst
    | _ -> stack
  else if k = 9 then
    match stack with
      x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: rst ->
      x9 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x0 :: rst
    | _ -> stack
  else if k = 10 then
    match stack with
      x0  :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: rst ->
      x10 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x0  :: rst
    | _ -> stack
  else if k = 11 then
    match stack with
      x0  :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rst ->
      x11 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x0  :: rst
    | _ -> stack
  else if k = 12 then
    match stack with
      x0  :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rst ->
      x12 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x0  :: rst
    | _ -> stack
  else if k = 13 then
    match stack with
      x0  :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rst ->
      x13 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x0  :: rst
    | _ -> stack
  else if k = 14 then
    match stack with
      x0  :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rst ->
      x14 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x0  :: rst
    | _ -> stack
  else if k = 15 then
    match stack with
      x0  :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rst ->
      x15 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x0  :: rst
    | _ -> stack
  else if k = 16 then
    match stack with
      x0  :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rst ->
      x16 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x0  :: rst
    | _ -> stack
  else stack
;;

let exec_Swap (s, k) =
  let new_stack = swap_k (s.stack, k) in
  { s with stack = new_stack;
           pc = Z.(s.pc + 1) }
;;

let exec_Balance (s) =
  let address = List.hd s.stack in
  let v   = get_balance(address, s.balance) in
  let st = List.tl s.stack in
  { s with stack = v :: st;
           pc = Z.(s.pc + 1) }
;;

(* Byte-addressable, reads and writes on word boundaries (i mod 32 = 0) *)

let exec_MLoad (s) =
  let i = List.hd s.stack in
  let m = s.memory in
  let ok = mem_extend_ok(s.gas, m.cur_size, i, Z.(32)) in
  match ok with
    Some e ->
    let mem = get_mem(i, s.memory) in
    let st = List.tl s.stack in
    { s with stack = mem.peek :: st;
             memory = mem;
             gas = e.new_gas;
             pc = Z.(s.pc + 1) }
  | None -> raise_exception(s, Oog_extending_memory)
;;

let exec_MStore (s) =
  let i = List.hd s.stack in
  let v = List.hd (List.tl s.stack) in
  let mem  = set_mem(i, v, s.memory) in
  let st = List.tl (List.tl s.stack) in
  { s with stack = st;
           memory = mem;
           pc = Z.(s.pc + 1) }
;;

let exec_MStore8 (s : state) =
  let i = List.hd s.stack in
  let v = List.hd (List.tl s.stack) in
  let mem  = set_byte(i, Z.(v mod 256), s.memory) in
  let st = List.tl (List.tl s.stack) in
  { s with stack = st;
           memory = mem;
           pc = Z.(s.pc + 1) }
;;

let exec_MSize (s) =
  let num_bytes = Z.(s.memory.cur_size * 32) in
  { s with stack = num_bytes :: s.stack;
           pc = Z.(s.pc + 1) }
;;

let exec_Origin (s) =
  { s with stack = s.ext.tx_origin :: s.stack;
           pc = Z.(s.pc + 1) }
;;

let exec_Caller (s) =
  { s with stack = s.msg.sender :: s.stack;
           pc = Z.(s.pc + 1) }
;;

let exec_CallValue (s) =
  { s with stack = s.msg.value :: s.stack;
           pc = Z.(s.pc + 1) }
;;

let exec_GasPrice (s) =
  { s with stack = s.ext.tx_gas_price :: s.stack;
           pc = Z.(s.pc + 1) }
;;

let exec_TimeStamp (s) =
  { s with stack = s.ext.block_timestamp :: s.stack;
           pc = Z.(s.pc + 1) }
;;

let exec_Address (s) =
  { s with stack = s.msg.recipient :: s.stack;
           pc = Z.(s.pc + 1) }
;;

val sha3 : word list -> word;;

(* Note: As far as I can tell, the yellow paper doesn't specify if exec_SHA3
    should update the memory.cur_size in the manner that, e.g., MLOAD does. As
    there is no mention of it, we assume the answer is no. But, we should check
    this with Vitalik et al and in all major EVMs. *)

let exec_SHA3 (s) =
  let base = List.hd s.stack in
  let len  = List.hd (List.tl s.stack) in
  let seq  = mem_range (s.memory, base, len) in
  let w    = sha3 (seq) in
  let st   = List.tl (List.tl s.stack) in
  { s with stack = w :: st;
           pc = Z.(s.pc + 1) }
;;

let exec_Return (s : state) =
  Z.(let s0 = List.hd s.stack in
     let s1 = List.hd (List.tl s.stack) in
     let ok = mem_extend_ok (s.gas, s.memory.cur_size, s0, s1) in
     match ok with
       Some e ->
       peaceful_exit({s with gas = e.new_gas},
                     Return_instruction,
                     mem_range(s.memory, s0, s1))
     | None ->
       let s' = {s with gas = 0} in
       raise_exception(s', Oog_extending_memory))
;;

let exec_GasLimit (s : state) =
  { s with
    stack = s.ext.block_difficulty :: s.stack;
    pc = Z.(s.pc + 1) }
;;

let exec_BlockHash (s : state) =
  let loc = List.hd s.stack in
  let h = get_word_map(s.ext.block_hashes, loc) in
  { s with
    stack = h :: (List.tl s.stack);
    pc = Z.(s.pc + 1) }
;;

let exec_CoinBase (s : state) =
  { s with
    stack = s.ext.block_coinbase :: s.stack;
    pc = Z.(s.pc + 1) }
;;

let exec_Number (s : state) =
  { s with
    stack = s.ext.block_number :: s.stack;
    pc = Z.(s.pc + 1) }
;;

let exec_Difficulty (s : state) =
  { s with
    stack = s.ext.block_difficulty :: s.stack;
    pc = Z.(s.pc + 1) }
;;

let exec_Suicide (s : state) =
  Z.(let to_    = List.hd s.stack in
     let to_b   = get_balance(to_, s.balance) in
     let xfer   = get_balance(s.msg.recipient, s.balance) in
     let b      = set_balance(to_, to_b + xfer, s.balance) in
     let b      = set_balance(s.msg.recipient, 0, b) in
     let sub    = add_suicide(s.substate, s.msg.recipient) in
     let s      = { s with
                    stack    = List.tl s.stack;
                    balance  = b;
                    substate = sub;
                    pc       = s.pc + 1 }
     in
     peaceful_exit (s, Intentional_suicide, []))
;;

let exec_Log (s, k : state * int) =
  let mem_start = List.hd s.stack in
  let mem_size  = List.hd (List.tl s.stack) in
  let data      = mem_range(s.memory, mem_start, mem_size) in
  let topic_stk = List.tl (List.tl s.stack) in
  let topics    =
    if (k = 0) then
      []
    else if (k = 1) then
      [List.hd topic_stk]
    else if (k = 2) then
      [List.hd topic_stk;
       List.hd (List.tl topic_stk)]
    else if (k = 3) then
      [List.hd topic_stk;
       List.hd (List.tl topic_stk);
       List.hd (List.tl (List.tl topic_stk))]
    else
      [List.hd topic_stk;
       List.hd (List.tl topic_stk);
       List.hd (List.tl (List.tl topic_stk));
       List.hd (List.tl (List.tl (List.tl topic_stk)))]
  in
  let stack = drop_fst(topic_stk, Z.of_int k) in
  let substate = add_log(s.substate, topics, data) in
  { s with stack = stack;
           substate = substate;
           pc = Z.(s.pc + 1) }
;;

let exec_ExtCodeSize (s : state) =
  let addr = List.hd s.stack in
  let code = get_code_map (s.ext.code_repository, addr) in
  let len  = Z.of_int (List.length code) in
  { s with stack = len :: (List.tl s.stack);
           pc    = Z.(s.pc + 1) }
;;

let exec_CallDataCopy (s : state) =
  let mstart = List.hd s.stack in
  let dstart = List.hd (List.tl s.stack) in
  let size   = List.hd (List.tl (List.tl s.stack)) in
  let stk    = List.tl (List.tl (List.tl s.stack)) in
  let ok     = mem_extend_ok (s.gas, s.memory.cur_size, mstart, size) in
  match ok with
    Some e ->
    let ok = data_copy_ok (e.new_gas, size) in
    (match ok with
       Some g ->
       { s with
         stack  = stk;
         gas    = g;
         memory = copy_call_data_to_mem (s.memory, s.msg.msg_data, mstart, dstart, size);
         pc     = Z.(s.pc + 1) }
     | None ->
       raise_exception (s, Oog_copy_data))
  | None ->
    raise_exception (s, Oog_extending_memory)
;;

let exec_CodeCopy (s : state) =
  let start = List.hd s.stack in
  let s1    = List.hd (List.tl s.stack) in
  let size  = List.hd (List.tl (List.tl s.stack)) in
  let stk   = List.tl (List.tl (List.tl s.stack)) in
  let ok    = mem_extend_ok (s.gas, s.memory.cur_size, start, size) in
  match ok with
    Some e ->
    let ok = data_copy_ok (e.new_gas, size) in
    (match ok with
       Some g ->
       { s with stack  = stk;
                gas    = g;
                memory = copy_code_to_mem (s.memory, s1, s.program, start, size);
                pc     = Z.(s.pc + 1) }
     | None ->
       raise_exception (s, Oog_copy_data))
  | None ->
    raise_exception (s, Oog_extending_memory)
;;

let exec_ExtCodeCopy (s : state) =
  let addr  = List.hd s.stack in
  let start = List.hd (List.tl s.stack) in
  let s1    = List.hd (List.tl (List.tl s.stack)) in
  let size  = List.hd (List.tl (List.tl (List.tl s.stack))) in
  let stk   = List.tl (List.tl (List.tl (List.tl s.stack))) in
  let ok    = mem_extend_ok (s.gas, s.memory.cur_size, start, size) in
  let code  = get_ext_code (addr, s.ext) in
  match ok with
    Some e ->
    let ok = data_copy_ok (e.new_gas, size) in
    (match ok with
       Some g ->
       { s with stack  = stk;
                gas    = g;
                memory = copy_code_to_mem (s.memory, s1, code, start, size);
                pc     = Z.(s.pc + 1) }
     | None ->
       raise_exception (s, Oog_copy_data))
  | None ->
    raise_exception (s, Oog_extending_memory)
;;

let exec_Create (s : state) =
  let open List in
  Z.(let value         = hd s.stack in
     let mem_start     = hd (tl s.stack) in
     let mem_size      = hd (tl (tl s.stack)) in
     let new_stack     = tl (tl (tl s.stack)) in
     let ok            = mem_extend_ok (s.gas, s.memory.cur_size, mem_start, mem_size) in
     match ok with
       Some e ->
       if get_balance(s.msg.recipient, s.balance) >= value && s.msg.depth < 1024
       then
         begin
           let cd = mk_call_data (s.memory, mem_start, mem_size) in
           let cm = { sender          = s.msg.recipient;
                      recipient       = 0;
                      value           = value;
                      msg_gas         = e.new_gas;
                      msg_data        = cd;
                      depth           = s.msg.depth + 1;
                      code_address    = 0;
                      is_create       = true;
                      transfers_value = value > 0;
                      msg_logs        = [] } in
           { s with
             pending_call = Some cm;
             gas          = e.new_gas;
             pc           = s.pc + 1;
             stack        = new_stack }
         end
       else
         { s with
           stack   = 0 :: new_stack;
           pc      = s.pc + 1;
           gas     = e.new_gas }
     | None -> raise_exception(s, Out_of_gas)
    )
;;

let exec_Call (s : state) =
  let open List in
  Z.(let gas           = hd s.stack in
     let target        = hd (tl s.stack) in
     let value         = hd (tl (tl s.stack)) in
     let mem_in_start  = hd (tl (tl (tl s.stack))) in
     let mem_in_size   = hd (tl (tl (tl (tl s.stack)))) in
     let mem_out_start = hd (tl (tl (tl (tl (tl s.stack))))) in
     let mem_out_size  = hd (tl (tl (tl (tl (tl (tl s.stack)))))) in
     let new_stack     = tl (tl (tl (tl (tl (tl (tl s.stack)))))) in
     let ok_1 = mem_extend_ok (s.gas, s.memory.cur_size, mem_in_start, mem_in_size) in
     let ok_2 = mem_extend_ok (s.gas, s.memory.cur_size, mem_out_start, mem_out_size) in
     let is_create = account_exists (target, s.ext) in
     match ok_1, ok_2 with
       Some e1, Some e2 ->
       let extra_gas =
         match is_create, (value > 0) with
           true, true   -> gas_CALLVALUETRANSFER
         | true, false  -> 0
         | false, true  -> gas_CALLNEWACCOUNT + gas_CALLVALUETRANSFER
         | false, false -> gas_CALLNEWACCOUNT
       in
       let submsg_gas =
         if value > 0 then gas + gas_STIPEND else gas in
       if (s.gas < gas + extra_gas) then
         raise_exception (s, Out_of_gas)
       else
       if get_balance (s.msg.recipient, s.balance) >= value && s.msg.depth < 1024 then
         begin

           (* Now we can actually setup the call! *)
           let new_gas = s.gas - (gas + extra_gas) in
           let cd = mk_call_data (s.memory, mem_in_start, mem_in_size) in
           let cm = { sender          = s.msg.recipient;
                      recipient       = target;
                      value           = value;
                      msg_gas         = submsg_gas;
                      msg_data        = cd;
                      depth           = s.msg.depth + 1;
                      code_address    = target;
                      is_create       = is_create;
                      transfers_value = value > 0;
                      msg_logs        = [] } in
           { s with
             pending_call = Some cm;
             gas          = new_gas;
             pc           = s.pc + 1;
             stack        = new_stack }
         end
       else
         let new_gas = s.gas - (gas + extra_gas - submsg_gas) in
         { s with
           gas   = new_gas;
           pc    = s.pc + 1;
           stack = 0 :: new_stack }
     | _ ->
       raise_exception (s, Oog_extending_memory))
;;

let exec_CallCode (s : state) =
  let open List in
  Z.(let gas           = hd s.stack in
     let target        = hd (tl s.stack) in
     let value         = hd (tl (tl s.stack)) in
     let mem_in_start  = hd (tl (tl (tl s.stack))) in
     let mem_in_size   = hd (tl (tl (tl (tl s.stack)))) in
     let mem_out_start = hd (tl (tl (tl (tl (tl s.stack))))) in
     let mem_out_size  = hd (tl (tl (tl (tl (tl (tl s.stack)))))) in
     let new_stack     = tl (tl (tl (tl (tl (tl (tl s.stack)))))) in
     let ok_1 = mem_extend_ok (s.gas, s.memory.cur_size, mem_in_start, mem_in_size) in
     let ok_2 = mem_extend_ok (s.gas, s.memory.cur_size, mem_out_start, mem_out_size) in
     match ok_1, ok_2 with
       Some e1, Some e2 ->
       let extra_gas =
         if value > 0 then
           gas_CALLVALUETRANSFER
         else 0
       in
       let submsg_gas =
         if value > 0 then gas + gas_STIPEND else gas in
       if (s.gas < gas + extra_gas) then
         raise_exception (s, Out_of_gas)
       else
       if get_balance (s.msg.recipient, s.balance) >= value && s.msg.depth < 1024 then
         begin
           (* Now we can actually setup the call(code)! *)
           let new_gas = s.gas - (gas + extra_gas) in
           let cd = mk_call_data (s.memory, mem_in_start, mem_in_size) in
           let cm = { sender          = s.msg.sender;
                      recipient       = target;
                      value           = value;
                      msg_gas         = submsg_gas;
                      msg_data        = cd;
                      depth           = s.msg.depth + 1;
                      code_address    = target;
                      is_create       = false;
                      transfers_value = false;
                      msg_logs        = [] } in
           { s with
             pending_call = Some cm;
             gas          = new_gas;
             pc           = s.pc + 1;
             stack        = new_stack }
         end
       else
         let new_gas = s.gas - (gas + extra_gas - submsg_gas) in
         { s with
           gas   = new_gas;
           pc    = s.pc + 1;
           stack = 0 :: new_stack }
     | _ ->
       raise_exception (s, Oog_extending_memory))
;;

let exec_DelegateCall (s : state) =
  let open List in
  Z.(let gas           = hd s.stack in
     let target        = hd (tl s.stack) in
     let mem_in_start  = hd (tl (tl s.stack)) in
     let mem_in_size   = hd (tl (tl (tl s.stack))) in
     let mem_out_start = hd (tl (tl (tl (tl s.stack)))) in
     let mem_out_size  = hd (tl (tl (tl (tl (tl s.stack))))) in
     let new_stack     = tl (tl (tl (tl (tl (tl s.stack))))) in
     let value         = 0 in
     let ok_1 = mem_extend_ok (s.gas, s.memory.cur_size, mem_in_start, mem_in_size) in
     let ok_2 = mem_extend_ok (s.gas, s.memory.cur_size, mem_out_start, mem_out_size) in
     match ok_1, ok_2 with
       Some e1, Some e2 ->
       let extra_gas =
         if value > 0 then
           gas_CALLVALUETRANSFER
         else 0
       in
       let submsg_gas =
         if value > 0 then gas + gas_STIPEND else gas in
       if (s.gas < gas + extra_gas) then
         raise_exception (s, Out_of_gas)
       else
       if get_balance (s.msg.recipient, s.balance) >= value && s.msg.depth < 1024 then
         begin
           (* Now we can actually setup the (delegate)call! *)
           let new_gas = s.gas - (gas + extra_gas) in
           let cd = mk_call_data (s.memory, mem_in_start, mem_in_size) in
           let cm = { sender          = s.msg.sender;
                      recipient       = s.msg.recipient;
                      value           = value;
                      msg_gas         = submsg_gas;
                      msg_data        = cd;
                      depth           = s.msg.depth + 1;
                      code_address    = target;
                      is_create       = false;
                      transfers_value = false;
                      msg_logs        = [] } in
           { s with
             pending_call = Some cm;
             gas          = new_gas;
             pc           = s.pc + 1;
             stack        = new_stack }
         end
       else
         let new_gas = s.gas - (gas + extra_gas - submsg_gas) in
         { s with
           gas   = new_gas;
           pc    = s.pc + 1;
           stack = 0 :: new_stack }
     | _ ->
       raise_exception (s, Oog_extending_memory))
;;

