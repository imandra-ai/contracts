(* A formal model of the Ethereum Virtual Machine in ImandraML         *)
(* (c)Copyright Aesthetic Integration, Ltd., 2016                      *)
(* All rights reserved.                                                *)
(*                                                                     *)
(* Released under Apache 2.0 license as described in the file LICENSE. *)
(*                                                                     *)
(* Contributors:                                                       *)
(*  Grant Olney Passmore (grant@aestheticintegration.com)              *)
(*                                                                     *)

(* Ethereum instruction set (Homestead revision) *)

type instruction =
  (* Stop and arithmetic *)
  | Stop
  | Add
  | Mul
  | Sub
  | Div
  | SDiv
  | Mod
  | SMod
  | AddMod
  | MulMod
  | Exp
  | SignExtend
  (* Comparison and bitwise logical operations *)
  | Lt
  | Gt
  | Slt
  | Sgt
  | Eq
  | IsZero
  | BitAnd
  | BitOr
  | BitXor
  | BitNot
  | Byte
  (* SHA3 *)
  | SHA3
  (* Environment *)
  | Address
  | Balance
  | Origin
  | Caller
  | CallValue
  | CallDataLoad
  | CallDataSize
  | CallDataCopy
  | CodeSize
  | CodeCopy
  | GasPrice
  | ExtCodeSize
  | ExtCodeCopy
  (* Block information *)
  | BlockHash
  | CoinBase
  | TimeStamp
  | Number
  | Difficulty
  | GasLimit
  (* Stack, memory, storage and flow operations *)
  | Pop
  | MLoad
  | MStore
  | MStore8
  | SLoad
  | SStore
  | Jump
  | JumpI
  | Pc
  | MSize
  | Gas
  | JumpDest
  (* Push operations *)
  (* We use (Push ...) for Push1 ... Push32,
     determining which we have by the length of byte list. *)
  | Push of byte list
  (* Duplication operations *)
  | Dup of int  (* 1 ... 16 *)
  (* Exchange operations *)
  | Swap of int (* 1 ... 16 *)
  (* Log operations *)
  | Log of int  (* 0 ... 4  *)
  (* System operations *)
  | Create
  | Call
  | CallCode
  | Return
  | DelegateCall
  | Suicide
;;

(* Pretty-printing *)

let rec string_of_bytes (bs : byte list) =
  match bs with
    [] -> ""
  | b :: bs -> (Z.to_string b) ^ (string_of_bytes bs)
;;

let string_of_instruction x =
  match x with
  (* Stop and arithmetic *)
  | Stop              -> "STOP"
  | Add               -> "ADD"
  | Mul               -> "MUL"
  | Sub               -> "SUB"
  | Div               -> "DIV"
  | SDiv              -> "SDIV"
  | Mod               -> "MOD"
  | SMod              -> "SMOD"
  | AddMod            -> "ADDMOD"
  | MulMod            -> "MULMOD"
  | Exp               -> "EXP"
  | SignExtend        -> "SIGNEXTEND"
  (* Comparison and bitwise logical operations *)
  | Lt                -> "LT"
  | Gt                -> "GT"
  | Slt               -> "SLT"
  | Sgt               -> "SGT"
  | Eq                -> "EQ"
  | IsZero            -> "ISZERO"
  | BitAnd            -> "AND"
  | BitOr             -> "OR"
  | BitXor            -> "XOR"
  | BitNot            -> "NOT"
  | Byte              -> "BYTE"
  (* SHA3 *)
  | SHA3              -> "SHA3"
  (* Environment *)
  | Address           -> "ADDRESS"
  | Balance           -> "BALANCE"
  | Origin            -> "ORIGIN"
  | Caller            -> "CALLER"
  | CallValue         -> "CALLVALUE"
  | CallDataLoad      -> "CALLDATALOAD"
  | CallDataSize      -> "CALLDATASIZE"
  | CallDataCopy      -> "CALLDATACOPY"
  | CodeSize          -> "CODESIZE"
  | CodeCopy          -> "CODECOPY"
  | GasPrice          -> "GASPRICE"
  | ExtCodeSize       -> "EXTCODESIZE"
  | ExtCodeCopy       -> "EXTCODECOPY"
  (* Block information *)
  | BlockHash         -> "BLOCKHASH"
  | CoinBase          -> "COINBASE"
  | TimeStamp         -> "TIMESTAMP"
  | Number            -> "NUMBER"
  | Difficulty        -> "DIFFICULTY"
  | GasLimit          -> "GASLIMIT"
  (* Stack, memory, storage and flow operations *)
  | Pop               -> "POP"
  | MLoad             -> "MLOAD"
  | MStore            -> "MSTORE"
  | MStore8           -> "MSTORE8"
  | SLoad             -> "SLOAD"
  | SStore            -> "SSTORE"
  | Jump              -> "JUMP"
  | JumpI             -> "JUMPI"
  | Pc                -> "PC"
  | MSize             -> "MSIZE"
  | Gas               -> "GAS"
  | JumpDest          -> "JUMPDEST"
  | Push bytes        ->
    let n = List.length bytes in
    "PUSH" ^ (string_of_int n) ^ "(" ^ (string_of_bytes bytes) ^ ")"
  (* Duplication operations *)
  | Dup n             -> "DUP" ^ (string_of_int n)
  (* Exchange operations *)
  | Swap n            -> "SWAP" ^ (string_of_int n)
  (* Log operations *)
  | Log n             -> "LOG" ^ (string_of_int n)
  (* System operations *)
  | Create            -> "CREATE"
  | Call              -> "CALL"
  | CallCode          -> "CALLCODE"
  | Return            -> "RETURN"
  | DelegateCall      -> "DELEGATECALL"
  | Suicide           -> "SUICIDE"
;;

(* Number of in and out (stack) args *)

type inst_sig = { num_in : int; num_out : int };;

let sig_of_inst x =
  match x with
  (* Stop and arithmetic *)
  | Stop              -> { num_in = 0; num_out = 0 }
  | Add               -> { num_in = 2; num_out = 1 }
  | Mul               -> { num_in = 2; num_out = 1 }
  | Sub               -> { num_in = 2; num_out = 1 }
  | Div               -> { num_in = 2; num_out = 1 }
  | SDiv              -> { num_in = 2; num_out = 1 }
  | Mod               -> { num_in = 2; num_out = 1 }
  | SMod              -> { num_in = 2; num_out = 1 }
  | AddMod            -> { num_in = 3; num_out = 1 }
  | MulMod            -> { num_in = 3; num_out = 1 }
  | Exp               -> { num_in = 2; num_out = 1 }
  | SignExtend        -> { num_in = 2; num_out = 1 }
  (* Comparison and bitwise logical operations *)
  | Lt                -> { num_in = 2; num_out = 1 }
  | Gt                -> { num_in = 2; num_out = 1 }
  | Slt               -> { num_in = 2; num_out = 1 }
  | Sgt               -> { num_in = 2; num_out = 1 }
  | Eq                -> { num_in = 2; num_out = 1 }
  | IsZero            -> { num_in = 1; num_out = 1 }
  | BitAnd            -> { num_in = 2; num_out = 1 }
  | BitOr             -> { num_in = 2; num_out = 1 }
  | BitXor            -> { num_in = 2; num_out = 1 }
  | BitNot            -> { num_in = 1; num_out = 1 }
  | Byte              -> { num_in = 2; num_out = 1 }
  (* SHA3 *)
  | SHA3              -> { num_in = 2; num_out = 1 }
  (* Environment *)
  | Address           -> { num_in = 0; num_out = 1 }
  | Balance           -> { num_in = 1; num_out = 1 }
  | Origin            -> { num_in = 0; num_out = 1 }
  | Caller            -> { num_in = 0; num_out = 1 }
  | CallValue         -> { num_in = 0; num_out = 1 }
  | CallDataLoad      -> { num_in = 1; num_out = 1 }
  | CallDataSize      -> { num_in = 0; num_out = 1 }
  | CallDataCopy      -> { num_in = 3; num_out = 0 }
  | CodeSize          -> { num_in = 0; num_out = 1 }
  | CodeCopy          -> { num_in = 3; num_out = 0 }
  | GasPrice          -> { num_in = 0; num_out = 1 }
  | ExtCodeSize       -> { num_in = 1; num_out = 1 }
  | ExtCodeCopy       -> { num_in = 4; num_out = 0 }
  (* Block information *)
  | BlockHash         -> { num_in = 1; num_out = 1 }
  | CoinBase          -> { num_in = 0; num_out = 1 }
  | TimeStamp         -> { num_in = 0; num_out = 1 }
  | Number            -> { num_in = 0; num_out = 1 }
  | Difficulty        -> { num_in = 0; num_out = 1 }
  | GasLimit          -> { num_in = 0; num_out = 1 }
  (* Stack, memory, storage and flow operations *)
  | Pop               -> { num_in = 1; num_out = 0 }
  | MLoad             -> { num_in = 1; num_out = 1 }
  | MStore            -> { num_in = 2; num_out = 0 }
  | MStore8           -> { num_in = 2; num_out = 0 }
  | SLoad             -> { num_in = 1; num_out = 1 }
  | SStore            -> { num_in = 2; num_out = 0 }
  | Jump              -> { num_in = 1; num_out = 0 }
  | JumpI             -> { num_in = 2; num_out = 0 }
  | Pc                -> { num_in = 0; num_out = 1 }
  | MSize             -> { num_in = 0; num_out = 1 }
  | Gas               -> { num_in = 0; num_out = 1 }
  | JumpDest          -> { num_in = 0; num_out = 0 }
  | Push _            -> { num_in = 0; num_out = 1 }
  (* Duplication operations *)
  | Dup n             -> { num_in = n; num_out = n + 1 }
  (* Exchange operations *)
  | Swap n            -> { num_in = n + 1; num_out = n + 1 }
  (* Log operations *)
  | Log n             -> { num_in = n + 2; num_out = 0 }
  (* System operations *)
  | Create            -> { num_in = 3; num_out = 1 }
  | Call              -> { num_in = 7; num_out = 1 }
  | CallCode          -> { num_in = 7; num_out = 1 }
  | Return            -> { num_in = 2; num_out = 0 }
  | DelegateCall      -> { num_in = 6; num_out = 0 }
  | Suicide           -> { num_in = 1; num_out = 0 }
;;

let num_in_args (x : instruction) =
  (sig_of_inst x).num_in
;;

let num_out_args (x : instruction) =
  (sig_of_inst x).num_out
;;

(* Length of an instruction: Varies only for PUSH *)

let length_of_inst i =
  Z.(match i with
        Push bs -> 1 + (of_int (List.length bs))
      | _ -> 1)
;;

type program = instruction list;;

let rec program_length (p : program) =
  Z.(match p with
        [] -> 0
      | inst :: rst ->
        (length_of_inst inst) + (program_length rst))
;;

(* @meta[measure : index_into_program]
    let measure_index_into_program (i, p : int * _) = i
   @end
*)

let rec index_into_program (i, p : word * program) =
  Z.(match p with
        [] -> Stop
      | inst :: rst ->
        if i <= 0 then inst else
          index_into_program (i - (length_of_inst inst), rst))
;;

(* Convert an instruction to a byte encoding *)

let bytes_of_inst x =
  Z.(match x with
      (* Stop and arithmetic *)
      | Stop              -> [0x00]
      | Add               -> [0x01]
      | Mul               -> [0x02]
      | Sub               -> [0x03]
      | Div               -> [0x04]
      | SDiv              -> [0x05]
      | Mod               -> [0x06]
      | SMod              -> [0x07]
      | AddMod            -> [0x08]
      | MulMod            -> [0x09]
      | Exp               -> [0x0a]
      | SignExtend        -> [0x0b]
      (* Comparison and bitwise logical operations *)
      | Lt                -> [0x10]
      | Gt                -> [0x11]
      | Slt               -> [0x12]
      | Sgt               -> [0x13]
      | Eq                -> [0x14]
      | IsZero            -> [0x15]
      | BitAnd            -> [0x16]
      | BitOr             -> [0x17]
      | BitXor            -> [0x18]
      | BitNot            -> [0x19]
      | Byte              -> [0x1a]
      (* SHA3 *)
      | SHA3              -> [0x20]
      (* Environment *)
      | Address           -> [0x30]
      | Balance           -> [0x31]
      | Origin            -> [0x32]
      | Caller            -> [0x33]
      | CallValue         -> [0x34]
      | CallDataLoad      -> [0x35]
      | CallDataSize      -> [0x36]
      | CallDataCopy      -> [0x37]
      | CodeSize          -> [0x38]
      | CodeCopy          -> [0x39]
      | GasPrice          -> [0x3a]
      | ExtCodeSize       -> [0x3b]
      | ExtCodeCopy       -> [0x3c]
      (* Block information *)
      | BlockHash         -> [0x40]
      | CoinBase          -> [0x41]
      | TimeStamp         -> [0x42]
      | Number            -> [0x43]
      | Difficulty        -> [0x44]
      | GasLimit          -> [0x45]
      (* Stack, memory, storage and flow operations *)
      | Pop               -> [0x50]
      | MLoad             -> [0x51]
      | MStore            -> [0x52]
      | MStore8           -> [0x53]
      | SLoad             -> [0x54]
      | SStore            -> [0x55]
      | Jump              -> [0x56]
      | JumpI             -> [0x57]
      | Pc                -> [0x58]
      | MSize             -> [0x59]
      | Gas               -> [0x5a]
      | JumpDest          -> [0x5b]
      | Push bs           -> (0x5f + (of_int (List.length bs))) :: bs
      (* Duplication operations *)
      | Dup n             -> [0x7f + (of_int n)]
      (* Exchange operations *)
      | Swap n            -> [0x8f + (of_int n)]
      (* Log operations *)
      | Log n             -> [0xa0 + (of_int n)]
      (* System operations *)
      | Create            -> [0xf0]
      | Call              -> [0xf1]
      | CallCode          -> [0xf2]
      | Return            -> [0xf3]
      | DelegateCall      -> [0xf4]
      | Suicide           -> [0xff])
;;

(* Some non-logical utilities *)

:shadow off

let rec list_program' (p, n : program * int) =
  match p with
    [] -> ()
  | i :: is ->
    Printf.printf "%d. %s\n" n (string_of_instruction i);
    list_program' (is, n + (Z.to_int (length_of_inst i)))
;;

let list_program (p) = list_program' (p, 0)
;;

:shadow on

