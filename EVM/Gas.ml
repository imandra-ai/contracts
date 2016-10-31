(* A formal model of the Ethereum Virtual Machine in ImandraML         *)
(* (c)Copyright Aesthetic Integration, Ltd., 2016                      *)
(* All rights reserved.                                                *)
(*                                                                     *)
(* Released under Apache 2.0 license as described in the file LICENSE. *)
(*                                                                     *)
(* Contributors:                                                       *)
(*  Grant Olney Passmore (grant@aestheticintegration.com)              *)
(*                                                                     *)

(* Base gas cost of an instruction *)

let base_cost_of_inst x =
  Z.(match x with
      (* Stop and arithmetic *)
        Stop              -> 0
      | Add               -> 3
      | Mul               -> 5
      | Sub               -> 3
      | Div               -> 5
      | SDiv              -> 5
      | Mod               -> 5
      | SMod              -> 5
      | AddMod            -> 8
      | MulMod            -> 8
      | Exp               -> 10
      | SignExtend        -> 5
      (* Comparison and bitwise logical operations *)
      | Lt                -> 3
      | Gt                -> 3
      | Slt               -> 3
      | Sgt               -> 3
      | Eq                -> 3
      | IsZero            -> 3
      | BitAnd            -> 3
      | BitOr             -> 3
      | BitXor            -> 3
      | BitNot            -> 3
      | Byte              -> 3
      (* SHA3 *)
      | SHA3              -> 30
      (* Environment *)
      | Address           -> 2
      | Balance           -> 20
      | Origin            -> 2
      | Caller            -> 2
      | CallValue         -> 2
      | CallDataLoad      -> 3
      | CallDataSize      -> 2
      | CallDataCopy      -> 3
      | CodeSize          -> 2
      | CodeCopy          -> 3
      | GasPrice          -> 2
      | ExtCodeSize       -> 20
      | ExtCodeCopy       -> 20
      (* Block information *)
      | BlockHash         -> 20
      | CoinBase          -> 2
      | TimeStamp         -> 2
      | Number            -> 2
      | Difficulty        -> 2
      | GasLimit          -> 2
      (* Stack, memory, storage and flow operations *)
      | Pop               -> 2
      | MLoad             -> 3
      | MStore            -> 3
      | MStore8           -> 3
      | SLoad             -> 50
      | SStore            -> 0
      | Jump              -> 8
      | JumpI             -> 10
      | Pc                -> 2
      | MSize             -> 2
      | Gas               -> 2
      | JumpDest          -> 1
      | Push _            -> 3
      (* Duplication operations *)
      | Dup _             -> 3
      (* Exchange operations *)
      | Swap _            -> 3
      (* Log operations *)
      | Log 0             -> 375
      | Log 1             -> 750
      | Log 2             -> 1125
      | Log 3             -> 1500
      | Log 4             -> 1875
      | Log n             -> 0 (* Unreachable *)
      (* System operations *)
      | Create            -> 32000
      | Call              -> 40
      | CallCode          -> 40
      | Return            -> 0
      | DelegateCall      -> 40
      | Suicide           -> 0)
;;

(* -- Other gas prices -- *)

let gas_DEFAULT              = Z.(1);;
let gas_MEMORY               = Z.(3);;
let gas_QUADRATICMEMDENOM    = Z.(512);;
let gas_STORAGEREFUND        = Z.(15000);;
let gas_STORAGEKILL          = Z.(5000);;
let gas_STORAGEMOD           = Z.(5000);;
let gas_STORAGEADD           = Z.(20000);;
let gas_EXPONENTBYTE         = Z.(10);;
let gas_COPY                 = Z.(3);;
let gas_CONTRACTBYTE         = Z.(200);;
let gas_CALLVALUETRANSFER    = Z.(9000);;
let gas_LOGBYTE              = Z.(8);;
let gas_TXCOST               = Z.(21000);;
let gas_TXDATAZERO           = Z.(4);;
let gas_TXDATANONZERO        = Z.(68);;
let gas_SHA3WORD             = Z.(6);;
let gas_SHA256BASE           = Z.(60);;
let gas_SHA256WORD           = Z.(12);;
let gas_RIPEMD160BASE        = Z.(600);;
let gas_RIPEMD160WORD        = Z.(120);;
let gas_IDENTITYBASE         = Z.(15);;
let gas_IDENTITYWORD         = Z.(3);;
let gas_ECRECOVER            = Z.(3000);;
let gas_STIPEND              = Z.(2300);;
let gas_CALLNEWACCOUNT       = Z.(25000);;
let gas_SUICIDEREFUND        = Z.(24000);;

