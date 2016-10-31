(* A formal model of the Ethereum Virtual Machine in ImandraML         *)
(* (c)Copyright Aesthetic Integration, Ltd., 2016                      *)
(* All rights reserved.                                                *)
(*                                                                     *)
(* Released under Apache 2.0 license as described in the file LICENSE. *)
(*                                                                     *)
(* Contributors:                                                       *)
(*  Grant Olney Passmore (grant@aestheticintegration.com)              *)
(*                                                                     *)

(* Raising exceptions and exiting peacefully     *)
(* Note: See Environment for exit explanations  *)

let raise_exception (s, e : state * exit_explanation) =
  let r = { e_flag = true;
            e_gas  = s.gas;
            e_data = [];
            e_desc = e } in
  { s with halted = Some (Exception r) }
;;

let peaceful_exit (s, e, mem : state * exit_explanation * word list) =
  let r = { e_flag = false;
            e_gas  = s.gas;
            e_data = mem;
            e_desc = e } in
  { s with halted = Some (Exit r) }
;;

(* If it's OK to extend memory as specified, then we return
     (Some g), where g is our new gas after the extension fee is taken.

   If it's not OK to extend memory, then we return None.
     Gas must be zeroed / Out_of_memory exception must be raised by caller. *)

type mem_extn =
  { new_size : word;
    new_gas  : word }
;;

let mem_extend_ok (cur_gas, cur_size, start, sz) =
  Z.(if sz > 0 then
       let old_size = cur_size in
       let old_total_fee = (old_size * gas_MEMORY +
                            (old_size * old_size) / gas_QUADRATICMEMDENOM) in
       let new_size = ceiling(start + sz, 32) in
       let new_total_fee = (new_size * gas_MEMORY +
                            (new_size * new_size) / gas_QUADRATICMEMDENOM) in
       if old_total_fee < new_total_fee then
         let mem_fee = new_total_fee - old_total_fee in
         if cur_gas < mem_fee then
           None
         else
           let g = cur_gas - mem_fee in
           Some { new_size = new_size; new_gas = g }
       else Some { new_size = new_size; new_gas = cur_gas }
     else Some { new_size = cur_size; new_gas = cur_gas })
;;

(* Is a data_copy operation OK? If so, compute the remaining gas. *)

let data_copy_ok (cur_gas, sz) =
  Z.(if sz > 0 then
       let fee = gas_COPY * ceiling(sz, 32) in
       if cur_gas < fee then
         None
       else Some (cur_gas - fee)
     else Some cur_gas)
;;

 
