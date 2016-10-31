(* A formal model of the Ethereum Virtual Machine in ImandraML         *)
(* (c)Copyright Aesthetic Integration, Ltd., 2016                      *)
(* All rights reserved.                                                *)
(*                                                                     *)
(* Released under Apache 2.0 license as described in the file LICENSE. *)
(*                                                                     *)
(* Contributors:                                                       *)
(*  Grant Passmore (grant@aestheticintegration.com)                    *)
(*                                                                     *)

(* Let's verify some basic facts about the EVM *)

lemma _ (s,w) =
 Z.(s.pc < program_length s.program
    && s.gas > 3
    && stack_size s < 1024
     ==>
    stack_top ((do_inst (s, Push [w]))) = Some w)
;;

lemma _ (s,w) =
 Z.(s.pc + 2 < program_length s.program
    && s.gas > 6
    && stack_size s < 1024
     ==>
     let s1 = do_inst (s, Push [w]) in
     let s2 = do_inst (s1, Pop) in
     s2.stack = s.stack)
;;

(* Let's introduce a predicate for being non-exceptionally poised to
    execute a given instruction. *)

let well_poised_inst (s, inst) =
  s.pc < program_length(s.program)
  && Z.(base_cost_of_inst(inst) <= s.gas)
  && num_in_args(inst) <= List.length s.stack 
  && List.length s.stack - num_in_args(inst) + num_out_args(inst) <= 1024
;;

(* Now, let's prove functional correctness of our instruction set. *)

lemma[rw] inst_correct_Add (s, inst) =
 Z.(well_poised_inst(s, inst)
    && inst = Add
       ==>
       let x = List.hd s.stack in
       let y = List.hd (List.tl s.stack) in
       let s1 = do_inst (s, inst) in
       List.hd s1.stack = u256 (x + y))
;;

lemma[rw] inst_correct_Sub (s, inst) =
 Z.(well_poised_inst(s, inst)
    && inst = Sub
       ==>
       let x = List.hd s.stack in
       let y = List.hd (List.tl s.stack) in
       let s1 = do_inst (s, inst) in
       List.hd s1.stack = u256 (x - y))
;;

(* etc.! *)
