(* A formal model of the Ethereum Virtual Machine in ImandraML         *)
(* (c)Copyright Aesthetic Integration, Ltd., 2016                      *)
(* All rights reserved.                                                *)
(*                                                                     *)
(* Released under Apache 2.0 license as described in the file LICENSE. *)
(*                                                                     *)
(* Contributors:                                                       *)
(*  Grant Passmore (grant@aestheticintegration.com)                    *)
(*                                                                     *)

(* Example: Analysing a simple registry smart contract *)

:indent on
:adts on

(* Example contract
      from
    https://ethereum.gitbooks.io/frontier-guide/content/opcodes,_costs,_and_gas.html

   Note: Ethereum documentation uses NOT (i.e., BitNot) for the next
         instruction, but that's wrong! We need to use IsZero here. Why?
         Observe that BitNot(x) = 0 iff x = -1 ... Not what we want!
*)

let c1 =
  Z.([ Push [0];
       CallDataLoad;
       SLoad;
       IsZero;
       Push [9];
       JumpI;
       Stop;
       JumpDest;
       Push [32];
       CallDataLoad;
       Push [0];
       CallDataLoad;
       SStore ])
;;

let s1 = init_state Z.([],
                       [],
                       c1,
                       100,
                       mk_basic_msg ({ fun_selector = None;
                                       call_args    = [54; 2020202020] }),
                       empty_ext);;

(* Let's run the machine for 15 steps with symbolic storage *)

let run_15_sym (storage, ext) = run({s1 with storage = storage;
                                             ext     = ext},
                                    15);;

(* Now, what are its possible behaviours?
   We do a region decomposition to see. *)

:decompose run_15_sym

(* Let's make gas and storage symbolic *)

let run_15_sym_gas (gas, storage) = run({s1 with gas = gas;
                                                 storage = storage},
                                        15);;

:decompose run_15_sym_gas

(* Notice that now examines all the possible ways we can run out of gas!
   So, let's add an assumption that we have at least, e.g., 100 gas. *)

let gas_lb (gas, storage : word * storage) = gas >= Z.(100);;

:decompose run_15_sym_gas assuming gas_lb

(* Let's prove some theorems. For fun, we'll use a version with only symbolic storage. *)

let run_15_sym_storage (storage) = run({s1 with storage = storage;}, 15);;

(* Next, let's verify the name registry bytecode w.r.t. its spec *)

theorem c1_correct_1 (x, k, v, v_new : storage * _ * _ * _) =
 Z.(valid_word k && valid_word v_new &&
    get_storage(k,x) = v && v <> 0)
   ==>
   let init_state = { s1 with storage = x;
                              msg = { s1.msg with
                                      msg_data = { fun_selector = None;
                                                   call_args    = [k; v_new] } } } in
   get_storage(k, (run (init_state, 15)).storage) = v
;;

theorem c1_correct_2 (x, k, v : storage * _ * _) =
 Z.(valid_word k && valid_word v &&
    get_storage(k,x) = 0)
   ==>
   let init_state = { s1 with storage = x;
                              msg = { s1.msg with
                                      msg_data = { fun_selector = None;
                                                   call_args    = [k; v] } } }
   in
   get_storage(k, (run(init_state, 15)).storage) = v
;;

(* Both goals above are proved automatically. *)

(* Now, some nice examples of a false goals *)

theorem c1_bad_1 (x, k, v : storage * _ * _) =
 Z.(get_storage(k,x) = 0)
  ==>
  let init_state = {s1 with storage = x;
                            msg = { s1.msg with
                                    msg_data = { fun_selector = None;
                                                 call_args    = [v; k] } } } in
  get_storage(k, (run(init_state, 15)).storage) = v
;;

(* To see the subgoals left by the failed proof attempt,
   use ':s' --

# :s
2 subgoals:

 k : int
 v : int
 x : storage_entry list
 get_storage(k, x) = 0
 get_storage(v, x) = 0
|--------------------------------------------------------------------------
 get_storage(k, set_storage(v, k, x)) = v

 k : int
 v : int
 x : storage_entry list
 get_storage(k, x) = 0
 get_storage(v, x) <> 0
|--------------------------------------------------------------------------
 0 = v

*)

(* And another false goal *)

theorem c1_bad_2 (x, k, v : storage * _ * _) =
 Z.(get_storage(k,x) = 0)
   ==>
   let init_state = {s1 with storage = x;
                             msg     = { s1.msg with
                                         msg_data = { fun_selector = None;
                                                      call_args    = [k; v] } } } in
   get_storage(k, (run(init_state, 6)).storage) = v
;;

(* Let's look at the remaining subgoal, which is obviously false!:

# :s
1 subgoal:

 k : int
 v : int
 x : storage_entry list
 get_storage(k, x) = 0
|--------------------------------------------------------------------------
 0 = v

*)

(* And another where gas is too low! *)

theorem c1_bad_3 (x, k, v : storage * _ * _) =
 Z.(valid_word k && valid_word v &&
    get_storage(k,x) = 0 && v > 0
     ==>
     let init_state = {s1 with storage = x;
                               gas     = 80;
                               msg     = { s1.msg with
                                           msg_data = { fun_selector = None;
                                                        call_args    = [k; v] } } } in
     get_storage(k, (run(init_state, to_int 15)).storage) = v)
;;

(* Let's inspect the failure...
   Notice: Our subgoal tries to establish the hyp (v > 0) is always false!

# :s
1 subgoal:

 k : int
 v : int
 x : storage_entry list
 get_storage(k, x) = 0
 u256(k) = k
 u256(v) = v
|--------------------------------------------------------------------------
 v <= 0

*)

