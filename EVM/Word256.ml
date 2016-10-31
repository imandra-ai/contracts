(* A formal model of the Ethereum Virtual Machine in ImandraML         *)
(* (c)Copyright Aesthetic Integration, Ltd., 2016                      *)
(* All rights reserved.                                                *)
(*                                                                     *)
(* Released under Apache 2.0 license as described in the file LICENSE. *)
(*                                                                     *)
(* Contributors:                                                       *)
(*  Grant Olney Passmore (grant@aestheticintegration.com)              *)
(*                                                                     *)

(* 256-bit word arithmetic for Ethereum *)

let fix_unsigned (x, bit_width) =
  Z.(x mod (pow 2 bit_width))
;;

let fix_signed (x, bit_width) =
  Z.(let tmp = x mod (pow 2 bit_width) in
     if tmp < pow 2 Int.(bit_width - 1) then
       tmp
     else (tmp - (pow 2 bit_width)))
;;

type byte = Z.t;;

let u8 (x : Z.t) : byte =
  fix_unsigned (x, 8)
;;

let s8 (x : Z.t) : byte =
  fix_signed (x, 8)
;;

type word = Z.t;;

let u256 (x : Z.t) : word =
  fix_unsigned (x, 256)
;;

let s256 (x : Z.t) : word =
  fix_signed (x, 256)
;;

let fix_word (x : Z.t) : word =
  u256 x
;;

let valid_word (x : Z.t) =
  u256 x = x
;;

let max_u256 : word =
  Z.((pow 2 (to_int 256)) - 1)
;;

let pow_to_256 = Z.(pow 2 (to_int 256))
;;

let pow_2_255 = Z.(pow 2 (to_int 255))
;;

let word_of_bool b =
  if b then Z.one else Z.zero
;;

type fun_id = Z.t;;

:reasoner bits

lemma[rw] lognot_is_zero_elim (x) =
  Z.((lognot x = 0) = (x = -1))
;;

lemma[rw] lognot_is_minus_one_elim (x : Z.t) =
  Z.((lognot x = -1) = (x = 0))
;;

lemma[rw] u256_idempotent (x : Z.t) =
  u256 (u256 x) = u256 x
;;

:disable u256

lemma[rw] u256_lognot_zero_cases (x) =
 Z.(u256 x = x &&
    u256(-x - 1) = (-x - 1)
      ==>
    (u256 (lognot x) = 0)
      = (x = -1))
;;

:disable u256_lognot_zero_cases

type address = Z.t;;

let rec word_of_bytes' (bytes, coeff, res) =
  match bytes with
    [] -> res
  | b :: bs ->
    Z.(let n = b * coeff + res in
       word_of_bytes' (bs, coeff * 256, n))
;;

let word_of_bytes (bytes) =
  Z.(word_of_bytes' (bytes, 1, 0))
;;

lemma[rw] word_of_bytes_single (bytes) =
  List.length bytes = 1
   ==>
   word_of_bytes bytes = List.hd bytes
;;

let get_byte (word, i) =
  Z.(let n = shift_right word Int.(8 * i) in
     logand n 255)
;;

lemma[rw] get_byte_grounded (word) =
  Z.(0 <= word && word <= 255
     ==>
       get_byte(word, to_int 0) = word)
;;

(* @meta[measure : mk_32_bytes_aux]
    let measure_mk_32_bytes_aux (word, shift : _ * int) =
      256 - shift
   @end
*)

let rec mk_32_bytes_aux (word, shift) =
  Z.(if Int.(shift >= 256) then []
     else
       let byte = u8 (word asr shift) in
       byte :: mk_32_bytes_aux (word, Int.(shift + 8)))
;;

let mk_32_bytes (word) =
  mk_32_bytes_aux (word, 0)
;;

:disable word_of_bytes
:disable mk_32_bytes

(* @meta[measure : bits_of_word_aux]
    let measure_bits_of_word_aux (word, k : _ * int) =
      k + 1
   @end
 *)

let rec bits_of_word_aux (word, k) =
  if k < 0 then []
  else
    let b = Z.(if testbit word k then 1 else 0) in
    b :: (bits_of_word_aux (word, k-1))
;;

let bits_of_word (word) =
  let num_bits = Z.numbits word in
  bits_of_word_aux (word, num_bits - 1)
;;

let rec word_of_bits_aux (bits, coeff) =
  Z.(match bits with
       [] -> 0
     | b :: bs ->
        let k = if b = 1 then coeff else 0 in
        k + word_of_bits_aux(bs, 2 * coeff))
;;

let word_of_bits (bits) =
  word_of_bits_aux (List.rev bits, Z.(1))
;;

let sign_extend (sint, size) =
  fix_signed (sint, size)
;;

let sign_extend_from_bit (word, sign_bit) =
  let i = Z.(signed_extract word (to_int 0) (to_int sign_bit)) in
  sign_extend (i, 256)
;;
