(* Some experiments with memory *)

let test_1 () =
  Z.(let m = { data = [1;2]; cur_size = 2; peek = 0 } in
     set_mem(96, 100, m))
;;

test_1 ();;

let test_2 () =
 Z.(let m = { data = [1;2;3;]; cur_size = 3; peek = 2 } in
    let m = set_mem(32, 100, m) in
    get_mem(1024,m))
;;

test_2 ();;

(* incorrect *)
set_mem <-- (128, 3, {data = []; cur_size = 0; peek = 0})
set_mem --> {data = [0; 0; 0; 0; 3]; cur_size = 5; peek = 0}
set_mem <-- (160, 6, {data = [0; 0; 0; 0; 3]; cur_size = 5; peek = 3})
set_mem --> {data = [0; 0; 0; 0; 3]; cur_size = 6; peek = 3}


let test_3 () =
 Z.(let m = { data = [0;0;0;0;3]; cur_size = 5; peek = 3 } in
    set_mem(160, 6, m))
;;


