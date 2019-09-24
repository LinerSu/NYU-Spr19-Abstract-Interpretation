
open AbstractSyntaxExpressions
open Apron

type abstractOctagon = Oct.t Abstract1.t

let man = Oct.manager_alloc ()

let env =
    let var_x = Var.of_string "x" in
    let var_y = Var.of_string "y" in
    Environment.make
    [|var_x; var_y;|]
    [||]

(* environments are represented as a function of "x" and "y" only *)
type t = abstractOctagon
let leq r1 r2 = Abstract1.is_leq man r1 r2
let initialize vl = ()
let bot () = Abstract1.bottom man env
let join r1 r2 = Abstract1.join man r1 r2

let initialP () = Abstract1.top man env
    (*let tab = Parser.lincons1_of_lstring env ["x=0";"y=0";] in
    Abstract1.of_lincons_array man env tab*)

let rec transforma a = match a with
   | Num i -> string_of_int i
   | Var x -> x
   | Minus (a1,a2) -> (transforma a1) ^ "-" ^ (transforma a2)
   | Plus (a1,a2) -> (transforma a1) ^ "+" ^ (transforma a2)

let rec transformb b = match b with
   | Lt (a1,a2) -> let expr = (transforma a1) ^ "<" ^ (transforma a2) in
   let tcons = Parser.tcons1_of_string env expr in
   let arr = Tcons1.array_make env 1 in
   Tcons1.array_set arr 0 tcons; arr
   | Eq (a1,a2) -> let expr = (transforma a1) ^ "=" ^ (transforma a2) in
   let tcons = Parser.tcons1_of_string env expr in
   let arr = Tcons1.array_make env 1 in
   Tcons1.array_set arr 0 tcons; arr
   | Neq (a1,a2) -> let arr = Tcons1.array_make env 1 in
   let expr = (transforma a1) ^ "!=" ^ (transforma a2) in
   let tcons = Parser.tcons1_of_string env expr in
   Tcons1.array_set arr 0 tcons; arr
   | Gt (a1,a2) -> let expr = (transforma a1) ^ ">" ^ (transforma a2) in
   let tcons = Parser.tcons1_of_string env expr in
   let arr = Tcons1.array_make env 1 in
   Tcons1.array_set arr 0 tcons; arr
   | Nand (b1,b2) -> transformb b2 (* coarse approximation *)

let rec transformb_n b = match b with
    | Lt (a1,a2) -> let expr = (transforma a1) ^ ">=" ^ (transforma a2) in
    let tcons = Parser.tcons1_of_string env expr in
    let arr = Tcons1.array_make env 1 in
    Tcons1.array_set arr 0 tcons; arr
    | Eq (a1,a2) -> let expr = (transforma a1) ^ "!=" ^ (transforma a2) in
    let tcons = Parser.tcons1_of_string env expr in
    let arr = Tcons1.array_make env 1 in
    Tcons1.array_set arr 0 tcons; arr
    | Neq (a1,a2) -> let arr = Tcons1.array_make env 1 in
    let expr = (transforma a1) ^ "=" ^ (transforma a2) in
    let tcons = Parser.tcons1_of_string env expr in
    Tcons1.array_set arr 0 tcons; arr
    | Gt (a1,a2) -> let expr = (transforma a1) ^ "<=" ^ (transforma a2) in
    let tcons = Parser.tcons1_of_string env expr in
    let arr = Tcons1.array_make env 1 in
    Tcons1.array_set arr 0 tcons; arr
    | Nand (b1,b2) -> transformb b2 (* coarse approximation *)

let assign x a r = let var_x = Var.of_string x in
    let texpr = Parser.texpr1_of_string env (transforma a) in
    Abstract1.assign_texpr man r var_x texpr None

let test b r = Abstract1.meet_tcons_array man r (transformb b)
let nottest b r = Abstract1.meet_tcons_array man r (transformb_n b)
let stringofaP r = Format.printf "%a@." Abstract1.print r; ""
