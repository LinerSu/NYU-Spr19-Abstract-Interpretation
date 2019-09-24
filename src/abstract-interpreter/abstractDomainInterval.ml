
open AbstractSyntaxExpressions

type abstractInterval = BOT | Int of int * int | TOP

type op = Plu | Min

type cmp = LT | GT | EQ | NQ | NAND

let pleq a1 a2 = match (a1,a2) with
| (BOT,_) -> true
| (_,BOT) -> false
| (_,TOP) -> true
| (TOP,_) -> false
| Int (i1,i2), Int (p1,p2) -> p1<=i1 && i2<=p2

let rec pjoin a1 a2 = match (a1,a2) with
| (BOT,a2) -> a2
| (a1,BOT) -> a1
| (_,TOP) -> TOP
| (TOP,_) -> TOP
| (Int (i1,i2),Int (p1,p2)) -> if i1 > i2 && p1 > p2 then BOT else
    if i1 > i2 then pjoin BOT a2 else Int(min i1 p1, max i2 p2)

let psum a1 a2 oper = match (a1,a2) with
  | BOT, _ -> BOT
  | _, BOT -> BOT
  | Int (i1,i2), Int (p1,p2) -> (match oper with
    | Plu -> let low = if i1 = min_int || p1 = min_int then min_int else i1+p1
    and high = if i2 = max_int || p2 = max_int then max_int else i2+p2
    in Int (low,high)
    | Min -> let low = if p2 = min_int then
        if i1 = min_int then 0 else min_int
        else if i1 = max_int then max_int else i1-p2
    and high = if p1 = min_int then
        if i2 = max_int then 0 else min_int
        else if i2 = max_int then max_int else i2-p1
    in Int (low,high))
  | _, _ -> TOP

let stringofconst a =  match a with
  | BOT -> "_|_"
  | Int (i1,i2) -> if i1 = min_int && i2 = max_int then "T" else
  "[" ^ (if i1 = min_int then "-oo" else string_of_int i1)  ^ ", "
  ^ (if i2 = max_int then "oo" else string_of_int i2) ^ "]"
  | TOP -> "T"

(* environments are represented as a function of "x" and "y" only *)
type t = string -> abstractInterval
let leq r1 r2 = (pleq (r1 "x") (r2 "x")) &&
                (pleq (r1 "y") (r2 "y"))
let initialize vl = ()
let bot () = function x -> BOT
let join r1 r2 = function x -> pjoin (r1 x) (r2 x)
let initialP () = function x -> TOP
let rec evala a r = match a with
   | Num i -> Int (i, i)
   | Var x -> if (x="x") || (x="y") then (r x)
              else failwith "AbstractDomainInterval : undeclared variable"
   | Minus (a1,a2) -> psum (evala a1 r) (evala a2 r) Min
   | Plus (a1,a2) -> psum (evala a1 r) (evala a2 r) Plu
let assign x a r = function y -> if (x=y) then
    if r x = BOT then BOT else (evala a r)
    else (r y)
let change_Env a p r = match a with
    | Var x -> fun z -> if (z=x) then p else r z
    | _ -> r
let rec smash b1 b2 r cmp a1 a2 = (match (b1,b2) with
   | BOT, _ -> bot ()
   | _, BOT -> bot ()
   | Int _, TOP -> smash b1 (Int (min_int, max_int)) r cmp a1 a2
   | TOP, Int _ -> smash (Int (min_int, max_int)) b2 r cmp a1 a2
   | Int (i1,i2), Int (p1,p2) -> (match cmp with
        | LT -> if i1>=p2 then bot () else
        let p1' = Int (i1, min i2 (p2-1)) in
        let p2' = Int (max (i1+1) p1, p2) in
        change_Env a2 p2' (change_Env a1 p1' r)
        | GT -> if p1>=i2 then bot() else
        let p1' = Int (max i1 (p1+1), i2) in
        let p2' = Int (p1, min (i2-1) p2) in
        change_Env a2 p2' (change_Env a1 p1' r)
        | EQ -> if i2<p1 || i1>p2 then bot() else
        let p1' = Int (max i1 p1, min i2 p2) in
        let p2' = Int (max i1 p1, min i2 p2) in
        change_Env a2 p2' (change_Env a1 p1' r)
        | NQ ->
        let p1' = pjoin (Int (i1, min i2 p2)) (Int (max i1 p2, i2)) in
        let p2' = pjoin (Int (p1, min i1 p1)) (Int (max i2 p2, p2)) in
        change_Env a2 p2' (change_Env a1 p1' r)
        | NAND -> r
        )
   | _, _ -> r)
let rec smash_n b1 b2 r cmp a1 a2 = (match (b1,b2) with
  | BOT, _ -> bot ()
  | _, BOT -> bot ()
  | Int _, TOP -> smash_n b1 (Int (min_int, max_int)) r cmp a1 a2
  | TOP, Int _ -> smash_n (Int (min_int, max_int)) b2 r cmp a1 a2
  | Int (i1,i2), Int (p1,p2) -> (match cmp with
       | LT -> if i1>=p2 then r else
       let p1' = Int (min i2 p2, i2) in
       let p2' = Int (p1, max (i1) p1) in
       change_Env a2 p2' (change_Env a1 p1' (bot()))
       | GT -> if p1>=i2 then r else
       let p1' = Int (i1, max i1 (p1)) in
       let p2' = Int (min (i2) p2, p2) in
       change_Env a2 p2' (change_Env a1 p1' (bot()))
       | EQ -> if i2<p1 || i1>p2 then r else
       let p1' = pjoin (Int (i1, min i2 p2)) (Int (max i1 p2, i2)) in
       let p2' = pjoin (Int (p1, min i1 p1)) (Int (max i2 p2, p2)) in
       change_Env a2 p2' (change_Env a1 p1' (bot()))
       | NQ ->
       let p1' = Int (max i1 p1, min i2 p2) in
       let p2' = Int (max i1 p1, min i2 p2) in
       change_Env a2 p2' (change_Env a1 p1' (bot()))
       | NAND -> r
       )
  | _, _ -> r)
let rec test b r = match b with
   | Lt (a1,a2) -> smash (evala a1 r) (evala a2 r) r LT a1 a2
   | Eq (a1,a2) -> smash (evala a1 r) (evala a2 r) r EQ a1 a2
   | Neq (a1,a2) -> smash (evala a1 r) (evala a2 r) r NQ a1 a2
   | Gt (a1,a2) -> smash (evala a1 r) (evala a2 r) r GT a1 a2
   | Nand (b1,b2) -> test b2 r (* coarse approximation *)
let nottest b r = match b with
   | Lt (a1,a2) -> smash_n (evala a1 r) (evala a2 r) r LT a1 a2
   | Eq (a1,a2) -> smash_n (evala a1 r) (evala a2 r) r EQ a1 a2
   | Neq (a1,a2) -> smash_n (evala a1 r) (evala a2 r) r NQ a1 a2
   | Gt (a1,a2) -> smash_n (evala a1 r) (evala a2 r) r GT a1 a2
   | Nand (b1,b2) -> r (* coarse approximation *)
let stringofaP r = "x=" ^ (stringofconst (r "x")) ^ ", y=" ^ (stringofconst (r "y"))
