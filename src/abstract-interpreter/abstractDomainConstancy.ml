
open AbstractSyntaxExpressions

type abstractConstancy = BOT | Int of int | TOP

type op = Plu | Min

type cmp = LT | GT | EQ | NQ | NAND

let pleq a1 a2 = match (a1,a2) with
| (BOT,_) -> true
| (_,BOT) -> false
| (_,TOP) -> true
| (TOP,_) -> false
| (Int a1, Int a2) -> a1<=a2

let pjoin a1 a2 = match (a1,a2) with
| (BOT,a2) -> a2
| (a1,BOT) -> a1
| (_,TOP) -> TOP
| (TOP,_) -> TOP
| (Int a1, Int a2) -> if (a1=a2) then Int a1 else TOP

let psum a1 a2 oper = match (a1,a2) with
  | BOT, _ -> BOT
  | _, BOT -> BOT
  | Int i, Int p -> (match oper with
    | Plu -> Int (i+p)
    | Min -> Int (i-p))
  | _, _ -> TOP

let stringofconst a =  match a with
  | BOT -> "_|_"
  | Int i -> string_of_int i
  | TOP -> "T"

(* environments are represented as a function of "x" and "y" only *)
type t = string -> abstractConstancy
let leq r1 r2 = (pleq (r1 "x") (r2 "x")) &&
                (pleq (r1 "y") (r2 "y"))
let initialize vl = ()
let bot () = function x -> BOT
let join r1 r2 = function x -> pjoin (r1 x) (r2 x)
let initialP () = function x -> Int 0
let rec evala a r = match a with
   | Num i -> Int i
   | Var x -> if (x="x") || (x="y") then (r x)
              else failwith "AbstractDomainConstancy : undeclared variable"
   | Minus (a1,a2) -> psum (evala a1 r) (evala a2 r) Min
   | Plus (a1,a2) -> psum (evala a1 r) (evala a2 r) Plu
let assign x a r = function y -> if (x=y) then
    if r x = BOT then BOT else (evala a r)
    else (r y)
let smash p1 p2 r cmp = (match (p1,p2) with
   | BOT, _ -> bot ()
   | _, BOT -> bot ()
   | Int i, Int p -> (match cmp with
        | LT -> if i<p then r else bot()
        | GT -> if i>p then r else bot()
        | EQ -> if i=p then r else bot()
        | NQ -> if i!=p then r else bot()
        | NAND -> r
        )
   | _, _ -> r)
let smash_n p1 p2 r cmp = (match (p1,p2) with
  | BOT, _ -> bot ()
  | _, BOT -> bot ()
  | Int i, Int p -> (match cmp with
       | LT -> if i<p then bot() else r
       | GT -> if i>p then bot() else r
       | EQ -> if i=p then bot() else r
       | NQ -> if i!=p then bot() else r
       | NAND -> bot()
       )
  | _, _ -> r)
let rec test b r = match b with
   | Lt (a1,a2) -> smash (evala a1 r) (evala a2 r) r LT
   | Eq (a1,a2) -> smash (evala a1 r) (evala a2 r) r EQ
   | Neq (a1,a2) -> smash (evala a1 r) (evala a2 r) r NQ
   | Gt (a1,a2) -> smash (evala a1 r) (evala a2 r) r GT
   | Nand (b1,b2) -> test b2 r (* coarse approximation *)
let nottest b r = match b with
   | Lt (a1,a2) -> smash_n (evala a1 r) (evala a2 r) r LT
   | Eq (a1,a2) -> smash_n (evala a1 r) (evala a2 r) r EQ
   | Neq (a1,a2) -> smash_n (evala a1 r) (evala a2 r) r NQ
   | Gt (a1,a2) -> smash_n (evala a1 r) (evala a2 r) r GT
   | Nand (b1,b2) -> r (* coarse approximation *)
let stringofaP r = "x=" ^ (stringofconst (r "x")) ^ ", y=" ^ (stringofconst (r "y"))
