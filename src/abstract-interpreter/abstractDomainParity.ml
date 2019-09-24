(* file abstractDomainParity.ml  © P. Cousot 2018 *)

open AbstractSyntaxExpressions

type abstractParity = BOT | ODD | EVEN | TOP

let pleq a1 a2 = match (a1,a2) with
| (BOT,_) -> true
| (_,BOT) -> false
| (_,TOP) -> true
| (TOP,_) -> false
| (a1, a2) -> (a1=a2)

let pjoin a1 a2 = match (a1,a2) with
| (BOT,a2) -> a2
| (a1,BOT) -> a1
| (_,TOP) -> TOP
| (TOP,_) -> TOP
| (a1, a2) -> if (a1=a2) then a1 else TOP

let psum a1 a2 = match (a1,a2) with
  | BOT, _ -> BOT
  | _, BOT -> BOT
  | ODD, EVEN -> ODD
  | EVEN, ODD -> ODD
  | EVEN, EVEN -> EVEN
  | ODD, ODD -> EVEN
  | _, _ -> TOP

let stringofparity a =  match a with
  | BOT -> "_|_"
  | ODD -> "o"
  | EVEN -> "e"
  | TOP -> "T"

(* environments are represented as a function of "x" and "y" only *)
type t = string -> abstractParity
let leq r1 r2 = (pleq (r1 "x") (r2 "x")) &&
                (pleq (r1 "y") (r2 "y"))
let initialize vl = ()
let bot () = function x -> BOT
let join r1 r2 = function x -> pjoin (r1 x) (r2 x)
let initialP () = function x -> EVEN
let rec evala a r = match a with
   | Num i -> if (i mod 2 = 0) then EVEN else ODD
   | Var x -> if (x="x") || (x="y") then (r x)
              else failwith "AbstractDomainParity : undeclared variable"
   | Minus (a1,a2) -> psum (evala a1 r) (evala a2 r)
   | Plus (a1,a2) -> psum (evala a1 r) (evala a2 r)
let assign x a r = function y -> if (x=y) then
    if r x = BOT then BOT else (evala a r)
    else (r y)
let smash p1 p2 r = (match (p1,p2) with
   | BOT, _ -> bot ()
   | _, BOT -> bot ()
   | _, _ -> r)
let rec test b r = match b with
   | Lt (a1,a2) -> smash (evala a1 r) (evala a2 r) r
   | Eq (a1,a2) -> (match (evala a1 r), (evala a2 r) with
                   | BOT, _ -> bot ()
                   | _, BOT -> bot ()
                   | ODD, EVEN -> bot ()
                   | EVEN, ODD -> bot ()
                   | _, _ -> r)
   | Neq (a1,a2) -> smash (evala a1 r) (evala a2 r) r
   | Gt (a1,a2) -> smash (evala a1 r) (evala a2 r) r
   | Nand (b1,b2) -> test b2 r (* coarse approximation *)
let nottest b r = match b with
   | Lt (a1,a2) -> smash (evala a1 r) (evala a2 r) r
   | Eq (a1,a2) -> smash (evala a1 r) (evala a2 r) r
   | Neq (a1,a2) -> smash (evala a1 r) (evala a2 r) r
   | Gt (a1,a2) -> smash (evala a1 r) (evala a2 r) r
   | Nand (b1,b2) -> r (* coarse approximation *)
let stringofaP r = "x=" ^ (stringofparity (r "x")) ^ ", y=" ^ (stringofparity (r "y"))
