
open AbstractSyntaxExpressions

let rec gcd u v =
  if v <> 0 then (gcd v (u mod v))
  else (abs u)

let lcm m n =
  match m, n with
  | 0, _ | _, 0 -> 0
  | m, n -> abs (m * n) / (gcd m n)

type abstractCongruence = BOT | TOP | CONG of int * int

type op = Plu | Min

type cmp = LT | GT | EQ | NQ | NAND

let pleq a1 a2 = match (a1,a2) with
| (BOT,_) -> true
| (_,BOT) -> false
| (_,TOP) -> true
| (TOP,_) -> false
| (CONG (c1,m1), CONG (c2,m2)) -> if m2!=0 then (c1 - c2) mod m2 = 0 else c1 - c2 = 0

let pjoin a1 a2 = match (a1,a2) with
| (BOT,a2) -> a2
| (a1,BOT) -> a1
| (_,TOP) -> TOP
| (TOP,_) -> TOP
| (CONG (c1,m1), CONG (c2,m2)) -> let m' = gcd (gcd m1 m2) (abs (c1 - c2)) in CONG (c1, m')

let psum a1 a2 oper = match (a1,a2) with
  | BOT, _ -> BOT
  | _, BOT -> BOT
  | CONG (c1,m1), CONG (c2,m2) -> (* only allow operate with constants *)
    (match oper with
  	| Plu -> CONG (c1+c2, gcd m1 m2)
  	| Min -> CONG (c1-c2, gcd m1 m2)
  	)
  | _, _ -> TOP

let stringofparity a =  match a with
  | BOT -> "_|_"
  | CONG (c,m) -> (string_of_int c) ^ "+" ^ (string_of_int m) ^ "Z"
  | TOP -> "T"

(* environments are represented as a function of "x" and "y" only *)
type t = string -> abstractCongruence
let leq r1 r2 = (pleq (r1 "x") (r2 "x")) &&
                (pleq (r1 "y") (r2 "y"))
let initialize vl = ()
let bot () = function x -> BOT
let join r1 r2 = function x -> pjoin (r1 x) (r2 x)
let initialP () = function x -> CONG (0,0)
let rec evala a r = match a with
   | Num i -> CONG (i,0)
   | Var x -> if (x="x") || (x="y") then (r x)
              else failwith "AbstractDomainCongruence : undeclared variable"
   | Minus (a1,a2) -> psum (evala a1 r) (evala a2 r) Min
   | Plus (a1,a2) -> psum (evala a1 r) (evala a2 r) Plu
let assign x a r = function y -> if (x=y) then
    if r x = BOT then BOT else (evala a r)
    else (r y)
let smash p1 p2 r cmp = (match (p1,p2) with
   | BOT, _ -> bot ()
   | _, BOT -> bot ()
   | CONG (c1,m1), CONG (c2,m2) -> (match cmp with
        | LT -> if m1<m2 || (m1=m2 && c1 < c2) then r else bot()
        | GT -> if m1>m2 || (m1=m2 && c1 > c2) then r else bot()
        | EQ -> if m1=m2 && c1=c2 then r else bot()
        | NQ -> if m1!=m2 || (m1=m2 && c1 != c2) then r else bot()
        | NAND -> r
        )
   | _, _ -> r)
let smash_n p1 p2 r cmp = (match (p1,p2) with
  | BOT, _ -> bot ()
  | _, BOT -> bot ()
  | CONG (c1,m1), CONG (c2,m2) -> (match cmp with
       | LT -> if m1<m2 || (m1=m2 && c1 < c2) then bot() else r
       | GT -> if m1>m2 || (m1=m2 && c1 > c2) then bot() else r
       | EQ -> if m1=m2 && c1=c2 then bot() else r
       | NQ -> if m1!=m2 || (m1=m2 && c1 != c2) then bot() else r
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
let stringofaP r = "x=" ^ (stringofparity (r "x")) ^ ", y=" ^ (stringofparity (r "y"))
