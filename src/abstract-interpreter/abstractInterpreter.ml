
open AbstractSyntax
open AbstractDomain
open AbstractTree

let leq x y = match x, y with
    | (While (b, sb, (at,atP,af,afP,es,br,brP))), (While (b', sb', (at',atP',af',afP',es',br',brP')))
        -> (leq atP atP') && (leq afP afP') && (leq brP brP')
    | _,_ -> invalid_arg "Invalid arguments for leq"

let rec lfp f x = let x' = f x in
	if leq x' x then x' else lfp f x'

let rec fWh r0 x = match x with
    | While (b, sb, (at,xl,af,afP,es,br,brP)) -> let sb' = abstractInterpreter sb (test b xl) in
        let afP' = property_after sb' and brP' = property_break sb' in
        let atP = join r0 afP' in
        let afP = join (nottest b atP) brP' in
            While (b, sb', (at,atP,af,afP,es,br,bot ()))
    | _ -> invalid_arg "Invalid arguments for F"
and abstractInterpreter stmt r0 = match stmt with
	| Prog (sl, (at,atP,af,afP,es,br,brP)) -> let sl',atP',afP',brP' = asbtractInterpreteStmtlist sl r0 in
		Prog (sl', (at,atP',af,afP',es,br,brP'))
	| Stmtlist (sl, (at,atP,af,afP,es,br,brP)) -> let sl',atP',afP',brP' = asbtractInterpreteStmtlist sl r0 in
		Stmtlist (sl', (at,atP',af,afP',es,br,brP'))
	| Assign (v, a, (at,atP,af,afP,es,br,brP)) -> let afP' = assign v a r0 in Assign (v, a, (at,r0,af,afP',es,br,bot()))
    | Emptystmt (at,atP,af,afP,es,br,brP) -> Emptystmt (at,r0,af,r0,es,br,bot())
    | If (b, st, (at,atP,af,afP,es,br,brP)) -> let st' = abstractInterpreter st (test b r0) in
    	let afP' = property_after st' and brP' = property_break st' and afP'' = nottest b r0 in
    	If (b, st', (at,r0,af,(join afP' afP''),es,br,brP'))
    | Ifelse (b, st, se, (at,atP,af,afP,es,br,brP)) ->
    let st' = abstractInterpreter st (test b r0) and se' = abstractInterpreter se (nottest b r0) in
    	let afpt' = property_after st' and afpe' = property_after se' in
    	let brPt' = property_break st' and brPe' = property_break se' in
    	Ifelse (b, st', se', (at,r0,af,(join afpt' afpe'),es,br,(join brPt' brPe')))
    | Break (at,atP,af,afP,es,br,brP) -> Break (at,r0,af,bot(),es,br,r0)
    | While (b, sb, (at,atP,af,afP,es,br,brP)) ->
        let wbot = While (b, sb, (at,bot (),af,bot (),es,br,bot ())) in
        let fix_x = lfp (fWh r0) wbot in
        (match fix_x with
        | While (b', sb', (at',atP',af',afP',es',br',brP')) ->
            let sb'' = abstractInterpreter sb' (test b' atP') in
    	       While (b', sb'', (at',atP',af',afP',es',br',brP'))
        | _ -> invalid_arg "Invalid arguments after fix")
and asbtractInterpreteStmtlist sl r0 =
	match sl with
		| [] -> [],r0,r0,(bot ())
		| [s] -> let s' = abstractInterpreter s r0 in [s'], property_at s', property_after s', property_break s'
		| s :: slf (* trees in inverse order *) -> let sl',atP',afP',brP' = asbtractInterpreteStmtlist slf r0 in
			let s' = abstractInterpreter s afP' in
				s' :: sl', atP', property_after s', (join (property_break s') brP')
