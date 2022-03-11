(* Genealogy module body *)

(* 
Aluno 1: Francisco Gouveia 57488
Aluno 2: ????? mandatory to fill

Comment:

?????????????????????????
?????????????????????????
?????????????????????????
?????????????????????????
?????????????????????????
?????????????????????????

*)

(*
0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789
   100 columns
*)


(* COMPILATION - How to build this module (used by Mooshak))
         ocamlc -c Genealogy.mli Genealogy.ml
*)


(* AUXILIARY BASIC FUNCTIONS - you can add more *)

let rec uniq l =
	match l with
	|  [] -> []
	| [x] -> [x]
	| x::y::xs ->
		if x = y then uniq (y::xs)
		else x::uniq (y::xs)

let clean l = (* removes repetitions *)
	uniq (List.sort compare l)

let len =
	List.length

let map =
	List.map

let filter =
	List.filter

let mem =
	List.mem

let flatMap f l =
	List.flatten (map f l)

let partition =
	List.partition

let exists =
	List.exists

let for_all =
	List.for_all

let cFlatMap f l =
	clean (flatMap f l)

let union l1 l2 =
	clean (l1 @ l2)

let inter l1 l2 =
	filter (fun x -> mem x l2) l1

let diff l1 l2 =
	filter (fun a -> not (mem a l2)) l1



(* TYPES *)

type item = string * string list
type repository = item list

type aTree = ANil | ANode of string * aTree * aTree
type dTree = DNil | DNode of string * dTree list


(* EXAMPLES - you can add more *)
let example = [
           ("a", ["f";"g";]);
           ("b", ["f";"h"]);
           ("c", ["h";"i"]);
           ("f", ["g"; "j"]);
           ("g", ["j"]);
           ("h", []);
           ("i", []);
           ("j", [])
          ]
(* BASIC REPOSITORY FUNCTIONS - you can add more *)

let size rep = (* number of individuals *)
	len rep

let all1 rep = (* all the individuals *)
	map fst rep

let all2 rep = (* all the children (of anyone) *)
	cFlatMap snd rep

let roots rep = (* individuals without any parents *)
	diff (all1 rep) (all2 rep)

let inners rep = (* individuals with children *)
	let xs = filter (fun (p,cs) -> cs <> []) rep in
		all1 xs

let leaves rep = (* individuals without any children *)
	let xs = filter (fun (p,cs) -> cs = []) rep in
		all1 xs

let cut1 rep l = (* partition based on first component of the repository *)
	partition (fun (p,cs) -> mem p l) rep

let cut2 rep l = (* partition based on second component of the repository *)
	partition (fun (p,cs) -> inter cs l <> []) rep

let cut rep = (* partition -> (root pairs, rest pairs) *)
	cut1 rep (roots rep)

let children rep l = (* get all the children of the list l *)
	let (a,b) = cut1 rep l in
		all2 a

let rec parents rep l = (* get all the parents of the list l *)
	let (a,b) = cut2 rep l in
		all1 a



		
(* FUNCTION height *)

let rec height rep = 
		match rep with 
		[] -> 0
		|x::xs -> let (p,c) = cut rep in 1 + height c
	
(* FUNCTION makeATree *)

let rec makeATree rep a =
	let asc = parents rep [a] in
	match asc with
	| [] -> ANode(a,ANil,ANil)
	| [p] -> ANode(a, (makeATree rep p), ANil)
	| [p1;p2] -> ANode(a, (makeATree rep p1), (makeATree rep p2))
	| x::y::xs -> failwith "makeATree: bad argument"
		
(* FUNCTION makeDTree *)

let rec makeDTree rep a =

	let childrens = children rep [a] in
	match childrens with
	| [] -> DNode(a,[])
	| [x] -> DNode(a,[makeDTree rep x])
	| x::xs -> DNode(a, (makeDTree rep x) :: (makeDTreeChilds rep xs))
	and 
	makeDTreeChilds rep childs = 
		match childs with
		|[] ->  []
		|x::xs -> (makeDTree rep x) :: (makeDTreeChilds rep xs)
	

;;
(* FUNCTION merge *)
let rec repLess rep a =
	match rep with
	[] -> []
	|(x,xs)::ys-> if a = x then repLess ys a else (x,xs)::(repLess ys a)

let rec joinIfEqual (a,cs) rep =
	match rep with
	[] -> (a,cs)
	|(x,xs)::ys-> if a = x then (a,union xs cs) else (joinIfEqual (a,cs) ys)
let rec merge rep1 rep2 =
	match rep1 with
	[] -> rep2
	|(a,cs)::xs ->  (joinIfEqual (a,cs) rep2) :: (merge xs (repLess rep2 a))



(* FUNCTION repOfATree *)
let extrairNomeATree t = 
	match t with 
		|ANil -> failwith "extrairNomeATree: bad argument"
		|ANode(a,_,_) -> a

let rec repOfAtreeAux t = 
	match t with 
	| ANil -> []
	| ANode(a,ANil,ANil) -> [(a,[])]
	| ANode(a,ANil, rt) -> merge (repOfAtreeAux rt) ([(extrairNomeATree(rt),[a])] @ [(a, [])])
	| ANode(a,lt,ANil) -> merge (repOfAtreeAux lt) ([(extrairNomeATree(lt),[a])] @ [(a, [])])
	| ANode(a,lt,rt) -> merge (merge (repOfAtreeAux lt) (repOfAtreeAux rt))  ([(extrairNomeATree(lt),[a])] @ [(extrairNomeATree(rt),[a])] @ [(a, [])])


let repOfATree t = repOfAtreeAux t



(* FUNCTION repOfDTree *)

let rec extrairNomesDTreeList l =
	match l with
	|[] -> []
	|DNil :: xs -> failwith "extrairNomeDTreeList: bad argument"
	|DNode(x,_)::xs -> x::(extrairNomesDTreeList xs)

let rec repOfDtreeAux t = 
	match t with 
	| DNil -> []
	| DNode(a, []) -> [(a,[])]
	| DNode(a, [c]) -> (a,extrairNomesDTreeList [c])::(repOfDtreeAux c)
	|DNode(a,x::xs) -> (a,extrairNomesDTreeList (x::xs)) :: ((repOfDtreeAux x) @ (repOfDtreeAuxChilds xs))

	and 
	repOfDtreeAuxChilds childs = 
		match childs with
		|[] ->  []
		|x::xs -> (repOfDtreeAux x) @ (repOfDtreeAuxChilds xs)

let repOfDTree t = clean(repOfDtreeAux(t))


(* FUNCTION descendantsN *)


let rec descendantsNAux rep n lst =
	if (n = 0) then lst else 
	match lst with
	|[]-> []
	|x::xs -> (descendestes rep n x) @ (descendantsNAux rep n xs)
	
	and descendestes rep n item =
		if n = 0 then [] else
		 let childList = children rep [item] in
		 childList @ (descendantsNAux (rep) (n-1) (childList))

	
let descendantsN rep n lst = clean (descendantsNAux rep n lst)

(* FUNCTION siblings *)

let rec siblingsAux rep lst =
	match lst with
	| [] -> []
	| x::xs -> (listOfSiblings rep x) @ (siblingsAux rep xs)
	and listOfSiblings rep x = 
		let parentsOfItem = parents rep [x] in
		children rep parentsOfItem


let siblings rep lst = clean(siblingsAux rep lst)


(* FUNCTION siblingsInbreeding *)
let areInbreeding (s1,s2) rep =
	let childs1 = children rep [s1] in
	let childs2 = children rep [s2] in
	let comunChild = inter childs1 childs2 in
	comunChild <> [] 
let rec joint rep elem l =
	match l with 
	[] -> []
	|x::xs -> (if ((areInbreeding (elem, x) rep) = true) then [(elem, x)] else []) @ (joint rep elem xs)

let rec getPossiblePairs rep l =
	match l with 
	|[]-> []
	|[x] -> []
	|x::xs -> (joint rep x xs) @ (getPossiblePairs rep xs)

let rec siblingsInbreedingAux rep fixedRep =
		match rep with 
		[] -> []
		|(p,[])::xs -> (siblingsInbreedingAux xs fixedRep )
		|(p,[c])::xs -> (siblingsInbreedingAux xs fixedRep )
		|(p,c::cs)::xs -> union (getPossiblePairs fixedRep (c::cs)) (siblingsInbreedingAux xs fixedRep )
	
let siblingsInbreeding rep = siblingsInbreedingAux rep rep
	



(* FUNCTION waveN *)
let rec totalWave rep n lst =
	if lst = [] then [] else
	match n with 
	0 -> lst
	|1 -> (parents rep lst) @ (children rep lst) @ lst
	|v -> (totalWave rep (n-1) (parents rep lst)) @ (totalWave rep (n-1) (children rep lst))

let rec waveN rep n lst =
	if lst = [] then [] else
	match n with 
	0 -> lst
	|1 -> (parents rep lst) @ (children rep lst)
	|v -> diff ((waveN rep (n-1) (parents rep lst)) @ (waveN rep (n-1) (children rep lst))) (totalWave rep (n-1) lst)

(* FUNCTION supremum *)
let rec allAscendentsL rep l = 
	match l with
	[] -> []
	|[x] -> allAscendents rep x
	|x::xs -> inter (allAscendents rep x) (allAscendentsL rep xs) 
and allAscendents rep x =
	let dads = parents rep [x] in
	match dads with 
		[]-> []
		|[d] -> dads @ (allAscendents rep d)
		|[d1;d2] -> dads @ (allAscendents rep d1) @ (allAscendents rep d2)
		|y::w::ys -> failwith "allAscendents: bad argument"
;;

let haveChild rep x l =
	match l with 
	[]-> false 
	|y::ys -> let l2 = (inter (y::ys) (children rep [x])) in
	l2 <> [] 	

let rec supremum rep l = 
	match l with 
	[] -> []
	|[x] -> let dads = (parents rep [x]) in
	supremumAux rep dads dads
	|x::xs -> let comun = clean(allAscendentsL rep l) in supremumAux rep comun comun
	and supremumAux rep comun comunFix = 
	match comun with 
	[] -> []
	|[y] -> [y]
	|y::ys -> if (haveChild rep y comunFix) then supremumAux rep ys comunFix else y::(supremumAux rep ys comunFix)

(* FUNCTION validStructural *)
let rec allOccurrencies rep =
	match rep with
	[]-> []
	|(a,cs)::xs -> union cs ([a] @ (allOccurrencies xs))

let rec haveRepeated rep =
	match rep with
	[] -> false
	|(a,_)::xs -> if (inter [a] (all1 xs)) = [a] then true else haveRepeated xs

let validStructural rep =
	if haveRepeated rep = true then false else 
	if (len (allOccurrencies rep) = size rep) then true else false 

(* FUNCTION validSemantic *)

let rec validSemanticAux rep l ancestors =
	match ancestors with 
	[] -> true
	|[d] -> if((inter l [d]) <> [] ) then false else validSemanticAux rep (d::l) (parents rep [d])
	|[d1;d2] ->  if((inter l [d1;d2]) <> []) then false
	else (validSemanticAux rep (l @ ancestors) (parents rep [d1;d2]))
	|x::y::xs -> false
	

let rec validSemantic rep =
	match rep with
	[]-> true 
	|(a,cs)::xs -> let dads = parents rep [a] in
	(validSemanticAux rep [a] dads) && validSemantic xs

;;
let rec heightTeste tree =
	match tree with
	|ANil -> 0
	|ANode(x,y,z) -> 1 + max (heightTeste y) (heightTeste z);;

;;
let rec pathl tree =
	match tree with
	ANil -> []
	|ANode(x,y,z) -> if heightTeste y > heightTeste z then x::(pathl y) else x::(pathl z);;
let rec paths tree =
	match tree with
	ANil -> []
	|ANode(x,ANil,ANil) -> [[x]]
	|ANode(x,y,z) -> if heightTeste y = heightTeste z then [x::pathl y] @ [(x::(pathl z))] 
	else 
	if heightTeste y > heightTeste z then [x:: (pathl y)] else [x::(pathl z)];;


