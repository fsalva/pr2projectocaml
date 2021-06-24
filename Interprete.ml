(*  
  Autore: Francesco Salvatori 
  Matricola: 581142 
  Progetto PR2 sessione estiva 2021. *)

type ide = string;;

type exp = 
(*Interi*)
  | CstInt of int
  | CstTrue 
  | CstFalse
  | CstString of string
  | Den of ide
  | Sum of exp * exp
  | Sub of exp * exp
  | Times of exp * exp
  (*Booleani*)
  | GT of exp * exp
  | Eq of exp * exp
  | Ifthenelse of exp * exp * exp
  | BOr of exp * exp
  | BAnd of exp * exp 
  | BNot of exp
(*Funzioni*)
  | Let of ide * exp * exp
  | Fun of ide * exp
  | Letrec of ide * ide * exp * exp
  | Apply of exp * exp
(*Insiemi*)
  | Empty of ide
  | Singleton of ide * exp 
  | OfSet of ide * elements
  | Union of exp * exp
  | Intersect of exp * exp
  | Diff of exp * exp
  | Insert of exp * exp
  | Remove of exp * exp
  | IsEmpty of exp
  | Member of exp * exp
  | Subset of exp * exp
  | MinSet of exp
  | MaxSet of exp
  | ForAll of exp * exp
  | Exists of exp * exp
  | Filter of exp * exp 
  | Map of exp * exp 
(*Lista: vedi relazione sulle motivazioni*)
  | OfList of ide * elements 
and elements = | End | Element of exp * elements;;

(*Def. ambiente*)
type 'v env = (string * 'v) list;;

(* Tipi di dato esprimibili: *)
type evT = Int of int 
         | Bool of bool 
         | String of string
         | Closure of ide * exp * evT env 
         | RecClosure of ide * ide * exp * evT env 
         | Set of ide * evT list
         | List of ide * evT list
         | Unbound;;

(* Op. su ambiente *)

let emptyEnv  = [ ("", Unbound)] ;;

let bind (s: evT env) (i:string) (x:evT) = ( i, x ) :: s;;

let rec lookup (s:evT env) (i:string) = match s with
  | [] ->  Unbound
  | (j,v)::sl when j = i -> v
  | _::sl -> lookup sl i;;

(* Typechecking *)
let typecheck (x, y) = match x with	
  | "int" -> 
      (match y with 
       | Int(u) -> true
       | _ -> false)
  | "bool" -> 
      (match y with 
       | Bool(u) -> true
       | _ -> false)
  | "string" -> 
      (match y with
       | String(u) -> true
       | _ -> false)
  | "set" -> 
      (match y with 
       | Set(t, vl) -> 
           (match t with
            | "int" | "bool" | "string" -> true
            | _ -> false)
       | _ -> false)
  | "list" -> 
      (match y with
       | List(t, vl) -> (match t with
           |  "int" | "bool" | "string" -> true
           | _ -> false)
       | _ -> false) 
  | _ -> failwith ("not a valid type");;


(*Op. su Interi*)
let int_eq(x,y) =   
  match (typecheck("int",x), typecheck("int",y), x, y) with
  | (true, true, Int(v), Int(w)) -> Bool(v = w)
  | (_,_,_,_) -> failwith("run-time error ");;
      
let int_plus(x, y) = 
  match(typecheck("int",x), typecheck("int",y), x, y) with
  | (true, true, Int(v), Int(w)) -> Int(v + w)
  | (_,_,_,_) -> failwith("run-time error ");;

let int_sub(x, y) = 
  match(typecheck("int",x), typecheck("int",y), x, y) with
  | (true, true, Int(v), Int(w)) -> Int(v - w)
  | (_,_,_,_) -> failwith("run-time error ");;

let int_times(x, y) = 
  match(typecheck("int",x), typecheck("int",y), x, y) with
  | (true, true, Int(v), Int(w)) -> Int(v * w)
  | (_,_,_,_) -> failwith("run-time error ");;

let int_gt(x, y) = 
match(typecheck("int",x), typecheck("int",y), x, y) with
| (true, true, Int(v), Int(w)) -> Bool(v > w)
| (_,_,_,_) -> failwith("run-time error ");;


(*Op. su booleani*)
let bool_or(x,y) =
  match (typecheck("bool", x), typecheck("bool", y), x, y) with
  | (true, true, Bool(v), Bool(w)) -> Bool( v || w)
  | (_,_,_,_) -> failwith("typecheck error.");;

let bool_and(x,y) = 
  match (typecheck("bool", x), typecheck("bool", y), x, y) with
  | (true, true, Bool(v), Bool(w)) -> Bool( v && w)
  | (_,_,_,_) -> failwith("typecheck error.");;

let bool_not(x) = 
  match (typecheck("bool", x), x) with 
  | (true, Bool(v)) ->  Bool(not v) 
  | (_,_) -> failwith("typecheck error.");;


(*Op. su Insiemi*)


(*Controlla se s è un set poi guarda la sua implementazione. *)
let is_empty (s:evT) = match (typecheck("set", s), s) with
  | (true, Set(t, vl)) -> (match vl with | [] -> Bool(true) | _ -> Bool(false))
  | (_,_) -> failwith("is_empty: called on a non-set");;

(*ricerca in una lista.*)
let rec searchList v l = (match l with
    | [] -> false
    | h::tl -> if v = h then true else searchList v tl);;

(*Controlla se s è un set, poi vede se il tipo di 'e' è ammesso e uguale a quello del set e lo cerca nel set.*)
let member (e:evT) s = (match (typecheck("set", s), s) with 
    | (true, Set(t, vl)) -> 
        if typecheck(t, e) then if searchList  e vl then Bool(true) else Bool(false)
        else failwith("member: can't have heterogeneous sets")
    | (_,_) -> failwith("member: called on a non-set")) ;;

(*Chiama la member per scoprire se un elemento è presente, altrimenti restituisce un nuovo set e lo inserisce in testa. *)
let insert (e:evT) (s:evT) = match s with
  | Set(t, vl) -> if searchList e vl then Set(t, vl) else Set(t, e::vl)
  | _ -> failwith("insert: called on a non-set");;



(*Funzione ausiliaria per calcolare il max di una lista di interi.*)
let rec aux_max (l:evT list) (max:int) = match l with 
  | h::tl -> (match h with 
      | Int(u) -> if u > max then aux_max tl u else aux_max tl max
      | _ -> failwith("max: called on a non-integer set"))
  | [] -> max;;

(*Controlla che s sia un set, se è un set di interi chiama una routine per trovare il massimo, altrimenti fallisce.*)
let max (s:evT) = match s with 
  | Set("int", vl) -> (match vl with 
      | [] -> failwith("max: called on an empty set.")
      | _ -> Int(aux_max vl Int.min_int))
  | _ -> failwith("max: called on a non-set");;

(*Come sopra, ma col minimo.*)
let rec aux_min (l:evT list) (min:int) = match l with
  | h::tl -> (match h with 
      | Int(u) -> if u < min then aux_min tl u else aux_min tl min
      | _ -> failwith("min: called on a non-integer set") )
  | [] -> min;;

(*Come sopra, ma col minimo.*)
let min (s:evT) = match s with 
  | Set("int", vl) -> (match vl with 
      | [] -> failwith("max: called on an empty set.")
      | h::tl -> Int(aux_min vl Int.max_int))
  | _ -> failwith("max: called on a non-set");;  

(*Sottoinsieme: chiama la member per ogni elemento del primo set sul secondo.*)
let subset (s1:evT) (s2:evT) = match ( typecheck("set", s1), typecheck("set", s2) , s1 , s2 ) with
  | (true, true, Set(t1, vl1), Set(t2, vl2)) -> 
      if t1 = t2 then
        let rec aux_subset l1 l2 = (match l1 with 
            | h::tl -> if searchList h vl2 
                then aux_subset tl l2
                else false
            | [] -> true)
        in Bool(aux_subset vl1 vl2) 
      else failwith("subset: called on different set types")
  | (_,_,_,_) -> failwith("subset: called on one or more non-set(s).");;

(*funzione ausiliaria che fa il merge di due liste.*)
let rec aux_union l1 l2 = (match (l1,l2) with 
    |([], _) -> l2 
    | (_, []) -> l1 
    | (h::tl, _) -> if searchList h l2 
        then aux_union tl l2 
        else h::aux_union tl l2);;

(*Unione: creo un set, con gli elementi del primo e del secondo mantenendo l'invariante dei Set.*)
let union (s1:evT) (s2:evT) = match ( typecheck("set", s1), typecheck("set", s2) , s1 , s2 ) with
  | (true, true, Set(t1, vl1), Set(t2, vl2)) ->
      if t1 = t2 then Set(t1, aux_union vl1 vl2)
      else failwith("union: called on different set types")
  | (_,_,_,_) -> failwith("union: failed typecheck");;

(*Intersezione: come union ma nella funzione ausiliaria aggiungo ad una lista solo quando trovo duplicati.*)
let rec aux_intersect l1 l2 = (match (l1, l2) with 
    | ([], _) -> []
    | (_, []) -> []
    | (h::tl, _) -> if searchList h l2 
        then h::aux_intersect tl l2 
        else aux_intersect tl l2);;

let intersect  (s1:evT) (s2:evT) = match ( typecheck("set", s1), typecheck("set", s2) , s1 , s2 ) with
  | (true, true, Set(t1, vl1), Set(t2, vl2)) -> 
      if t1 = t2 then Set(t1, aux_intersect vl1 vl2)
      else failwith("intersect: called on different set types")
  | (_,_,_,_) -> failwith("intersect: failed typecheck");;

(*Funzione ausiliaria per la differenza che è un po' il duale della funzione ausiliaria per l'intersezione.*)
let rec aux_diff l1 l2 = (match (l1, l2) with 
    | ([], _) -> []
    | (_, []) -> []
    | (h::tl, _) -> if searchList h l2 
        then aux_diff tl l2 
        else h::aux_diff tl l2);;


(* A - B =|= B - A, diff rimuove dal primo gli elementi del secondo che (nel primo) risultano duplicati *)
let diff (s1:evT) (s2:evT) = match ( typecheck("set", s1), typecheck("set", s2) , s1 , s2 ) with
  | (true, true, Set(t1, vl1), Set(t2, vl2)) -> 
      if t1 = t2 then Set(t1, aux_diff vl1 vl2)
      else failwith("diff: called on different set types")
  | (_,_,_,_) -> failwith("intersect: failed typecheck");;

(* _________________________________*)
(*Costruttori di Set*)
(* ---------------------------------*)

let empty_Set t = match  t with
  | "int" | "bool" | "string" -> Set(t, [])
  | _ -> failwith("empty_Set: unsupported type.");; 

let singleton_Set t (e:evT) = if typecheck(t, e) 
  then let set = empty_Set t in insert e set
  else failwith("singletonConstructor: Cannot instanciate heterogeneous sets.");;

let rec aux_ofSet t l l2 = match l with
  | [] -> l2
  | h::tl -> if searchList h l2 
      then aux_ofSet t tl l2 
      else aux_ofSet t tl (h::l2);;

(*Costruttore di of(), fa il typecheck sulla lista di espr. del Set e poi li aggiunge con una subroutine senza duplicati.*)
let of_Set (t, (el:evT list)) = 
  if typecheck("set", (Set(t, el)))
  then (match el with 
      | [] -> empty_Set t 
      | h::tl -> Set(t, aux_ofSet t el []))
  else failwith("ofConstructor: typecheck fail.");;

let of_List (t, (el:evT list)) = if typecheck("list", (List(t, el)))
  then (match el with | [] -> List(t, []) | h::tl -> List(t, el)) 
  else failwith("ofListConstructor: typecheck fail.");;

(*Remove chiama la diff e il costuttore del singleton per semplicità.*)
let remove (e:evT) (s:evT) = match s with 
  | Set((t:ide), vl) -> 
      if typecheck(t, e) 
      then let s1 = singleton_Set t e in diff s s1
      else failwith("remove: non consistent call")
  | _ -> failwith("remove: called on a non-set");;

let rec eval  (e:exp) (s:evT env) = match e with
(*Interi ---- Operazioni tra interi.*)
  | GT(e1, e2) -> int_gt((eval e1 s), (eval e2 s))
  | CstInt(n) -> Int(n)
  | Eq(e1, e2) -> int_eq((eval e1 s), (eval e2 s))
  | Times(e1,e2) -> int_times((eval e1 s), (eval e2 s))
  | Sum(e1, e2) -> int_plus((eval e1 s), (eval e2 s))
  | Sub(e1, e2) -> int_sub((eval e1 s), (eval e2 s))
(*Booleani ---- Operazioni tra booleani *)
  | CstTrue -> Bool(true)
  | CstFalse -> Bool(false)
  | BOr(e1, e2) -> bool_or((eval e1 s), (eval e2 s))
  | BAnd(e1, e2) -> bool_and((eval e1 s), (eval e2 s))
  | BNot(e) -> bool_not(eval e s)
  | Ifthenelse(e1,e2,e3) -> let g = eval e1 s in
      (match (typecheck("bool", g), g) with
       | (true, Bool(true)) -> eval e2 s
       | (true, Bool(false)) -> eval e3 s
       | (_, _) -> failwith ("nonboolean guard"))
(*Stringhe*)
  | CstString(s) -> String(s)
(*Lista ---- Costruttore*)
  | OfList(t, args) -> let rec evaList (el:elements) ret =
                         (match el with 
                          | Element(v, next) -> let v' = eval v s in
                              if typecheck(t, v') then evaList next (v'::ret)
                              else failwith("Of: typecheck fail!")
                          | End -> ret) 
      in of_List (t, (evaList args []))
(*Insiemi ---- Costruttori*)
  | Empty(t) -> empty_Set t
  | Singleton(t, v) -> singleton_Set t (eval v s)
  | OfSet(t, args) -> let rec evaList (el:elements) ret =
                        (match el with 
                         | Element(v, next) -> let v' = eval v s in
                             if typecheck(t, v') then evaList next (v'::ret)
                             else failwith("Of: typecheck fail!")
                         | End -> ret) 
      in of_Set(t, (evaList args []))

(*Insiemi ---- Operazioni di base*)
  | Union(s1, s2) -> union (eval s1 s) (eval s2 s)
  | Intersect(s1, s2) -> intersect (eval s1 s) (eval s2 s)
  | Diff(s1, s2) -> diff (eval s1 s) (eval s2 s)
  | Insert(v, set) -> insert (eval v s) (eval set s)
  | Remove(v, set) -> remove (eval v s) (eval set s)
  | IsEmpty(set) -> is_empty (eval set s)
  | Member(v, set) -> member (eval v s) (eval set s)
  | Subset(set1, set2) -> subset (eval set1 s) (eval set2 s)
  | MinSet(set) -> min (eval set s)
  | MaxSet(set) -> max (eval set s)
(*Insiemi ---- Operazioni funzionali*)
  | ForAll(p, set) -> 
      let eSet = eval set s in 
      let eP = eval p s in 
      (match (typecheck("set", eSet), eSet, eP) with
       | (true, Set(t, vl), Closure(arg, fbody, fenv)) -> 
           let env0 = emptyEnv in
           let rec aux_forall (l:evT list) = 
             (match l with
              | [] -> Bool(true)
              | h::tl -> (match app eP h env0 with
                  | Bool(b) -> if b then aux_forall tl else Bool(false) 
                  | _ -> failwith("Forall: non-boolean predicate") )
             )
           in aux_forall vl
       | (_,_,_) -> failwith("Forall: typecheck error." )) 
  | Exists(p, set) -> let eSet = eval set s in let eP = eval p s in 
      (match(typecheck("set", eSet), eSet, eP ) with
       | (true, Set(t, vl), Closure(arg, fbody, fenv)) -> 
           let env0 = emptyEnv in 
           let rec aux_exists (l:evT list) = 
             (match l with
              | [] -> Bool(false)
              | h::tl -> (match app eP h env0 with
                  | Bool(b) -> if b then Bool(true) else aux_exists tl
                  | _ -> failwith("Forall: non-boolean predicate")))
           in aux_exists vl
       | (_,_,_) -> failwith("Exists: typecheck error"))
  | Filter(p, set) -> let eSet = eval set s in let eP = eval p s in
      (match(typecheck("set", eSet),  eSet, eP) with
       | (true, Set(t,vl), Closure(arg, fbody, fenv)) -> 
           let env0 = emptyEnv in 
           let rec aux_filter (l:evT list) lret = 
             (match l with
              | [] -> lret
              | h::tl -> 
                (match app eP h env0 with 
                | Bool(b) -> if b then aux_filter tl (h::lret) else aux_filter tl lret
                | _ -> failwith("Filter: non-boolean predicate")))
           in Set(t, aux_filter vl []) 
       | (_,_,_) -> failwith("Filter: typecheck error"))
  | Map(f, set) -> 
      let eSet = eval set s in let eF = eval f s in 
      (match(typecheck("set", eSet), eSet, eF) with
       | (true, Set(t, vl), Closure(arg, fbody, fenv)) -> 
           let env0 = emptyEnv in 
           let rec aux_map (l:evT list) lret =
             (match l with
              | [] -> lret
              | h::tl -> let rv = app eF h env0 in aux_map tl (rv::lret)) 
            
           in List(t, (aux_map vl [])) 
       | (_,_,_) -> failwith("Map: typecheck error"))
  | Den(i) -> lookup s i
  | Let(i, e, ebody) -> eval ebody (bind s i (eval e s))
  | Fun(arg, ebody) -> Closure(arg,ebody,s)
  | Letrec(f, arg, fBody, letBody) -> 
      let benv = bind (s) (f) (RecClosure(f, arg, fBody,s)) in
      eval letBody benv
  | Apply(eF, eArg) ->
      let fclosure = eval eF s in 
      (match fclosure with 
       | Closure(arg, fbody, fDecEnv) ->
           let aVal = eval eArg s in
           let aenv = bind fDecEnv arg aVal in 
           eval fbody aenv
       | RecClosure(f, arg, fbody, fDecEnv) ->
           let aVal = eval eArg s in
           let rEnv = bind fDecEnv f fclosure in
           let aenv = bind rEnv arg aVal in 
           eval fbody aenv
       | _ -> failwith("non functional value")) 
and app (fclosure:evT) (argVal:evT) (env:evT env) = 
  (match fclosure with
   | Closure(arg, fbody, fDeclEnv) -> 
       let nEnv = bind fDeclEnv arg argVal 
       in eval fbody nEnv
   | RecClosure(f, arg, fbody, fDeclEnv) -> 
       let recEnv = bind fDeclEnv f fclosure 
       in let nEnv = bind recEnv arg argVal 
       in eval fbody nEnv
   | _ -> failwith("apply: functional type expected!")
  );;