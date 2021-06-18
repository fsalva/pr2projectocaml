(*  Autore: Francesco Salvatori - Matricola: 581142 - Progetto PR2 sessione estiva 2021. *)

type ide = string;;

type exp = CstInt of int
		| CstTrue 
		| CstFalse
    | CstString of string
		| Den of ide
		| Sum of exp * exp
		| Sub of exp * exp
		| Times of exp * exp
		| Ifthenelse of exp * exp * exp
		| Eq of exp * exp
		| Let of ide * exp * exp
		| Fun of ide * exp
		| Letrec of ide * ide * exp * exp
		| Apply of exp * exp
    | Empty of ide
    | Singleton of ide * exp 
    | Set of ide * values
    | Union of exp * exp
    | Intersect of exp * exp
    | Diff of exp * exp
    | Insert of exp * exp
    | IsEmpty of exp
    | Member of exp * exp
    | Subset of exp * exp
    | Min of exp
    | Max of exp
    | ForAll of exp * exp
    | Exists of exp * exp
    | Filter of exp * exp 
    | Map of exp * exp 
  and values = End | Val of exp * Values;;

(* Tipi di dato esprimibili: *)
type evT = Int of int 
| Bool of bool 
| String of string
| Closure of ide * exp * evT env 
| RecClosure of ide * ide * exp * evT env 
| Set of ide * exp list
| Unbound;;

(* Op. su ambiente *)
type 'v env = (string * 'v) list;;


let emptyEnv  = [ ("", Unbound)] ;;

let bind (s: evT env) (i:string) (x:evT) = ( i, x ) :: s;;

let rec lookup (s:evT env) (i:string) = match s with
    | [] ->  Unbound
    | (j,v)::sl when j = i -> v
    | _::sl -> lookup sl i;;

(* Typechecking *)

(* Funzione ausiliaria per trasformare i tipi esprimibili in stringhe
Definita solo per i tipi Int, Bool e String, come da specifica.*)
let evT2str (e:evT) = match e with 
| Int(u) -> "int"
| Bool(u) -> "bool"
| String(u) -> "string"
| _ -> failwith("evT2str: unsupported set type");;


let setvaluesvalidator (t:string) vl = 
  match vl with 
  | [] -> true
  | h::tl -> if evT2str h = t 
            then setvaluesvalidator t tl
            else -> false;;

let typecheck (x, y) = match x with	
        | "int" -> 
             (match y with 
                         | Int(u) -> true
                         | _ -> false)
        | "bool" -> 
              (match y with 
                          | Bool(u) -> true
                          | _ -> false)

        | _ -> failwith ("not a valid type");;


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


let rec eval  (e:exp) (s:evT env) = match e with
 | CstInt(n) -> Int(n)
 | CstTrue -> Bool(true)
 | CstFalse -> Bool(false)
 | Eq(e1, e2) -> int_eq((eval e1 s), (eval e2 s))
 | Times(e1,e2) -> int_times((eval e1 s), (eval e2 s))
 | Sum(e1, e2) -> int_plus((eval e1 s), (eval e2 s))
 | Sub(e1, e2) -> int_sub((eval e1 s), (eval e2 s))
 | Ifthenelse(e1,e2,e3) -> let g = eval e1 s in
                (match (typecheck("bool", g), g) with
			| (true, Bool(true)) -> eval e2 s
                        | (true, Bool(false)) -> eval e3 s
                	| (_, _) -> failwith ("nonboolean guard"))
| Den(i) -> lookup s i
| Let(i, e, ebody) -> eval ebody (bind s i (eval e s))
| Fun(arg, ebody) -> Closure(arg,ebody,s)
| Letrec(f, arg, fBody, letBody) -> 
  let benv = bind (s) (f) (RecClosure(f, arg, fBody,s)) in
      eval letBody benv
| Apply(Den(f), eArg) -> 
  let fclosure = lookup s f in 
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
| Apply(_,_) -> failwith("Application: not first order function") ;;


Letrec("fact", "n",   
Ifthenelse(Eq(Den("n"),CstInt(0)),
                 CstInt(1),
                 Times(Den("n"),Apply(Den("fact"),Sub(Den("n"),CstInt(1))))), Apply(Den("fact"),CstInt(3)))

(* Interprete full *)

let rec eval1  (e:exp) (s:evT env) = match e with
 | CstInt(n) -> Int(n)
 | CstTrue -> Bool(true)
 | CstFalse -> Bool(false)
 | Eq(e1, e2) -> int_eq((eval e1 s), (eval e2 s))
 | Times(e1,e2) -> int_times((eval e1 s), (eval e2 s))
 | Sum(e1, e2) -> int_plus((eval e1 s), (eval e2 s))
 | Sub(e1, e2) -> int_sub((eval e1 s), (eval e2 s))
 | Ifthenelse(e1,e2,e3) -> let g = eval e1 s in
                (match (typecheck("bool", g), g) with
			| (true, Bool(true)) -> eval e2 s
                        | (true, Bool(false)) -> eval e3 s
                	| (_, _) -> failwith ("nonboolean guard"))
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
           | _ -> failwith("non functional value"));; 


