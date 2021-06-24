(*  
  Autore: Francesco Salvatori 
  Matricola: 581142 
  Progetto PR2 sessione estiva 2021. *)

type ide = string;;

type tval = TInt 
| TBool  
| TString
| TSet of tval
| TList of tval
| TFun of tval * tval
| Undefined;;

type texp = 
(*Interi*)
| EInt of int
| EBool of bool
| Den of ide
| EString of string
| Sum of texp * texp
| Sub of texp * texp
| Times of texp * texp
(*Booleani*)
| GT of texp * texp
| Eq of texp * texp
| Ifthenelse of texp * texp * texp
| BOr of texp * texp
| BAnd of texp * texp 
| BNot of texp
(*Funzioni*)
| Let of ide * texp * texp
| Fun of ide * tval * texp
| Letrec of ide * ide * tval * tval * texp * texp
| Apply of texp * texp
(*Insiemi*)
| Empty of tval
| Singleton of tval * texp 
| OfSet of tval * elements
| Union of texp * texp
| Intersect of texp * texp
| Diff of texp * texp
| Insert of texp * texp
| Remove of texp * texp
| IsEmpty of texp
| Member of texp * texp
| Subset of texp * texp
| MinSet of texp
| MaxSet of texp
| ForAll of texp * texp
| Exists of texp * texp
| Filter of texp * texp 
| Map of texp * texp 
(*Lista: vedi relazione sulle motivazioni*)
| OfList of tval * elements 
and elements = | End | Element of texp * elements;;

(*Def. ambiente*)
type 't tenv = (string * 't) list;;

let emptyEnv  = [ ("", Undefined)] ;;

let bind (s: tval tenv) (i:string) (x:tval) = ( i, x ) :: s;;

(* Op. su ambiente *)
let rec lookup (s:tval tenv) (i:string) = 
  match s with
  | [] ->  Undefined
  | (j,v)::sl when j = i -> v
  | _::sl -> lookup sl i;;

let rec teval (e:texp) tenv = match e with
(*Interi ---- Operazioni tra interi.*)
| EInt(n) -> TInt
| GT(e1, e2) -> 
    (match ((teval e1 tenv) , (teval e2 tenv)) with
    | (TInt, TInt) -> TBool
    | (_,_) -> failwith("GT: called on non-integer expression(s)"))
| Eq(e1, e2) ->
    (match ((teval e1 tenv) , (teval e2 tenv)) with
    | (TInt, TInt) -> TBool
    | (_,_) -> failwith("Eq: called on non-integer expression(s)"))
| Times(e1,e2) ->
    (match ((teval e1 tenv) , (teval e2 tenv)) with
    | (TInt, TInt) -> TInt
    | (_,_) -> failwith("Times: called on non-integer expression(s)"))
| Sum(e1, e2) ->
    (match ((teval e1 tenv) , (teval e2 tenv)) with
    | (TInt, TInt) -> TInt
    | (_,_) -> failwith("Sum: called on non-integer expression(s)"))
| Sub(e1, e2) ->
    (match ((teval e1 tenv) , (teval e2 tenv)) with
    | (TInt, TInt) -> TInt
    | (_,_) -> failwith("Sub: called on non-integer expression(s)"))
(*Booleani ---- Operazioni tra booleani *)
| EBool(e) -> TBool
| BOr(e1, e2) ->
    (match ((teval e1 tenv) , (teval e2 tenv)) with
    | (TBool, TBool) -> TBool
    | (_,_) -> failwith("Or: called on non-boolean expression(s)"))
| BAnd(e1, e2) ->
    (match ((teval e1 tenv) , (teval e2 tenv)) with
    | (TBool, TBool) -> TBool
    | (_,_) -> failwith("And: called on non-boolean expression(s)"))
| BNot(e)-> 
    (match (teval e tenv) with 
    | TBool -> TBool 
    | _ -> failwith("Not: called on a non-boolean exp"))
| Ifthenelse(e1,e2,e3) -> let t1 = (teval e1 tenv) in
    (match t1 with
    | TBool -> let t2 = (teval e2 tenv) in 
        let t3 = (teval e3 tenv) in 
        (match (t1, t2) with 
        | (TInt, TInt) -> TInt
        | (TBool, TBool) -> TBool 
        | (_,_) -> failwith("IfThenElse: inconsistent branches")) 
    | _ -> failwith ("IfThenElse: nonboolean guard"))
(*Stringhe*)
| EString(s) -> TString
(*Lista ---- Costruttore*)
| OfList(t, args) ->  
    (match t with 
    | TInt | TBool | TString -> 
        let rec checkArgs argss = 
            (match argss with 
            | Element(tt, l) -> if t = (teval tt tenv) then checkArgs l else failwith("OfSet: different types in args.") 
            | End -> TSet(t)) 
        in checkArgs args 
    | _ -> failwith("OfList: called on an unsupported set type."))
(*Insiemi ---- Costruttori*)
| Empty(t) -> 
    (match t with 
    | TInt | TBool | TString -> TSet(t) 
    | _ -> failwith("Empty: Unsupported set type"))
| Singleton(t, v) -> let v1 = (teval v tenv) in  
    (match (t,v1) with 
    | (TInt, TInt) | (TBool, TBool) | (TString, TString) -> TSet(t) 
    | _ -> failwith("Singleton: type fail."))
| OfSet(t, args) -> 
    (match t with 
    | TInt | TBool | TString -> 
        let rec checkArgs argss = 
            (match argss with 
            | Element(tt, l) -> if t = (teval tt tenv) then checkArgs l else failwith("OfSet: different types in args.") 
            | End -> TSet(t)) 
        in checkArgs args
    | _ -> failwith("Empty: Unsupported set type"))

(*Insiemi ---- Operazioni di base*)
| Union(s1, s2) -> 
    (match ((teval s1 tenv),(teval s2 tenv)) with
    | (TSet(t1), TSet(t2)) -> if t1 = t2 then t1 else failwith("Union: called on different set types")
    | (_,_) -> failwith("Union: called on non-sets."))
| Intersect(s1, s2) -> 
    (match ((teval s1 tenv),(teval s2 tenv)) with
    | (TSet(t1), TSet(t2)) -> if t1 = t2 then t1 else failwith("Intersect: called on different set types")
    | (_,_) -> failwith("Intersect: called on non-sets."))
| Diff(s1, s2) -> 
    (match ((teval s1 tenv),(teval s2 tenv)) with
    | (TSet(t1), TSet(t2)) -> if t1 = t2 then t1 else failwith("Diff: called on different set types")
    | (_,_) -> failwith("Diff: called on non-sets."))
| Insert(v, set) -> 
    (match ((teval v tenv),(teval set tenv)) with
    | (t1, TSet(t2)) -> if t1 = t2 then TSet(t1) else failwith("Insert: called on different set types")
    | (_,_) -> failwith("Insert: called on non-sets."))
| Remove(v, set) -> 
    (match ((teval v tenv),(teval set tenv)) with
    | (t1, TSet(t2)) -> if t1 = t2 then TSet(t1) else failwith("Remove: called on different set types")
    | (_,_) -> failwith("Remove: called on non-sets."))
| IsEmpty(set) ->  
    (match ((teval set tenv)) with
    | TSet(TInt) | TSet(TBool) | TSet(TString) -> TBool
    | _ -> failwith("IsEmpty: called on a non-set or a non supported one."))
| Member(v, set) -> 
    (match ((teval v tenv),(teval set tenv)) with
    | (t1, TSet(t2)) -> if t1 = t2 then TBool else failwith("Member: called on different types")
    | (_,_) -> failwith("Member: called on non-sets."))
| Subset(s1, s2) ->
    (match ((teval s1 tenv),(teval s2 tenv)) with
    | (TSet(t1), TSet(t2)) -> if t1 = t2 then TBool else failwith("Subset: called on different set types")
    | (_,_) -> failwith("Diff: called on non-sets."))
| MinSet(set) ->  
    (match ((teval set tenv)) with
    | TSet(TInt) -> TInt
    | _ -> failwith("MinSet: called on a non supported set type.")) 
| MaxSet(set)  ->  
    (match ((teval set tenv)) with
    | TSet(TInt) -> TInt
    | _ -> failwith("MinSet: called on a non supported set type.")) 
(*Insiemi ---- Operazioni funzionali*)
| ForAll(p, set) -> 
    (match((teval p tenv),(teval set tenv)) with
    | (TFun(t1, t2), TSet(t3)) -> 
        if t1 = t3 
        then (if t2 = TBool then TBool else failwith("ForAll: Not a predicate")) 
        else failwith("ForAll: called on different set types.")
    | _ -> failwith("ForAll: called on a non supported type"))
| Exists(p, set) -> 
    (match((teval p tenv),(teval set tenv)) with
    | (TFun(t1, t2), TSet(t3)) -> 
        if t1 = t3 
        then (if t2 = TBool then TBool else failwith("Exists: Not a predicate")) 
        else failwith("Exists: called on different set types.")
    | _ -> failwith("Exists: called on a non supported type"))
| Filter(p, set) -> 
    (match((teval p tenv),(teval set tenv)) with
    | (TFun(t1, t2), TSet(t3)) -> 
        if (t1 = t3 ) 
        then (if  t2 = TBool then TSet(t1) else failwith("Filter: Not a predicate")) 
        else failwith("Filter: Called on different set types")
    | _ -> failwith("Filter: called on a non supported type"))
| Map(f, set) -> 
    (match((teval f tenv),(teval set tenv)) with
    | (TFun(t1, t2), TSet(t3)) -> 
        if (t1 = t3) then TList(t2) else failwith("Map: Called on different set types")
    | _ -> failwith("Map: called on a non set or isn't a function."))
| Den(e)-> lookup tenv e
| Let(i, e1, e2) -> let t = teval e1 tenv in teval e2 (bind tenv i t)
| Fun(i, t1, e) -> let tenv1 = bind tenv i t1 in let t2 = teval e tenv1 in TFun(t1, t2)
| Letrec(f, arg, inputT, returnT, fBody, lBody) -> 
    let fEnv = bind tenv f (TFun(inputT, returnT)) in 
    let argEnv = bind fEnv arg inputT in 
    let t = teval fBody argEnv in 
    if t = (teval lBody argEnv) then t else failwith("LetRec: type fail.")  
| Apply(e1, e2) -> let f = (teval e1 tenv) in 
    (match f with 
    | TFun(t1,t2) -> 
        if ((teval e2 tenv) = t1) 
        then t2 
        else failwith("Apply: Wrong type.")
    | _ -> failwith("Apply: Wrong type."));; 