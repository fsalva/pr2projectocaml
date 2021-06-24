let test (e:exp) = eval e [];;

(* COSTRUTTORI *)
let s1 = OfSet("int", Element(CstInt(3), Element(CstInt(5), End )));;
let s2 = Empty("int");;
let s3 = Singleton("int", Sum(CstInt(2), CstInt(3)));;
let sset1 = OfSet("string", Element(CstString("hello"), Element(CstString("world"), Element(CstString("!"), End))));;

(* INSERT *)
let ins1 = Insert(Times(CstInt(1), CstInt(3)), s3);; (* non viene inserito. *)
let ins2 = Insert(CstInt(7), s3);;

(* REMOVE *)
let rm1 = Remove(CstInt(7), ins2);;
let rm2 = Remove(CstInt(7), ins2);; (* ignorato *)
let rm3 = Remove(CstString("Test"), ins2);; (* non passa il typecheck. *)

(* ISEMPTY *)
let ie1 = IsEmpty(s2);; (* true *)
let ie2 = IsEmpty(s3);; (* false *)

(* MEMBER *)
let mb1 = Member(CstString("!"), sset1);; (* true *)
let mb2 = Member(CstString("Nope!"), sset1);; (* false *)

(* SUBSET *)
let sub1 = Subset(s2, s3);; (* true *)
let sub2 = Subset(s3, s1);; (* true *)
let sub3 = Subset(s1, s3);; (* false *)

(* UNION *)
let un1 = Union(ins2, Singleton("int", CstInt(9)));;

(* INTERSECT *)
let is1 = Intersect(un1, Singleton("int", CstInt(9)));;
(* DIFF *)
let dif1 = Diff(is1, Singleton("int", CstInt(10)));; (*unchanged*)
let dif2 = Diff(is1, Singleton("int", CstInt(9)));; (*empty*)

(* MINSET *)
let min1 = MinSet(ins2);;
let min2 = MinSet(sset1);; (* non passa il typecheck *)
(* MAXSET *)
let max1 = MaxSet(ins2);; 

(* Funzioni e predicati per testare gli operatori funzionali.*)
let add1 = Fun("x", Sum(Den("x"), CstInt(1)));;
let greaterThan3 = Fun("x", GT(Den("x"), CstInt(3)));;

(* FOR ALL *)
let fa = ForAll(greaterThan3, ins2);;
(* EXISTS *)
let exs = Exists(greaterThan3, ins2);;

(* FILTER *)
let filt = Filter(greaterThan3, ins2);;

(* MAP *)
let mp = Map(add1, ins2);;

