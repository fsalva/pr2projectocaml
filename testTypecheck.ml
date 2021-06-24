let test (x:texp) = teval x [];; 

let eqq = Eq(EInt(3), EInt(4));;

let s1 = OfSet(TInt, Element(EInt(3), Element(EInt(5), End )));;

let greaterThan3 = Fun("x", TInt, GT(Den("x"), EInt(3)));;

let map1 = Map(greaterThan3, s1);;
