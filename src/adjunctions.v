Require Import Morphisms.
Import ProperNotations.
Require Import SetoidClass.
Require notation categories prods_pullbacks functors natural_transformations monads.

Module Make(Import M: notation.T).
 Module Export adjunctions_exp := monads.Make(M).


Class Adjunction (catC catD: Category) (F: catC -> catD) (G: catD -> catC) 
                 (fmapF : forall (a b: catC) (f: arrow catC b a), (arrow catD (F b) (F a)))
                 (fmapG : forall (a b: catD) (f: arrow catD b a), (arrow catC (G b) (G a)))
                 `(@Functor catC catD F fmapF) 
                 `(@Functor catD catC G fmapG): Type :=
  {
     bijl : forall (b: catC) (a: catD), (arrow catD a (F b)) -> (arrow catC (G a) b);
     bijr : forall (b: catC) (a: catD), (arrow catC (G a) b) -> (arrow catD a (F b))
  }.
Check Adjunction.

End Make.
