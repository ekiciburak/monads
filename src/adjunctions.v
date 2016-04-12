Require Import Morphisms.
Import ProperNotations.
Require Import SetoidClass.
Require notation categories prods_pullbacks functors natural_transformations monads.

Module Make(Import M: notation.T).
 Module Export adjunctions_exp := monads.Make(M).

Class Adjunction (catC catD: Category) (F: obj catC -> obj catD) (G: obj catD -> obj catC) 
                 (fmapF : forall (a b: obj catC) (f: arrow catC b a), (arrow catD (F b) (F a)))
                 (fmapG : forall (a b: obj catD) (f: arrow catD b a), (arrow catC (G b) (G a)))
                 `(@Functor catC catD F fmapF) 
                 `(@Functor catD catC G fmapG): Type :=
  {
     bijl : forall (b: obj catC) (a: obj catD), (arrow catD a (F b)) -> (arrow catC (G a) b);
     bijr : forall (b: obj catC) (a: obj catD), (arrow catC (G a) b) -> (arrow catD a (F b))
  }.
Check Adjunction.

End Make.
