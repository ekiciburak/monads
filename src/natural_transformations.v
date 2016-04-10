Require Import Morphisms.
Import ProperNotations.
Require Import SetoidClass.
Require notation categories prods_pullbacks functors.

Module Make(Import M: notation.T).
 Module Export natural_transformations_exp := functors.Make(M).

Class NaturalTransformation (catC catD: Category) (F G: catC -> catD) 
                            (fmapF : forall (a b: catC) (f: arrow catC b a), (arrow catD (F b) (F a)))
                            (fmapG : forall (a b: catC) (f: arrow catC b a), (arrow catD (G b) (G a)))
                            `(@Functor catC catD F fmapF) 
                            `(@Functor catC catD G fmapG) 
                                                  (trans : forall (a: catC), (arrow catD (G a) (F a))): Type :=
  {
    comm_diag: forall {a b: catC} (f: arrow catC b a), fmapG _ _ f o trans a = trans b o fmapF _ _ f
  }.
Check NaturalTransformation.

End Make.
