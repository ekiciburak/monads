Require Import Morphisms.
Import ProperNotations.
Require Import SetoidClass.
Require notation categories functors natural_transformations.

Module Make(Import M: notation.T).
 Module Export monads_exp := natural_transformations.Make(M).

Class Monad (catC: Category) (F: catC -> catC)
            (fmapId : forall (a b: catC) (f: arrow catC b a), (arrow catC (id b) (id a)))
            (fmapT  : forall (a b: catC) (f: arrow catC b a), (arrow catC (F b) (F a)))
            (fmapT2 : forall (a b: catC) (f: arrow catC b a), (arrow catC (F (F b)) (F (F a))))
                        (IdF : (Functor catC catC id fmapId))
                        (T   : (Functor catC catC F fmapT))
                        (T2  : (Functor catC catC (fun a: catC => F (F a)) fmapT2))
                        (eta : forall (a: catC), (arrow catC (F a) (id a)))
                        (mu  : forall (a: catC), (arrow catC (F a) (F (F a))))
                          `(@NaturalTransformation catC catC id F fmapId fmapT IdF T eta)
                          `(@NaturalTransformation catC catC (fun a: catC => F (F a)) F fmapT2 fmapT T2 T mu): Type :=
  {
    comm_diagram1   : forall (a: catC), (mu a) o (fmapT _ _  (mu a)) = (mu a) o (mu (F a));
    comm_diagram2   : forall (a: catC), (mu a) o (fmapT _ _ (eta a)) = (mu a) o (eta (F a));
    comm_diagram2_b1: forall (a: catC), (mu a) o (fmapT _ _ (eta a)) =  (identity catC (F a));
    comm_diagram2_b2: forall (a: catC), (mu a) o (eta (F a)) =  (identity catC (F a))
  }.
Check Monad.

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