Require Import Morphisms.
Import ProperNotations.
Require Import SetoidClass.
Require notation categories prods_pullbacks functors natural_transformations.

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

Class coMonad (catC: Category) (F: catC -> catC)
              (fmapId : forall (a b: catC) (f: arrow catC b a), (arrow catC (id b) (id a)))
              (fmapD  : forall (a b: catC) (f: arrow catC b a), (arrow catC (F b) (F a)))
              (fmapD2 : forall (a b: catC) (f: arrow catC b a), (arrow catC (F (F b)) (F (F a))))
                        (IdD     : (Functor catC catC id fmapId))
                        (D       : (Functor catC catC F fmapD))
                        (D2      : (Functor catC catC (fun a: catC => F (F a)) fmapD2))
                        (epsilon : forall (a: catC), (arrow catC (id a) (F a)))
                        (delta   : forall (a: catC), (arrow catC (F (F a)) (F a)))
                          `(@NaturalTransformation catC catC F id fmapD fmapId D IdD epsilon)
                          `(@NaturalTransformation catC catC F (fun a: catC => F (F a)) fmapD fmapD2 D D2 delta): Type :=
  {
    cm_comm_diagram1    : forall (a: catC), (fmapD _ _ (delta a)) o (delta a) = (delta (F a)) o (delta a);
    cm_comm_diagram2    : forall (a: catC), (fmapD _ _ (epsilon a)) o (delta a) = (epsilon (F a)) o (delta a);
    cm_comm_diagram_b1  : forall (a: catC), (fmapD _ _ (epsilon a)) o (delta a) = (identity catC (F a));
    cm_comm_diagram_b2  : forall (a: catC), (epsilon (F a)) o (delta a) = (identity catC (F a))
  }.
Check coMonad.

End Make.
