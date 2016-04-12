Require Import Morphisms.
Import ProperNotations.
Require Import SetoidClass.
Require notation categories prods_pullbacks functors natural_transformations.

Module Make(Import M: notation.T).
 Module Export monads_exp := natural_transformations.Make(M).

Class Monad (catC: Category) (F: catC -> catC)
            (fmapT  : forall (a b: catC) (f: arrow catC b a), (arrow catC (F b) (F a)))
                        (Id  : (Functor catC catC id (fun a b f => (@idf catC a b f))))
                        (T   : (Functor catC catC F fmapT))
                        (T2  : (Functor catC catC (fun a: catC => F (F a)) (fun a b f => fmapT _ _ (fmapT _ _ f))))
                        (eta : forall (a: catC), (arrow catC (F a) (id a)))
                        (mu  : forall (a: catC), (arrow catC (F a) (F (F a))))
                          `(@NaturalTransformation catC catC id F (fun a b f => (@idf catC a b f)) fmapT Id T eta)
                          `(@NaturalTransformation catC catC (fun a: catC => F (F a)) F (fun a b f => fmapT _ _ (fmapT _ _ f)) fmapT T2 T mu): Type :=
  {
    comm_diagram1   : forall (a: catC), (mu a) o (fmapT _ _  (mu a)) = (mu a) o (mu (F a));
    comm_diagram2   : forall (a: catC), (mu a) o (fmapT _ _ (eta a)) = (mu a) o (eta (F a));
    comm_diagram2_b1: forall (a: catC), (mu a) o (fmapT _ _ (eta a)) =  (identity catC (F a));
    comm_diagram2_b2: forall (a: catC), (mu a) o (eta (F a)) =  (identity catC (F a))
  }.
Check Monad.

Class coMonad (catC: Category) (F: catC -> catC)
              (fmapD  : forall (a b: catC) (f: arrow catC b a), (arrow catC (F b) (F a)))
                        (Id      : (Functor catC catC id (fun a b f => (@idf catC a b f))))
                        (D       : (Functor catC catC F fmapD))
                        (D2      : (Functor catC catC (fun a: catC => F (F a)) (fun a b f => fmapD _ _ (fmapD _ _ f))))
                        (epsilon : forall (a: catC), (arrow catC (id a) (F a)))
                        (delta   : forall (a: catC), (arrow catC (F (F a)) (F a)))
                          `(@NaturalTransformation catC catC F id fmapD (fun a b f => (@idf catC a b f)) D Id epsilon)
                          `(@NaturalTransformation catC catC F (fun a: catC => F (F a)) fmapD (fun a b f => fmapD _ _ (fmapD _ _ f)) D D2 delta): Type :=
  {
    cm_comm_diagram1    : forall (a: catC), (fmapD _ _ (delta a)) o (delta a) = (delta (F a)) o (delta a);
    cm_comm_diagram2    : forall (a: catC), (fmapD _ _ (epsilon a)) o (delta a) = (epsilon (F a)) o (delta a);
    cm_comm_diagram_b1  : forall (a: catC), (fmapD _ _ (epsilon a)) o (delta a) = (identity catC (F a));
    cm_comm_diagram_b2  : forall (a: catC), (epsilon (F a)) o (delta a) = (identity catC (F a))
  }.
Check coMonad.

End Make.
