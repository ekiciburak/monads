Require Import Morphisms.
Import ProperNotations.
Require Import SetoidClass.
Require notation categories prods_pullbacks functors natural_transformations monads adjunctions.

Module Make(Import M: notation.T).
 Module Export kleisli_exp := adjunctions.Make(M).

Class Kleisli `(catC: Category) (F: catC -> catC)
              (fmapId : forall (a b: catC) (f: arrow catC b a), (arrow catC (id b) (id a)))
              (fmapT  : forall (a b: catC) (f: arrow catC b a), (arrow catC (F b) (F a)))
              (fmapT2 : forall (a b: catC) (f: arrow catC b a), (arrow catC (F (F b)) (F (F a))))
                        (IdF : (Functor catC catC id fmapId))
                        (T   : (Functor catC catC F fmapT))
                        (T2  : (Functor catC catC (fun a: catC => F (F a)) fmapT2))
                        (eta : forall (a: catC), (arrow catC (F a) (id a)))
                        (mu  : forall (a: catC), (arrow catC (F a) (F (F a))))
                          (nt1: NaturalTransformation catC catC id F fmapId fmapT IdF T eta) 
                          (nt2: NaturalTransformation catC catC (fun a: catC => F (F a)) F fmapT2 fmapT T2 T mu)
                          `(@Monad catC F fmapId fmapT fmapT2 IdF T T2 eta mu nt1 nt2) : Type :=
{ 
   Kl_obj := obj catC;
   Kl_arrow (a b: catC) (f: arrow catC (F b) a) := arrow _ b a;
   Kl_comp (a b c: catC) (f: arrow catC (F b) a) (g: arrow catC (F c) b):= (mu c) o (fmapT _ _ g) o f;
   Kl_comp_assoc (a b c d: catC) (f : arrow catC (F b) a) (g : arrow catC (F c) b) (h : arrow catC (F d) c):= 
      (Kl_comp _ _ _  (Kl_comp _ _ _ f g) h) = (Kl_comp _ _ _  f (Kl_comp _ _ _ g h))
}.
Check Kleisli.

End Make.
