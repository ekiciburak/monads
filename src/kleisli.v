Require Import Morphisms.
Import ProperNotations.
Require Import SetoidClass.
Require notation categories prods_pullbacks functors natural_transformations monads adjunctions.

Module Make(Import M: notation.T).
 Module Export kleisli_exp := adjunctions.Make(M).

Definition id {catC: Category} (a: catC) := a.

Definition Kleisli `(catC: Category) (F: catC -> catC)
              (fmapId : forall (a b: catC) (f: arrow catC b a), (arrow catC (id b) (id a)))
              (fmapT  : forall (a b: catC) (f: arrow catC b a), (arrow catC (F b) (F a)))
              (fmapT2 : forall (a b: catC) (f: arrow catC b a), (arrow catC (F (F b)) (F (F a))))
                        (Id  : (Functor catC catC id fmapId))
                        (T   : (Functor catC catC F fmapT))
                        (T2  : (Functor catC catC (fun a: catC => F (F a)) fmapT2))
                        (eta : forall (a: catC), (arrow catC (F a) (id a)))
                        (mu  : forall (a: catC), (arrow catC (F a) (F (F a))))
                          (nt1: NaturalTransformation catC catC id F fmapId fmapT Id T eta) 
                          (nt2: NaturalTransformation catC catC (fun a: catC => F (F a)) F fmapT2 fmapT T2 T mu)
                          `(@Monad catC F fmapId fmapT fmapT2 Id T T2 eta mu nt1 nt2) : (Category).
Proof. refine (@mk_Category (catC)
                            (fun a b => (@arrow catC (F b) (id a)))
                            (fun a => eta a) 
                            (fun a b c f g => (mu (id c)) o (fmapT _ _ g) o f)
_ ). intros. simpl. destruct nt1, nt2. do 2 rewrite assoc. unfold id in *. remember (comm_diag1 _ _ f).
destruct H. admit. (* to be proven *) Qed.
Check Kleisli.

Definition coKleisli (catC: Category) (F: catC -> catC)
                (fmapId : forall (a b: catC) (f: arrow catC b a), (arrow catC (id b) (id a)))
                (fmapD  : forall (a b: catC) (f: arrow catC b a), (arrow catC (F b) (F a)))
                (fmapD2 : forall (a b: catC) (f: arrow catC b a), (arrow catC (F (F b)) (F (F a))))
                        (Id      : (Functor catC catC id fmapId))
                        (D       : (Functor catC catC F fmapD))
                        (D2      : (Functor catC catC (fun a: catC => F (F a)) fmapD2))
                        (epsilon : forall (a: catC), (arrow catC (id a) (F a)))
                        (delta   : forall (a: catC), (arrow catC (F (F a)) (F a)))
                          (nt1: NaturalTransformation catC catC F id fmapD fmapId D Id epsilon)
                          (nt2: NaturalTransformation catC catC F (fun a: catC => F (F a)) fmapD fmapD2 D D2 delta)
                            `(@coMonad catC F fmapId fmapD fmapD2 Id D D2 epsilon delta nt1 nt2) : (Category).
Proof. refine (@mk_Category (catC)
                            (fun a b => (@arrow catC (id b) (F a)))
                            (fun a => epsilon a) 
                            (fun a b c f g => g o (fmapD _ _ f) o (delta a))
_ ). intros. simpl. destruct nt1, nt2. rewrite <- assoc. unfold id in *. remember (comm_diag1 _ _ f).
destruct H. admit. (* to be proven *) Qed.
Check coKleisli.

(** mind these admits above. TODO:= prove associativity for Kleisli and coKleisli compositions. **)

(*
Class Kleisli `(catC: Category) (F: catC -> catC)
              (fmapId : forall (a b: catC) (f: arrow catC b a), (arrow catC (id b) (id a)))
              (fmapT  : forall (a b: catC) (f: arrow catC b a), (arrow catC (F b) (F a)))
              (fmapT2 : forall (a b: catC) (f: arrow catC b a), (arrow catC (F (F b)) (F (F a))))
                        (Id  : (Functor catC catC id fmapId))
                        (T   : (Functor catC catC F fmapT))
                        (T2  : (Functor catC catC (fun a: catC => F (F a)) fmapT2))
                        (eta : forall (a: catC), (arrow catC (F a) (id a)))
                        (mu  : forall (a: catC), (arrow catC (F a) (F (F a))))
                          (nt1: NaturalTransformation catC catC id F fmapId fmapT Id T eta) 
                          (nt2: NaturalTransformation catC catC (fun a: catC => F (F a)) F fmapT2 fmapT T2 T mu)
                          `(@Monad catC F fmapId fmapT fmapT2 Id T T2 eta mu nt1 nt2) : Type :=
{ 
   Kl_obj := obj catC;
   Kl_arrow (a b: catC) (f: arrow catC (F b) a) := arrow _ b a;
   Kl_identity (a: catC) := eta a;
   Kl_comp (a b c: catC) (f: arrow catC (F b) a) (g: arrow catC (F c) b):= (mu c) o (fmapT _ _ g) o f;
   Kl_comp_assoc (a b c d: catC) (f : arrow catC (F b) a) (g : arrow catC (F c) b) (h : arrow catC (F d) c):= 
      (Kl_comp _ _ _  (Kl_comp _ _ _ f g) h) = (Kl_comp _ _ _  f (Kl_comp _ _ _ g h))
}.
Check Kleisli.


Class coKleisli (catC: Category) (F: catC -> catC)
                (fmapId : forall (a b: catC) (f: arrow catC b a), (arrow catC (id b) (id a)))
                (fmapD  : forall (a b: catC) (f: arrow catC b a), (arrow catC (F b) (F a)))
                (fmapD2 : forall (a b: catC) (f: arrow catC b a), (arrow catC (F (F b)) (F (F a))))
                        (Id      : (Functor catC catC id fmapId))
                        (D       : (Functor catC catC F fmapD))
                        (D2      : (Functor catC catC (fun a: catC => F (F a)) fmapD2))
                        (epsilon : forall (a: catC), (arrow catC (id a) (F a)))
                        (delta   : forall (a: catC), (arrow catC (F (F a)) (F a)))
                          (nt1: NaturalTransformation catC catC F id fmapD fmapId D Id epsilon)
                          (nt2: NaturalTransformation catC catC F (fun a: catC => F (F a)) fmapD fmapD2 D D2 delta)
                            `(@coMonad catC F fmapId fmapD fmapD2 Id D D2 epsilon delta nt1 nt2) : Type :=
{ 
   coKl_obj := obj catC;
   coKl_arrow (a b: catC) (f: arrow catC b (F a)) := arrow _ b a;
   coKl_identity (a: catC) := epsilon a;
   coKl_comp (a b c: catC) (f: arrow catC b (F a)) (g: arrow catC c (F b)):= g o (fmapD _ _ f) o (delta a);
   coKl_comp_assoc (a b c d: catC) (f : arrow catC b (F a)) (g : arrow catC c (F b)) (h : arrow catC d (F c)):= 
      (coKl_comp _ _ _  (coKl_comp _ _ _ f g) h) = (coKl_comp _ _ _  f (coKl_comp _ _ _ g h))
}.
Check coKleisli.

*)

End Make.
