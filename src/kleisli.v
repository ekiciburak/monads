Require Import Morphisms.
Import ProperNotations.
Require Import SetoidClass.
Require notation categories prods_pullbacks functors natural_transformations monads adjunctions.

Module Make(Import M: notation.T).
 Module Export kleisli_exp := adjunctions.Make(M).

Definition id {catC: Category} (a: catC) := a.

Theorem rcancel:  forall {catC: Category} {a b c: catC} (f g: arrow _ c b) (h: arrow _ b a), f = g -> f o h = g o h.
Proof. intros. rewrite H. reflexivity. Qed.

Theorem lcancel:  forall {catC: Category} {a b c: catC} (f g: arrow _ b a) (h: arrow _ c b), f = g -> h o f = h o g.
Proof. intros. rewrite H. reflexivity. Qed.

Definition Kleisli_Category `(catC: Category) (F: catC -> catC)
                            (fmapId : forall (a b: catC) (f: arrow catC b a), (arrow catC (id b) (id a)))
                            (fmapT  : forall (a b: catC) (f: arrow catC b a), (arrow catC (F b) (F a)))
                               (Id  : (Functor catC catC id fmapId))
                               (T   : (Functor catC catC F fmapT))
                               (T2  : (Functor catC catC (fun a: catC => F (F a)) (fun a b f => fmapT _ _ (fmapT _ _ f))))
                                   (eta : forall (a: catC), (arrow catC (F a) (id a)))
                                   (mu  : forall (a: catC), (arrow catC (F a) (F (F a))))
                                      (nt1: NaturalTransformation catC catC id F fmapId fmapT Id T eta) 
                                      (nt2: NaturalTransformation catC catC (fun a: catC => F (F a)) F (fun a b f => fmapT _ _ (fmapT _ _ f)) fmapT T2 T mu)
                                         (M: Monad catC F fmapId fmapT Id T T2 eta mu nt1 nt2) : (Category).
Proof. refine (@mk_Category (catC)
                            (fun a b => (@arrow catC (F b) (id a)))
                            (fun a => eta a) 
                            (fun a b c f g => (mu (id c)) o (fmapT _ _ g) o f)
                            _ ).
       intros. simpl. destruct nt1, nt2, M, T, T2. unfold adjunctions_exp.id, id in *. rewrite preserve_comp0.
       rewrite assoc. rewrite preserve_comp0. rewrite assoc. rewrite (comm_diagram3 a). do 2 rewrite assoc.
       specialize(@comm_diag1 b (F a) f). rewrite <- assoc. (* rewrite comm_diag1. ?? *) rewrite assoc.
       apply rcancel. apply rcancel. rewrite <- assoc.
       rewrite <- assoc. apply lcancel. rewrite comm_diag1. reflexivity. Qed.
Check Kleisli_Category.     

Definition coKleisli_Category (catC: Category) (F: catC -> catC)
                              (fmapId : forall (a b: catC) (f: arrow catC b a), (arrow catC (id b) (id a)))
                              (fmapD  : forall (a b: catC) (f: arrow catC b a), (arrow catC (F b) (F a)))
                                 (Id  : (Functor catC catC id fmapId))
                                 (D   : (Functor catC catC F fmapD))
                                 (D2  : (Functor catC catC (fun a: catC => F (F a)) (fun a b f => fmapD _ _ (fmapD _ _ f))))
                                    (epsilon : forall (a: catC), (arrow catC (id a) (F a)))
                                    (delta   : forall (a: catC), (arrow catC (F (F a)) (F a)))
                                       (nt1: NaturalTransformation catC catC F id fmapD fmapId D Id epsilon)
                                       (nt2: NaturalTransformation catC catC F (fun a: catC => F (F a)) fmapD (fun a b f => fmapD _ _ (fmapD _ _ f)) D D2 delta)
                                          (CM: coMonad catC F fmapId fmapD Id D D2 epsilon delta nt1 nt2) : (Category).
Proof. refine (@mk_Category (catC)
                            (fun a b => (@arrow catC (id b) (F a)))
                            (fun a => epsilon a) 
                            (fun a b c f g => g o (fmapD _ _ f) o (delta a))
                            _ ).
 (*to dualize*) admit. (*mind the admit here*) Qed.
Check coKleisli_Category.

End Make.
