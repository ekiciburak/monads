Require Import Morphisms.
Import ProperNotations.
Require Import SetoidClass.
Require notation categories prods_pullbacks functors natural_transformations monads.

Module Make(Import M: notation.T).
 Module Export adjunctions_exp := monads.Make(M).

(*
Definition Hom (catC: Category) (a b : obj catC) := arrow catC a b.
*)

Class Hom (catC: Category) (a b: obj catC): Type :=
  {
    f : arrow catC a b 
  }.

Class bijection (catC catD: Category)
                (a: obj catC) (b: obj catD)
                (F: obj catC -> obj catD) (G: obj catD -> obj catC): Prop := 
  {
    lbij: Hom catC a (G b) -> Hom catD (F a) b;
    rbij: Hom catD (F a) b -> Hom catC a (G b);
    ob1 : forall x: Hom catC a (G b), rbij (lbij x) = x;
    ob2 : forall y: Hom catD (F a) b, lbij (rbij y) = y 
  }.

Class Adjunction (catC catD: Category)
                 (F: obj catC -> obj catD) (G: obj catD -> obj catC) 
                 (fmapF : forall (a b: obj catC) (f: arrow catC b a), (arrow catD (F b) (F a)))
                 (fmapG : forall (a b: obj catD) (f: arrow catD b a), (arrow catC (G b) (G a)))
                 (FunctF: @Functor catC catD F fmapF) 
                 (FunctG: @Functor catD catC G fmapG): Prop :=
  { bijob : forall (a: obj catC) (b: obj catD) 
                   (ha: Hom catC a (G b)) (hb: Hom catD (F a) b),
                   bijection catC catD a b F G
  }.

Class Adjunction2 (catC catD: Category) 
                  (F: obj catC -> obj catD) (G: obj catD -> obj catC)
                 `(@Functor2 catC catD F)
                 `(@Functor2 catD catC G): Type :=
  mk_Adjunction2
  {  bijob2 : forall (a: obj catC) (b: obj catD) 
                     (ha: Hom catC a (G b)) (hb: Hom catD (F a) b),
                     bijection catC catD a b F G
  }.

Program Instance Id (catC: Category): (@Functor catC catC id (fun a b (f: arrow catC b a) => f)).

Program Instance T  (catC catD: Category)
                    (F: obj catC -> obj catD) 
                    (G: obj catD -> obj catC)
                    (fmapF : forall (a b: obj catC) (f: arrow catC b a), (arrow catD (F b) (F a)))
                    (fmapG : forall (a b: obj catD) (f: arrow catD b a), (arrow catC (G b) (G a)))
                    (FunctF: @Functor catC catD F fmapF) 
                    (FunctG: @Functor catD catC G fmapG):
                    (@Functor catC catC (fun a: obj catC => G (F a)) (fun a b f => fmapG _ _ (fmapF _ _ f))).
Next Obligation. destruct FunctF, FunctG.
                 now rewrite preserve_id0, preserve_id1. Defined.
Next Obligation. destruct FunctF, FunctG.
                 now rewrite preserve_comp0, preserve_comp1. Defined.

Program Instance T2 (catC catD: Category)
                    (F: obj catC -> obj catD) 
                    (G: obj catD -> obj catC)
                    (fmapF : forall (a b: obj catC) (f: arrow catC b a), (arrow catD (F b) (F a)))
                    (fmapG : forall (a b: obj catD) (f: arrow catD b a), (arrow catC (G b) (G a)))
                    (FunctF: @Functor catC catD F fmapF) 
                    (FunctG: @Functor catD catC G fmapG):
                    (@Functor catC catC (fun a: obj catC => G (F (G (F a)))) 
                                        (fun a b f => fmapG _ _ (fmapF _ _ (fmapG _ _ (fmapF _ _ f))))).
Next Obligation. destruct FunctF, FunctG.
                 now rewrite preserve_id0, preserve_id1, preserve_id0, preserve_id1. Defined.
Next Obligation. destruct FunctF, FunctG.
                 now rewrite preserve_comp0, preserve_comp1, preserve_comp0, preserve_comp1. Defined.


(** an adjunction gives raise to a monad *)
Lemma eq_adj_mon: forall (catC catD: Category)
                  (F     : obj catC -> obj catD)
                  (G     : obj catD -> obj catC)
                  (fmapF : forall (a b: obj catC) (f: arrow catC b a), (arrow catD (F b) (F a)))
                  (fmapG : forall (a b: obj catD) (f: arrow catD b a), (arrow catC (G b) (G a)))
                  (FunctF: @Functor catC catD F fmapF) 
                  (FunctG: @Functor catD catC G fmapG)
                  (eta   : @NaturalTransformation catC catC
                            id 
                            (fun a => G (F a))
                            (fun a b (f: arrow catC b a) => f)
                            (fun a b f => fmapG _ _ (fmapF _ _ f))
                            (Id catC) 
                            (T catC catD F G fmapF fmapG FunctF FunctG)) 
                  (mu   : @NaturalTransformation catC catC 
                            (fun a: obj catC => G (F (G (F a))))
                            (fun a => G (F a))
                            (fun a b f => fmapG _ _ (fmapF _ _ (fmapG _ _ (fmapF _ _ f))))
                            (fun a b f => fmapG _ _ (fmapF _ _ f))
                            (T2 catC catD F G fmapF fmapG FunctF FunctG)
                            (T catC catD F G fmapF fmapG FunctF FunctG)),
                  Adjunction catC catD F G fmapF fmapG FunctF FunctG ->
                  Monad catC 
                        (fun a => G (F a))
                        (fun a b f => fmapG _ _ (fmapF _ _ f))
                        (Id catC)
                        (T catC catD F G fmapF fmapG FunctF FunctG) 
                        (T2 catC catD F G fmapF fmapG FunctF FunctG)
                        eta 
                        mu.
Proof. intros. destruct H, eta, mu, FunctF, FunctG. simpl. Admitted.


End Make.