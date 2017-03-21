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

Program Instance Id (catC: Category): (@Functor2 catC catC id).
Check IdentityFunctor2.

Program Instance T (catC catD: Category)
                    (F: obj catC -> obj catD) (G: obj catD -> obj catC)
                    (fmapF: @Functor2 catC catD F)
                    (fmapG: @Functor2 catD catC G):
                    (@Functor2 catC catC (fun a: obj catC => G (F a))).
Next Obligation. destruct fmapF, fmapG. apply fmap4, fmap3, f0. Defined.
Next Obligation. unfold T_obligation_1. destruct fmapF, fmapG.
                 now rewrite preserve_id3, preserve_id4. Defined.
Next Obligation. unfold T_obligation_1. destruct fmapF, fmapG.
                 now rewrite preserve_comp3, preserve_comp4. Defined.

Program Instance T2 (catC catD: Category)
                    (F: obj catC -> obj catD) (G: obj catD -> obj catC)
                    (fmapF: @Functor2 catC catD F)
                    (fmapG: @Functor2 catD catC G):
                    (@Functor2 catC catC (fun a: obj catC => G (F (G (F a))))).
Next Obligation. destruct fmapF, fmapG. apply fmap4, fmap3, fmap4, fmap3, f0. Defined.
Next Obligation. unfold T2_obligation_1. destruct fmapF, fmapG.
                 now rewrite preserve_id3, preserve_id4, preserve_id3, preserve_id4. Defined.
Next Obligation. unfold T2_obligation_1. destruct fmapF, fmapG.
                 now rewrite preserve_comp3, preserve_comp4, preserve_comp3, preserve_comp4. Defined.

Lemma asd: forall (catC catD: Category)
                  (F: obj catC -> obj catD) (G: obj catD -> obj catC)
                  (fmapF: @Functor2 catC catD F)
                  (fmapG: @Functor2 catD catC G)
                  (eta  : @NaturalTransformation2 catC catC
                          id 
                          (fun a => G (F a)) 
                          (Id catC) 
                          (T catC catD F G fmapF fmapG)) 
                  (mu   : @NaturalTransformation2 catC catC 
                          (fun a: obj catC => G (F (G (F a))))
                          (fun a => G (F a)) 
                          (T2 catC catD F G fmapF fmapG)
                          (T catC catD F G fmapF fmapG)),
                  Adjunction2 catC catD F G fmapF fmapG ->
                  Monad2 catC (fun a => G (F a)) 
                    (IdentityFunctor2 catC) 
                    (T catC catD F G fmapF fmapG) 
                    (T2 catC catD F G fmapF fmapG)
                    eta 
                    mu.
Proof. Admitted.


End Make.