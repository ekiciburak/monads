Require Import Morphisms.
Import ProperNotations.
Require Import SetoidClass.
Require notation categories prods_pullbacks functors natural_transformations monads adjunctions kleisli.

Module Make(Import M: notation.T).
 Module Export functor_categories_exp := kleisli.Make(M).

Axiom proof_irrelevance : forall (P : Prop) (p1 p2 : P), p1 = p2.

Definition Functor_Category (catC catD: Category) (F G: obj catC -> obj catD)
                            (trans : forall (a: obj catC), (arrow catD (G a) (F a))): Category.
Proof. refine (@mk_Category  {pFunctF: {F: obj catC -> obj catD  & 
                                (forall (a b: obj catC) (f: arrow catC b a), (arrow catD (F b) (F a)))} &
                                (Functor catC catD (projT1 pFunctF) (projT2 pFunctF))}
                             (fun FunctF FunctG => 
                                NaturalTransformation catC catD 
                                                     (projT1 (projT1 FunctF)) (projT1 (projT1 FunctG)) 
                                                     (projT2 (projT1 FunctF)) (projT2 (projT1 FunctG)) 
                                                     (projT2 FunctF) (projT2 FunctG))
                             (fun FunctF => 
                                IdentityNaturalTransformation catC catD
                                                              (projT1 (projT1 FunctF))  
                                                              (projT2 (projT1 FunctF)) 
                                                              (projT2 FunctF))
                             (fun FunctF FunctG FunctH nt1 nt2 =>
                                Compose_NaturalTransformations _ _ _ _ _ _ _ _
                                                               (projT2 FunctF) 
                                                               (projT2 FunctG)
                                                               (projT2 FunctH)
                                                               (nt1)
                                                               (nt2))
                             _ _ _ ). 
        - intros. simpl in *. Admitted.

(*
Lemma NaturalTransformations2_eq: forall   (catC catD: Category) 
                                           (F G     : obj catC -> obj catD)
                                           (FunctF  : @Functor2 catC catD F)
                                           (FunctG  : @Functor2 catC catD G)
                                           (nt1 nt2 : @NaturalTransformation2 catC catD F G FunctF FunctG),
(forall a: obj catC, (@trans2 _ _ _ _ _ _ nt1 a) = (@trans2  _ _ _ _ _ _ nt2 a)) ->
(forall (a b: obj catC) (f: arrow catC b a), (@comm_diag2 _ _ _ _ _ _ nt1 a b f) = (@comm_diag2  _ _ _ _ _ _ nt2 a b f)) ->
nt1 = nt2.
*)

Definition Functor_Category2 (catC catD: Category) (F G: obj catC -> obj catD)
                             (trans : forall (a: obj catC), (arrow catD (G a) (F a))): Category.
Proof. refine (@mk_Category  {F: obj catC -> obj catD  & (Functor2 catC catD F)}
                             (fun FunctF FunctG => 
                                NaturalTransformation2 catC catD 
                                                     (projT1 FunctF) (projT1 FunctG)
                                                     (projT2 FunctF) (projT2 FunctG))
                             (fun FunctF => 
                                IdentityNaturalTransformation2 catC catD
                                                               (projT1 FunctF)  
                                                               (projT2 FunctF))
                             (fun FunctF FunctG FunctH nt1 nt2 =>
                                Compose_NaturalTransformations2 _ _ _ _ _
                                                               (projT2 FunctF) 
                                                               (projT2 FunctG)
                                                               (projT2 FunctH)
                                                               (nt1)
                                                               (nt2))
                             _ _ _ ).  
        - intros. destruct f, g, h, a, b, c, d in *. simpl in *.
          unfold Compose_NaturalTransformations2, assoc. simpl.
          generalize trans2.
          assert ((fun a : obj catC => trans3 a o (trans4 a o trans5 a)) =
                  (fun a : obj catC => (trans3 a o trans4 a) o trans5 a)).
          { admit. } rewrite H.
          f_equal.
 eq_ind, eq_ind_r, eq_sym. simpl.
          subst.
          rewrite assoc.
          destruct f, f0, f1, f2. simpl in *.
          remember mk_Category. 
          unfold Compose_NaturalTransformations2. simpl.
          remember mk_Category.
          
          unfold Compose_NaturalTransformations2, eq_ind, eq_rect, assoc. simpl.
          rewrite <- assoc.

unfold assoc. simpl. rewrite assoc.
          repeat destruct Compose_NaturalTransformations2.
          rewrite (proof_irrelevance trans6 trans7).
          

 simpl.
          

 auto. easy.

 Admitted.
 
(* to complete: prove that Functor categories exist.
   required   : associativity of natural transformation composition
*)

End Make.