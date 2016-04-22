Require Import Morphisms.
Import ProperNotations.
Require Import SetoidClass.
Require notation categories prods_pullbacks functors natural_transformations monads adjunctions kleisli.

Module Make(Import M: notation.T).
 Module Export functor_categories_exp := kleisli.Make(M).

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
        - intros. destruct f, g, h. simpl in *. Admitted.
 
(* to complete: prove that Fucntor categories exist.
   required   : associativity of natural transformation composition
*)

End Make.