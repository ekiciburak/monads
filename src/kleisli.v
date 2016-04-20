Require Import Morphisms.
Import ProperNotations.
Require Import SetoidClass.
Require notation categories prods_pullbacks functors natural_transformations monads adjunctions.

Module Make(Import M: notation.T).
 Module Export kleisli_exp := adjunctions.Make(M).

Definition Kleisli_Category (catC : Category) (F: obj catC -> obj catC)
                            (fmapT: forall (a b: obj catC) (f: arrow catC b a), (arrow catC (F b) (F a)))
                            (Id   : (Functor catC catC id (fun a b f => (@idf catC a b f))))
                            (T    : (Functor catC catC F fmapT))
                            (T2   : (Functor catC catC (fun a: obj catC => F (F a)) (fun a b f => fmapT _ _ (fmapT _ _ f))))
                            (nt1  : @NaturalTransformation catC catC id F (fun a b f => (@idf catC a b f)) fmapT Id T) 
                            (nt2  : @NaturalTransformation catC catC (fun a: obj catC => F (F a)) F
                                   (fun a b f => fmapT _ _ (fmapT _ _ f)) fmapT T2 T)
                            (M    : @Monad catC F fmapT Id T T2 nt1 nt2) : (Category).
Proof. refine (@mk_Category (obj catC)
                            (fun a b => (@arrow catC (F b) (id a)))
                            (fun a => (@trans _ _ _ _ _ _ _ _ nt1 a)) 
                            (fun a b c f g => ((@trans _ _ _ _ _ _ _ _ nt2 (id c))) o (fmapT _ _ g) o f)
                            _ _ _ ).
       - intros. simpl. destruct nt1, nt2, M, T, T2. simpl in *. unfold id in *. rewrite preserve_comp0.
         rewrite assoc. rewrite preserve_comp0. rewrite assoc. rewrite (comm_diagram3 a). do 2 rewrite assoc.
         specialize(@comm_diag4 b (F a) f). (* rewrite comm_diag1. ?? *) apply rcancel. apply rcancel. 
         rewrite <- assoc. rewrite <- assoc. rewrite comm_diag4. reflexivity.
       - intros. unfold id in *. destruct nt1, nt2, M, T, T2.  simpl in *. unfold id in *.
         specialize (@comm_diag3 b (F a) f). rewrite <- assoc. rewrite comm_diag3. rewrite assoc.
         rewrite comm_diagram2_b4. rewrite identity_f. unfold idf. reflexivity.
       - intros. unfold id in *. destruct nt1, nt2, M, T, T2. simpl in *. unfold id in *. 
          rewrite comm_diagram4, comm_diagram2_b4, identity_f. reflexivity.
Defined.
Check Kleisli_Category.    

Definition coKleisli_Category (catC: Category) (F: obj catC -> obj catC)
                              (fmapD : forall (a b: obj catC) (f: arrow catC b a), (arrow catC (F b) (F a)))
                              (Id  : (Functor catC catC id (fun a b f => (@idf catC a b f))))
                              (D   : (Functor catC catC F fmapD))
                              (D2  : (Functor catC catC (fun a: obj catC => F (F a)) (fun a b f => fmapD _ _ (fmapD _ _ f))))
                              (nt1 : NaturalTransformation catC catC F id fmapD (fun a b f => (@idf catC a b f)) D Id)
                              (nt2 : NaturalTransformation catC catC F (fun a: obj catC => F (F a))
                                     fmapD (fun a b f => fmapD _ _ (fmapD _ _ f)) D D2)
                              (CM  : coMonad catC F fmapD Id D D2 nt1 nt2) : (Category).
Proof. refine (@mk_Category (obj catC)
                            (fun a b => (@arrow catC (id b) (F a)))
                            (fun a => (@trans _ _ _ _ _ _ _ _ nt1 a)) 
                            (fun a b c f g => g o (fmapD _ _ f) o (@trans _ _ _ _ _ _ _ _ nt2 a))
                            _ _ _ ).
      - intros. simpl. destruct nt1, nt2, CM, D, D2. simpl in *. unfold id in *. rewrite preserve_comp0.
         rewrite assoc. rewrite preserve_comp0. do 5 rewrite <- assoc. rewrite (cm_comm_diagram3 d).
         do 5 rewrite assoc.  apply rcancel. specialize(@comm_diag4 (F d) c h). rewrite <- assoc.
         rewrite <- comm_diag4. do 2 rewrite assoc. reflexivity.
      - intros. unfold id in *. destruct nt1, nt2, CM, D, D2. simpl in *. unfold id in *. rewrite <- assoc.
         rewrite cm_comm_diagram4, cm_comm_diagram_b4, f_identity. reflexivity.
      - intros. unfold id in *. destruct nt1, nt2, CM, D, D2. simpl in *. unfold id in *. rewrite <- comm_diag3.
         rewrite <- assoc. rewrite cm_comm_diagram_b4, f_identity. unfold idf; reflexivity.
Defined.
Check coKleisli_Category.


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
                             _
                             _ _ _ ). intros. Admitted. 

(* to complete *)

End Make.
   