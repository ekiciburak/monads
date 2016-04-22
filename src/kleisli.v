Require Import Morphisms.
Import ProperNotations.
Require Import SetoidClass.
Require notation categories prods_pullbacks functors natural_transformations monads adjunctions.

Module Make(Import M: notation.T).
 Module Export kleisli_exp := adjunctions.Make(M).

Definition Kleisli_Category' (catC : Category) 
                             (F    : obj catC -> obj catC)
                             (fmapT: forall (a b: obj catC) (f: arrow catC b a), (arrow catC (F b) (F a)))
                             (T    : Functor catC catC F fmapT)
                             (M    : @Monad' catC F fmapT T) : (Category).
Proof. destruct M. destruct nt3, nt4.
       refine (@mk_Category (obj catC)
                            (fun a b           => (@arrow catC (F b) a))
                            (fun a             => (@trans0 a)) 
                            (fun a b c f g     => (@trans1 c) o (fmapT _ _ g) o f)
                            _ _ _ ).
       - intros. simpl. destruct T, T3. simpl in *. unfold id in *. rewrite preserve_comp0.
         rewrite assoc. rewrite preserve_comp0. rewrite assoc. rewrite (comm_diagram1''0 a). do 2 rewrite assoc.
         specialize(@comm_diag1 b (F a) f). (* rewrite comm_diag1. ?? *) apply rcancel. apply rcancel. 
         rewrite <- assoc. rewrite <- assoc. rewrite comm_diag1. reflexivity.
       - intros. unfold id in *. destruct T, T3.  simpl in *. unfold id in *.
         specialize (@comm_diag0 b (F a) f). rewrite <- assoc. rewrite comm_diag0. rewrite assoc.
         rewrite comm_diagram2_b2''0. rewrite identity_f. unfold idf. reflexivity.
       - intros. unfold id in *. destruct T, T3. simpl in *. unfold id in *. 
          rewrite comm_diagram2''0, comm_diagram2_b2''0, identity_f. reflexivity.
Defined.
Check Kleisli_Category'.

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
         specialize(@comm_diag1 b (F a) f). (* rewrite comm_diag1. ?? *) apply rcancel. apply rcancel. 
         rewrite <- assoc. rewrite <- assoc. rewrite comm_diag1. reflexivity.
       - intros. unfold id in *. destruct nt1, nt2, M, T, T2.  simpl in *. unfold id in *.
         specialize (@comm_diag0 b (F a) f). rewrite <- assoc. rewrite comm_diag0. rewrite assoc.
         rewrite comm_diagram2_b4. rewrite identity_f. unfold idf. reflexivity.
       - intros. unfold id in *. destruct nt1, nt2, M, T, T2. simpl in *. unfold id in *. 
          rewrite comm_diagram4, comm_diagram2_b4, identity_f. reflexivity.
Defined.
Check Kleisli_Category.


Definition Kleisli_Category2 (catC : Category) (F: obj catC -> obj catC)
                             (Id   : (Functor2 catC catC id))
                             (T    : (Functor2 catC catC F))
                             (T2   : (Functor2 catC catC (fun a: obj catC => F (F a))))
                             (nt1  : @NaturalTransformation2 catC catC id F Id T) 
                             (nt2  : @NaturalTransformation2 catC catC (fun a: obj catC => F (F a)) F T2 T)
                             (M    : @Monad2 catC F Id T T2 nt1 nt2): 
                             (forall a b f, (@fmap2 _ _ _ T2 a b f) = (@fmap2 _ _ _ T _ _ (@fmap2 _ _ _ T _ _ f))) ->
                             (forall a b f, (@fmap2 _ _ _ Id a b f) = (@idf catC a b f))
                             -> (Category).
Proof. intros. refine (@mk_Category (obj catC)
                            (fun a b       => (@arrow catC (F b) (id a)))
                            (fun a         => (@trans2 _ _ _ _ _ _ nt1 a))
                            (fun a b c f g => (@trans2 _ _ _ _ _ _ nt2 (id c)) o (@fmap2 _ _ _ T _ _ g) o f)
                            _
                            _
                            _
               ).
       - intros. simpl. destruct nt1, nt2, M, T, T2. simpl in *. unfold id in *. rewrite preserve_comp3. 
         rewrite assoc. rewrite preserve_comp3. rewrite assoc. rewrite (comm_diagram1'0 a). do 2 rewrite assoc.
         apply rcancel. apply rcancel. specialize(@comm_diag4 b (F a) f).
         (* rewrite comm_diag1. ?? *)  
         rewrite <- assoc. rewrite <- assoc. rewrite comm_diag4.
         cut (fmap4 b (F a) f = fmap3 (F b) (F (F a)) (fmap3 b (F a) f)).
           + intros. rewrite H. reflexivity.
           + apply H.
       - intros. unfold id in *. destruct nt1, nt2, M, T, T2.  simpl in *. unfold id in *.
         specialize (@comm_diag3 b (F a) f). rewrite <- assoc. rewrite comm_diag3. rewrite assoc.
         rewrite comm_diagram2_b2'0. rewrite identity_f. destruct Id. unfold idf. rewrite H0.
         simpl; reflexivity.
       - intros. unfold id in *. destruct nt1, nt2, M, T, T2. simpl in *. unfold id in *. 
          rewrite comm_diagram2'0, comm_diagram2_b2'0, identity_f. reflexivity.
Defined.
Check Kleisli_Category2.

Definition coKleisli_Category' (catC: Category) (F: obj catC -> obj catC)
                               (fmapD : forall (a b: obj catC) (f: arrow catC b a), (arrow catC (F b) (F a)))
                               (D   : (Functor catC catC F fmapD))
                               (CM  : coMonad' catC F fmapD D): Category.
Proof. destruct CM. destruct cnt3, cnt4.
       refine (@mk_Category (obj catC)
                            (fun a b => (@arrow catC (id b) (F a)))
                            (fun a => (@trans0 a)) 
                            (fun a b c f g => g o (fmapD _ _ f) o (@trans1 a))
                            _ _ _ ).
      - intros. simpl. destruct D, D3. simpl in *. unfold id in *. rewrite preserve_comp0.
         rewrite assoc. rewrite preserve_comp0. do 5 rewrite <- assoc. rewrite (cm_comm_diagram1''0 d).
         do 5 rewrite assoc.  apply rcancel. specialize(@comm_diag1 (F d) c h). rewrite <- assoc.
         rewrite <- comm_diag1. do 2 rewrite assoc. reflexivity.
      - intros. unfold id in *. destruct D, D3. simpl in *. unfold id in *. rewrite <- assoc.
         rewrite cm_comm_diagram2''0, cm_comm_diagram_b2''0, f_identity. reflexivity.
      - intros. unfold id in *. destruct D, D3. simpl in *. unfold id in *. rewrite <- comm_diag0.
         rewrite <- assoc. rewrite cm_comm_diagram_b2''0, f_identity. unfold idf; reflexivity.
Defined.
Check coKleisli_Category'.

Definition coKleisli_Category (catC: Category) (F: obj catC -> obj catC)
                              (fmapD : forall (a b: obj catC) (f: arrow catC b a), (arrow catC (F b) (F a)))
                              (Id  : (Functor catC catC id (fun a b f => (@idf catC a b f))))
                              (D   : (Functor catC catC F fmapD))
                              (D2  : (Functor catC catC (fun a: obj catC => F (F a)) (fun a b f => fmapD _ _ (fmapD _ _ f))))
                              (nt1 : NaturalTransformation catC catC F id fmapD (fun a b f => (@idf catC a b f)) D Id)
                              (nt2 : NaturalTransformation catC catC F (fun a: obj catC => F (F a))
                                     fmapD (fun a b f => fmapD _ _ (fmapD _ _ f)) D D2)
                              (CM  : coMonad catC F fmapD Id D D2 nt1 nt2): Category.
Proof. refine (@mk_Category (obj catC)
                            (fun a b => (@arrow catC (id b) (F a)))
                            (fun a => (@trans _ _ _ _ _ _ _ _ nt1 a)) 
                            (fun a b c f g => g o (fmapD _ _ f) o (@trans _ _ _ _ _ _ _ _ nt2 a))
                            _ _ _ ).
      - intros. simpl. destruct nt1, nt2, CM, D, D2. simpl in *. unfold id in *. rewrite preserve_comp0.
         rewrite assoc. rewrite preserve_comp0. do 5 rewrite <- assoc. rewrite (cm_comm_diagram3 d).
         do 5 rewrite assoc.  apply rcancel. specialize(@comm_diag1 (F d) c h). rewrite <- assoc.
         rewrite <- comm_diag1. do 2 rewrite assoc. reflexivity.
      - intros. unfold id in *. destruct nt1, nt2, CM, D, D2. simpl in *. unfold id in *. rewrite <- assoc.
         rewrite cm_comm_diagram4, cm_comm_diagram_b4, f_identity. reflexivity.
      - intros. unfold id in *. destruct nt1, nt2, CM, D, D2. simpl in *. unfold id in *. rewrite <- comm_diag0.
         rewrite <- assoc. rewrite cm_comm_diagram_b4, f_identity. unfold idf; reflexivity.
Defined.
Check coKleisli_Category.


Definition coKleisli_Category2 (catC: Category) (F: obj catC -> obj catC)
                               (Id  : (Functor2 catC catC id))
                               (D   : (Functor2 catC catC F))
                               (D2  : (Functor2 catC catC (fun a: obj catC => F (F a))))
                               (nt1 : NaturalTransformation2 catC catC F id D Id)
                               (nt2 : NaturalTransformation2 catC catC F (fun a: obj catC => F (F a)) D D2)
                               (CM  : coMonad2 catC F Id D D2 nt1 nt2) :
                              (forall a b f, (@fmap2 _ _ _ D2 a b f) = (@fmap2 _ _ _ D _ _ (@fmap2 _ _ _ D _ _ f))) ->
                              (forall a b f, (@fmap2 _ _ _ Id a b f) = (@idf catC a b f)) ->
                              (Category).
Proof. intros. refine (@mk_Category (obj catC)
                            (fun a b       => (@arrow catC (id b) (F a)))
                            (fun a         => (@trans2 _ _ _ _ _ _ nt1 a)) 
                            (fun a b c f g => g o (@fmap2 _ _ _ D _ _ f) o (@trans2 _ _ _ _ _ _  nt2 a))
                            _ _ _ ).
      - intros. simpl. destruct nt1, nt2, CM, D, D2. simpl in *. unfold id in *. rewrite preserve_comp3.
         rewrite assoc. rewrite preserve_comp3. do 5 rewrite <- assoc. rewrite (cm_comm_diagram1'0 d).
         do 5 rewrite assoc.  apply rcancel. specialize(@comm_diag4 (F d) c h). rewrite <- assoc.
         rewrite <- comm_diag4. do 2 rewrite assoc.
         rewrite H. reflexivity.
      - intros. unfold id in *. destruct nt1, nt2, CM, D, D2. simpl in *. unfold id in *. rewrite <- assoc.
         rewrite cm_comm_diagram2'0, cm_comm_diagram_b2'0, f_identity. reflexivity.
      - intros. unfold id in *. destruct nt1, nt2, CM, D, D2. simpl in *. unfold id in *. rewrite <- comm_diag3.
         rewrite <- assoc. rewrite cm_comm_diagram_b2'0, f_identity. rewrite H0; reflexivity.
Defined.
Check coKleisli_Category2.


End Make.
   