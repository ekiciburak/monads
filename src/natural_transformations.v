Require Import Morphisms.
Import ProperNotations.
Require Import SetoidClass.
Require notation categories prods_pullbacks functors.

Module Make(Import M: notation.T).
 Module Export natural_transformations_exp := functors.Make(M).

Definition id {catC: Category} (a: obj catC) := a.

Class NaturalTransformation (catC catD: Category) (F G: obj catC -> obj catD) 
                            (fmapF : forall (a b: obj catC) (f: arrow catC b a), (arrow catD (F b) (F a)))
                            (fmapG : forall (a b: obj catC) (f: arrow catC b a), (arrow catD (G b) (G a)))
                            `(@Functor catC catD F fmapF) 
                            `(@Functor catC catD G fmapG)
                            (trans : forall (a: obj catC), (arrow catD (G a) (F a))): Type :=
  mk_nt
  {  
    comm_diag: forall {a b: obj catC} (f: arrow catC b a), fmapG _ _ f o trans a = trans b o fmapF _ _ f
  }.
Check NaturalTransformation.

Class NaturalTransformation2 (catC catD: Category) (F G: obj catC -> obj catD) 
                            (fmapF : forall (a b: obj catC) (f: arrow catC b a), (arrow catD (F b) (F a)))
                            (fmapG : forall (a b: obj catC) (f: arrow catC b a), (arrow catD (G b) (G a)))
                            `(@Functor catC catD F fmapF) 
                            `(@Functor catC catD G fmapG): Type :=
  mk_nt2
  {
    trans2    :  forall (a: obj catC), (arrow catD (G a) (F a));
    comm_diag2:  forall {a b: obj catC} (f: arrow catC b a), fmapG _ _ f o trans2 a  = trans2 b o fmapF _ _ f
  }.
Check NaturalTransformation2.
Check trans2.

Definition IdentityNaturalTransformation `(catC: Category) `(catD: Category) (F: obj catC -> obj catD) 
                            (fmapF : forall (a b: obj catC) (f: arrow catC b a), (arrow catD (F b) (F a)))
                            `(FunctF: @Functor catC catD F fmapF): 
                              `(@NaturalTransformation catC catD F F fmapF fmapF FunctF FunctF 
                                   (fun a => (@identity catD (F a)))).
Proof. refine (@mk_nt catC catD F F fmapF fmapF FunctF FunctF  (fun a => (@identity catD (F a))) _ ).
intros. rewrite identity_f. rewrite f_identity. reflexivity. Defined.
Check IdentityNaturalTransformation.

Definition IdentityNaturalTransformation2 `(catC: Category) `(catD: Category) (F: obj catC -> obj catD) 
                            (fmapF : forall (a b: obj catC) (f: arrow catC b a), (arrow catD (F b) (F a)))
                            `(FunctF: @Functor catC catD F fmapF): 
                              `(@NaturalTransformation2 catC catD F F fmapF fmapF FunctF FunctF).
Proof. refine (@mk_nt2 catC catD F F fmapF fmapF FunctF FunctF  (fun a => (@identity catD (F a))) _).
intros. rewrite identity_f. rewrite f_identity. reflexivity. Defined.
Check IdentityNaturalTransformation2.

Theorem rcancel:  forall {catC: Category} {a b c: obj catC} (f g: arrow _ c b) (h: arrow _ b a), f = g -> f o h = g o h.
Proof. intros. rewrite H. reflexivity. Qed.


Definition Compose_NaturalTransformations2 (catC catD catE: Category) 
                                          (F G H   : obj catC -> obj catD)
                                          (fmapF   : forall (a b: obj catC) (f: arrow catC b a), (arrow catD (F b) (F a)))
                                          (fmapG   : forall (a b: obj catC) (f: arrow catC b a), (arrow catD (G b) (G a)))
                                          (fmapH   : forall (a b: obj catC) (f: arrow catC b a), (arrow catD (H b) (H a)))
                                          (FunctF  : @Functor catC catD F fmapF)
                                          (FunctG  : @Functor catC catD G fmapG) 
                                          (FunctH  : @Functor catC catD H fmapH)
                                          (nt1     : @NaturalTransformation2 catC catD F G fmapF fmapG FunctF FunctG)
                                          (nt2     : @NaturalTransformation2 catC catD G H fmapG fmapH FunctG FunctH):
                                             `(@NaturalTransformation2 catC catD F H fmapF fmapH FunctF FunctH).
Proof. refine (@mk_nt2 _ _ _ _ _ _ FunctF FunctH
                                   (fun a: obj catC =>  (@trans2 _ _ _ _ _ _ _ _ nt2 a) o (@trans2 _ _ _ _ _ _ _ _ nt1 a)) _).
       intros. destruct nt1, nt2. simpl.
         rewrite <- assoc. rewrite <- comm_diag3.
         repeat rewrite assoc. apply rcancel. apply comm_diag4.
Qed. 
       

(*
Program Instance IdentityNaturalTransformation `(catC: Category) `(catD: Category) (F: obj catC -> obj catD) 
                            (fmapF : forall (a b: obj catC) (f: arrow catC b a), (arrow catD (F b) (F a)))
                            `(FunctF: @Functor catC catD F fmapF):
                            `(@NaturalTransformation catC catD F F fmapF fmapF FunctF FunctF 
                                   (fun a => (@identity catD (F a)))).
Obligation 1. destruct FunctF. rewrite <- preserve_id0. rewrite <- preserve_id0.
       rewrite <- preserve_comp0. rewrite <- preserve_comp0. rewrite identity_f.
       rewrite f_identity; reflexivity.
Qed.
Check IdentityNaturalTransformation.
*)

(*TODO:= composition of natural transformations *)

End Make.
