Require Import Morphisms.
Import ProperNotations.
Require Import SetoidClass.
Require notation categories prods_pullbacks functors.

Module Make(Import M: notation.T).
 Module Export natural_transformations_exp := functors.Make(M).

Definition id {catC: Category} (a: obj catC) := a.

Theorem rcancel:  forall {catC: Category} {a b c: obj catC} (f g: arrow _ c b) (h: arrow _ b a), f = g -> f o h = g o h.
Proof. intros. rewrite H. reflexivity. Qed.

Class NaturalTransformation (catC catD: Category) (F G: obj catC -> obj catD) 
                            (fmapF : forall (a b: obj catC) (f: arrow catC b a), (arrow catD (F b) (F a)))
                            (fmapG : forall (a b: obj catC) (f: arrow catC b a), (arrow catD (G b) (G a)))
                            `(@Functor catC catD F fmapF) 
                            `(@Functor catC catD G fmapG): Type :=
  mk_nt
  {
    trans    :  forall (a: obj catC), (arrow catD (G a) (F a));
    comm_diag:  forall {a b: obj catC} (f: arrow catC b a), fmapG _ _ f o trans a  = trans b o fmapF _ _ f
  }.
Check NaturalTransformation.
Check trans.

Definition IdentityNaturalTransformation `(catC: Category) `(catD: Category) (F: obj catC -> obj catD) 
                            (fmapF : forall (a b: obj catC) (f: arrow catC b a), (arrow catD (F b) (F a)))
                            `(FunctF: @Functor catC catD F fmapF): 
                              `(@NaturalTransformation catC catD F F fmapF fmapF FunctF FunctF).
Proof. refine (@mk_nt catC catD F F fmapF fmapF FunctF FunctF  (fun a => (@identity catD (F a))) _).
intros. rewrite identity_f. rewrite f_identity. reflexivity. Defined.
Check IdentityNaturalTransformation.

Definition Compose_NaturalTransformations (catC catD catE: Category) 
                                          (F G H   : obj catC -> obj catD)
                                          (fmapF   : forall (a b: obj catC) (f: arrow catC b a), (arrow catD (F b) (F a)))
                                          (fmapG   : forall (a b: obj catC) (f: arrow catC b a), (arrow catD (G b) (G a)))
                                          (fmapH   : forall (a b: obj catC) (f: arrow catC b a), (arrow catD (H b) (H a)))
                                          (FunctF  : @Functor catC catD F fmapF)
                                          (FunctG  : @Functor catC catD G fmapG) 
                                          (FunctH  : @Functor catC catD H fmapH)
                                          (nt1     : @NaturalTransformation catC catD F G fmapF fmapG FunctF FunctG)
                                          (nt2     : @NaturalTransformation catC catD G H fmapG fmapH FunctG FunctH):
                                             `(@NaturalTransformation catC catD F H fmapF fmapH FunctF FunctH).
Proof. refine (@mk_nt _ _ _ _ _ _ FunctF FunctH
                                  (fun a: obj catC =>  (@trans _ _ _ _ _ _ _ _ nt2 a) o (@trans _ _ _ _ _ _ _ _ nt1 a))
                                  _
               ).
       intros. destruct nt1, nt2. simpl.
         rewrite <- assoc. rewrite <- comm_diag0.
         repeat rewrite assoc. apply rcancel. apply comm_diag1.
Qed.
Check Compose_NaturalTransformations.       

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
