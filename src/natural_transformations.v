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

Program Instance IdentityNaturalTransformation `(catC: Category) `(catD: Category) (F G: obj catC -> obj catD) 
                            (fmapF : forall (a b: obj catC) (f: arrow catC b a), (arrow catD (F b) (F a)))
                            `(FunctF: @Functor catC catD F fmapF):
                            `(@NaturalTransformation catC catD F F fmapF fmapF FunctF FunctF 
                                   (fun a => (@identity catD (F a)))).
Obligation 1. destruct FunctF. rewrite <- preserve_id0. rewrite <- preserve_id0.
       rewrite <- preserve_comp0. rewrite <- preserve_comp0. rewrite identity_f.
       rewrite f_identity; reflexivity.
Qed.
Check IdentityNaturalTransformation.

(*TODO:= composition of natural transformations *)

End Make.
