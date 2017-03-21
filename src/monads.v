Require Import Morphisms.
Import ProperNotations.
Require Import SetoidClass.
Require notation categories prods_pullbacks functors natural_transformations.

Module Make(Import M: notation.T).
 Module Export monads_exp := natural_transformations.Make(M).


Class Monad (catC: Category) (F: obj catC -> obj catC)
            (fmapT  : forall (a b: obj catC) (f: arrow catC b a), (arrow catC (F b) (F a)))
                        (Id  : (Functor catC catC id (fun a b f => (@idf catC a b f))))
                        (T   : (Functor catC catC F fmapT))
                        (T2  : (Functor catC catC (fun a: obj catC => F (F a)) (fun a b f => fmapT _ _ (fmapT _ _ f))))
                        (nt1 :@NaturalTransformation catC catC id F (fun a b f => (@idf catC a b f)) fmapT Id T)
                        (nt2 :@NaturalTransformation catC catC (fun a: obj catC => F (F a)) F (fun a b f => fmapT _ _ (fmapT _ _ f)) fmapT T2 T): Type :=
  mk_Monad  
  {
    comm_diagram1   : forall (a: obj catC), (@trans _ _ _ _ _ _ _ _ nt2 a) o (fmapT _ _  ((@trans _ _ _ _ _ _ _ _ nt2 a))) 
                                            = 
                                            (@trans _ _ _ _ _ _ _ _ nt2 a) o (@trans _ _ _ _ _ _ _ _ nt2 (F a));
    comm_diagram2   : forall (a: obj catC), (@trans _ _ _ _ _ _ _ _ nt2 a) o (fmapT _ _ (@trans _ _ _ _ _ _ _ _ nt1 a)) 
                                            = 
                                            (@trans _ _ _ _ _ _ _ _ nt2 a) o (@trans _ _ _ _ _ _ _ _ nt1 (F a));
    comm_diagram2_b1: forall (a: obj catC), (@trans _ _ _ _ _ _ _ _ nt2 a) o (fmapT _ _ (@trans _ _ _ _ _ _ _ _ nt1 a))
                                            = (identity catC (F a));
    comm_diagram2_b2: forall (a: obj catC), (@trans _ _ _ _ _ _ _ _ nt2 a) o (@trans _ _ _ _ _ _ _ _ nt1 (F a)) 
                                            = (identity catC (F a))
  }.
Check Monad.

Class Monad' (catC  : Category) 
             (F     : obj catC -> obj catC)
             (fmapT : forall (a b: obj catC) (f: arrow catC b a), (arrow catC (F b) (F a)))
             (T     : (Functor catC catC F fmapT)): Type :=
  mk_Monad'
  {
    Id  : (Functor catC catC id (fun a b f => (@idf catC a b f)));
    T2  : (Functor catC catC (fun a: obj catC => F (F a)) (fun a b f => fmapT _ _ (fmapT _ _ f)));
    nt1 :@NaturalTransformation catC catC id F (fun a b f => (@idf catC a b f)) fmapT Id T;
    nt2 :@NaturalTransformation catC catC (fun a: obj catC => F (F a)) F (fun a b f => fmapT _ _ (fmapT _ _ f)) fmapT T2 T;
    comm_diagram1''   : forall (a: obj catC), (@trans _ _ _ _ _ _ _ _ nt2 a) o (fmapT _ _  ((@trans _ _ _ _ _ _ _ _ nt2 a))) 
                                            = 
                                            (@trans _ _ _ _ _ _ _ _ nt2 a) o (@trans _ _ _ _ _ _ _ _ nt2 (F a));
    comm_diagram2''   : forall (a: obj catC), (@trans _ _ _ _ _ _ _ _ nt2 a) o (fmapT _ _ (@trans _ _ _ _ _ _ _ _ nt1 a)) 
                                            = 
                                            (@trans _ _ _ _ _ _ _ _ nt2 a) o (@trans _ _ _ _ _ _ _ _ nt1 (F a));
    comm_diagram2_b1'' : forall (a: obj catC), (@trans _ _ _ _ _ _ _ _ nt2 a) o (fmapT _ _ (@trans _ _ _ _ _ _ _ _ nt1 a))
                                            = (identity catC (F a));
    comm_diagram2_b2'' : forall (a: obj catC), (@trans _ _ _ _ _ _ _ _ nt2 a) o (@trans _ _ _ _ _ _ _ _ nt1 (F a)) 
                                            = (identity catC (F a))
  }.
Check Monad'.


Class coMonad (catC: Category) (F: obj catC -> obj catC)
              (fmapD  : forall (a b: obj catC) (f: arrow catC b a), (arrow catC (F b) (F a)))
                        (Id      : (Functor catC catC id (fun a b f => (@idf catC a b f))))
                        (D       : (Functor catC catC F fmapD))
                        (D2      : (Functor catC catC (fun a: obj catC => F (F a)) (fun a b f => fmapD _ _ (fmapD _ _ f))))
                        (nt1     : @NaturalTransformation catC catC F id fmapD (fun a b f => (@idf catC a b f)) D Id)
                        (nt2     : @NaturalTransformation catC catC F (fun a: obj catC => F (F a)) fmapD (fun a b f => fmapD _ _ (fmapD _ _ f)) D D2): Type :=
  {
    cm_comm_diagram1    : forall (a: obj catC), (fmapD _ _ (@trans _ _ _ _ _ _ _ _ nt2 a)) o (@trans _ _ _ _ _ _ _ _ nt2 a) 
                                                = 
                                                (@trans _ _ _ _ _ _ _ _ nt2 (F a)) o (@trans _ _ _ _ _ _ _ _ nt2 a);
    cm_comm_diagram2    : forall (a: obj catC), (fmapD _ _ (@trans _ _ _ _ _ _ _ _ nt1 a)) o (@trans _ _ _ _ _ _ _ _ nt2 a) 
                                                = 
                                                (@trans _ _ _ _ _ _ _ _ nt1 (F a)) o (@trans _ _ _ _ _ _ _ _ nt2 a);
    cm_comm_diagram_b1  : forall (a: obj catC), (fmapD _ _ (@trans _ _ _ _ _ _ _ _ nt1 a)) o (@trans _ _ _ _ _ _ _ _ nt2 a)
                                                = (identity catC (F a));
    cm_comm_diagram_b2  : forall (a: obj catC), (@trans _ _ _ _ _ _ _ _ nt1 (F a)) o (@trans _ _ _ _ _ _ _ _ nt2 a)
                                                = (identity catC (F a))
  }.
Check coMonad.


Class coMonad' (catC  : Category) 
               (F     : obj catC -> obj catC)
               (fmapD : forall (a b: obj catC) (f: arrow catC b a), (arrow catC (F b) (F a)))
               (D     : (Functor catC catC F fmapD)): Type :=
  mk_CoMonad'
  {

    cId       : (Functor catC catC id (fun a b f => (@idf catC a b f)));
    D2        : (Functor catC catC (fun a: obj catC => F (F a)) (fun a b f => fmapD _ _ (fmapD _ _ f)));
    cnt1      : @NaturalTransformation catC catC F id fmapD (fun a b f => (@idf catC a b f)) D cId;
    cnt2      : @NaturalTransformation catC catC F (fun a: obj catC => F (F a)) fmapD (fun a b f => fmapD _ _ (fmapD _ _ f)) D D2;
    cm_comm_diagram1''    : forall (a: obj catC), (fmapD _ _ (@trans _ _ _ _ _ _ _ _ cnt2 a)) o (@trans _ _ _ _ _ _ _ _ cnt2 a) 
                                                = 
                                                (@trans _ _ _ _ _ _ _ _ cnt2 (F a)) o (@trans _ _ _ _ _ _ _ _ cnt2 a);
    cm_comm_diagram2''    : forall (a: obj catC), (fmapD _ _ (@trans _ _ _ _ _ _ _ _ cnt1 a)) o (@trans _ _ _ _ _ _ _ _ cnt2 a) 
                                                = 
                                                (@trans _ _ _ _ _ _ _ _ cnt1 (F a)) o (@trans _ _ _ _ _ _ _ _ cnt2 a);
    cm_comm_diagram_b1''  : forall (a: obj catC), (fmapD _ _ (@trans _ _ _ _ _ _ _ _ cnt1 a)) o (@trans _ _ _ _ _ _ _ _ cnt2 a)
                                                = (identity catC (F a));
    cm_comm_diagram_b2''  : forall (a: obj catC), (@trans _ _ _ _ _ _ _ _ cnt1 (F a)) o (@trans _ _ _ _ _ _ _ _ cnt2 a)
                                                = (identity catC (F a))
  }.
Check coMonad'.

(* monads with NaturalTransformation2 *)

Class Monad2 (catC: Category) (F: obj catC -> obj catC)
             (Id  : (Functor2 catC catC id))
             (T   : (Functor2 catC catC F))
             (T2  : (Functor2 catC catC (fun a: obj catC => F (F a))))
             (nt1 : @NaturalTransformation2 catC catC id F Id T)
             (nt2 : @NaturalTransformation2 catC catC (fun a: obj catC => F (F a)) F T2 T): Type :=
  mk_Monad2
  {
    comm_diagram1'   : forall (a: obj catC), (@trans2 _ _ _ _ _ _ nt2 a) o (@fmap2 _ _ _ T _ _ (@trans2 _ _ _ _ _ _  nt2 a))
                                             = 
                                             (@trans2 _ _ _ _ _ _ nt2 a) o (@trans2 _ _ _ _ _ _  nt2 (F a));
    comm_diagram2'   : forall (a: obj catC), (@trans2 _ _ _ _ _ _ nt2 a) o (@fmap2 _ _ _ T _ _ (@trans2 _ _ _ _ _ _  nt1 a)) 
                                             = 
                                             (@trans2 _ _ _ _ _ _ nt2 a) o (@trans2 _ _ _ _ _ _ nt1 (F a));
    comm_diagram2_b1': forall (a: obj catC), (@trans2 _ _ _ _ _ _ nt2 a) o (@fmap2 _ _ _ T _ _ (@trans2 _ _ _ _ _ _  nt1 a))
                                             =  (identity catC (F a));
    comm_diagram2_b2': forall (a: obj catC), (@trans2 _ _ _ _ _ _  nt2 a) o (@trans2 _ _ _ _ _ _  nt1 (F a)) 
                                             = (identity catC (F a))
  }.
Check Monad2.

Class coMonad2 (catC: Category) (F: obj catC -> obj catC)
               (Id  : (Functor2 catC catC id))
               (D   : (Functor2 catC catC F))
               (D2  : (Functor2 catC catC (fun a: obj catC => F (F a))))
               (nt1 : @NaturalTransformation2 catC catC F id D Id)
               (nt2 : @NaturalTransformation2 catC catC F (fun a: obj catC => F (F a)) D D2): Type :=
  {
    cm_comm_diagram1'    : forall (a: obj catC), (@fmap2 _ _ _ D _ _ (@trans2 _ _ _ _ _ _ nt2 a)) o (@trans2 _ _ _ _ _ _ nt2 a) 
                                                = 
                                                (@trans2 _ _ _ _ _ _  nt2 (F a)) o (@trans2 _ _ _ _ _ _ nt2 a);
    cm_comm_diagram2'    : forall (a: obj catC), (@fmap2 _ _ _ D _ _ (@trans2 _ _ _ _ _ _ nt1 a)) o (@trans2 _ _ _ _ _ _ nt2 a) 
                                                = 
                                                (@trans2 _ _ _ _ _ _ nt1 (F a)) o (@trans2 _ _ _ _ _ _ nt2 a);
    cm_comm_diagram_b1'  : forall (a: obj catC), (@fmap2 _ _ _ D _ _ (@trans2 _ _ _ _ _ _ nt1 a)) o (@trans2 _ _ _ _ _ _ nt2 a)
                                                = (identity catC (F a));
    cm_comm_diagram_b2'  : forall (a: obj catC), (@trans2 _ _ _ _ _ _ nt1 (F a)) o (@trans2 _ _ _ _ _ _ nt2 a)
                                                = (identity catC (F a))
  }.
Check coMonad2.


End Make.
