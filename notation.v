Require Import Coq.Unicode.Utf8.
Export Coq.Unicode.Utf8.

Module Type T.

(** some pretty notation; thanks to Harley Eades III **)
Notation "∀ x y z u q , P" := (forall x y z u q , P)
  (at level 200, q ident, x ident, y ident, z ident, u ident, right associativity)
  : type_scope.
Notation "∀ x y z u q v , P" := (forall x y z u q v , P)
  (at level 200, q ident, x ident, y ident, z ident, u ident, v ident, right associativity)
  : type_scope.
Notation "∀ x y z u q v a , P" := (forall x y z u q v a , P)
  (at level 200, q ident, x ident, y ident, z ident, u ident, v ident, a ident, right associativity)
  : type_scope.
Notation "∀ x y z u q v a b , P" := (forall x y z u q v a b , P)
  (at level 200, q ident, x ident, y ident, z ident, u ident, v ident, a ident, b ident, right associativity)
  : type_scope.
Notation "∀ x y z u q v a b r , P" := (forall x y z u q v a b r , P)
  (at level 200, q ident, x ident, y ident, z ident, u ident, v ident, a ident, b ident, r ident, right associativity)
  : type_scope.
Notation "∀ x y z u q v a b r s , P" := (forall x y z u q v a b r s , P)
  (at level 200, q ident, x ident, y ident, z ident, u ident, v ident, a ident, b ident, r ident, s ident, right associativity)
  : type_scope.
Notation "∀ x y z u q v a b r s t , P" := (forall x y z u q v a b r s t , P)
  (at level 200, q ident, x ident, y ident, z ident, u ident, v ident, a ident, b ident, r ident, s ident, t ident,
    right associativity)
  : type_scope.

End T.
