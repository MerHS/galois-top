From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div.
From mathcomp Require Import ssrnum ssralg ssrint intdiv rat order.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Import GRing.Theory.
Import Order.Theory.
Import Num.Theory.

(** Theorem 1.2 First-order Diophantine Equation *)
Theorem first_diophantine (a b d g: int):
  a <> 0 -> b <> 0 -> gcdz a b = g -> (g %| d)%Z ->
  (exists (x y: int), (a * x) + (b * y) = d).
Proof.
  (* implementing infinite-descending method (book's method) is somewhat hard
     just use Bezout's coefficient.*)
  move=> neq_a0 neq_b0 gcd_ab.
  case: (egcdzP a b) => u v Huv _.
  case/dvdzP => h ->.
  exists (u * h), (v * h). subst.
  rewrite -Huv.
  rewrite mulrDr.
  rewrite mulrC -mulrA mulrC mulrA -mulrA.
  by rewrite [in a * u]mulrC [in b * v]mulrC [in v * b * h]mulrC.
Qed.

Theorem first_diophantine_false (a b d g: int):
  a <> 0 -> b <> 0 -> gcdz a b = g -> (g %| d)%Z = false ->
  ~(exists (x y: int), (a * x) + (b * y) = d).
Proof.
  move=> neq_a0 neq_b0 gcd_ab false_dvd.
  case=> x [y eq_xy].
  have dvd_gd: (g %| d)%Z.
  rewrite -eq_xy rpredD => //=; subst;  apply: dvdz_mulr;
                     by [apply dvdz_gcdl|apply dvdz_gcdr].
  move: dvd_gd.
  apply: (contraFnot _ (g %| d)%Z) => //=.
Qed.
