From mathcomp Require Import ssreflect ssrbool eqtype ssrnat div.


Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** Propositional common divisor and gcd

Technically, each lemma in the proofs implicitly use 'edivn' which impliments
Euclidean division. Hence, these are not constructed from scratch.
 *)
Definition is_cdiv a b m := m %| a /\ m %| b /\ m > 0.

Definition is_gcd a b g := is_cdiv a b g /\ (forall i, i %| a -> i %| b -> i <= g).

Lemma cdivn1 a b: is_cdiv a b 1. Proof. by []. Qed.

Lemma mod_cdiv a b m: m %| a -> m %| b -> m %| (a %% b).
Proof.
  case/dvdnP => q ->; case/dvdnP => r ->.
  by rewrite -muln_modl dvdn_mull.
Qed.

(** Theorem 1.1 Eucledean Algorithm *)
Theorem Euclidean_Algorithm a b g: let r := a %% b in is_gcd a b g -> is_gcd b r g.
Proof.
  rewrite /is_gcd /is_cdiv.
  move=> [[div_ag [div_bg ltg]] IHg].
  repeat split; try by [].
  - by apply mod_cdiv.
  - move=> i Hib Hiab. apply IHg; repeat split; try by [].
    rewrite (divn_eq a b) dvdn_add //= dvdn_mull //=.
Qed.

Lemma is_gcdP a b g: g > 0 -> reflect (is_gcd a b g) (gcdn a b == g).
Proof.
  rewrite /is_gcd /is_cdiv => gt_g0.
  apply: (iffP eqP).
  - move=> ?; subst; repeat split; try by [apply dvdn_gcdl|apply dvdn_gcdr|eauto].
    move=> i Hia Hib.
    apply: dvdn_leq => //.
    rewrite dvdn_gcd; by apply/andP.
  - move=> [[div_ga [div_gb _]] IHg].
    have div_gcdg: (g %| gcdn a b).
    rewrite dvdn_gcd. by apply/andP.
    apply/eqP. rewrite eqn_leq; apply/andP.
    split.
    + apply IHg; repeat split; try by [apply dvdn_gcdl|apply dvdn_gcdr].
    + move: div_gcdg. apply dvdn_leq.
      rewrite gcdn_gt0 !ltnNge -negb_and !leqn0.
      apply/andP. case. do 2 case/eqnP=> ?; subst.
      have FF: (g.+1 <= g).
      apply: IHg; by apply dvdn0.
      move: FF. by rewrite ltnn.
Qed.
