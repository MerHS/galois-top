From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
From mathcomp Require Import fintype bigop prime finset fingroup morphism.
From mathcomp Require Import perm automorphism quotient gproduct ssralg.
From mathcomp Require Import finalg zmodp poly cyclic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory.

Section Chap1_5.

Variable gT : finGroupType.
Implicit Types (a x y : gT) (A B : {set gT}) (Cm G K H : {group gT}).

(** Theorem 1.5 Subgroup of Cyclic group is also cyclic *)
Theorem Cyclic_subgroup Cm H m:
  cyclic Cm -> #|Cm| = m -> H \subset Cm -> (#|H| %| m) && (cyclic H).
Proof.
  move=> /cyclicP[x cyc_Cm] ord_cm subset_H.
  apply/andP. split.
  - rewrite -ord_cm.
    rewrite -(Lagrange subset_H).
    by apply dvdn_mulr.
  - apply/cyclicP.
    exists (x ^+ (#[x] %/ #|H|)).
    apply/congr_group/set1P.
    rewrite -cycle_sub_group.
    by rewrite -cyc_Cm inE eqxx subset_H.
    rewrite /order -cyc_Cm.
    rewrite -(Lagrange subset_H).
    by apply dvdn_mulr.
Qed.

(**
Above proof require non-trivial lemmas like Lagrange and cycle_sub_group.
I copied those from math-comp.
 *)

Lemma LagrangeI G H : (#|G :&: H| * #|G : H|)%N = #|G|.
Proof.
rewrite -[#|G|]sum1_card (partition_big_imset (rcoset H)) /=.
rewrite mulnC -sum_nat_const; apply: eq_bigr => _ /rcosetsP[x Gx ->].
rewrite -(card_rcoset _ x) -sum1_card; apply: eq_bigl => y.
by rewrite rcosetE (sameP eqP rcoset_eqP) group_modr (sub1set, inE).
Qed.

Lemma divgI G H : #|G| %/ #|G :&: H| = #|G : H|.
Proof. by rewrite -(LagrangeI G H) mulKn ?cardG_gt0. Qed.

Lemma divg_index G H : #|G| %/ #|G : H| = #|G :&: H|.
Proof. by rewrite -(LagrangeI G H) mulnK. Qed.

Lemma dvdn_indexg G H : #|G : H| %| #|G|.
Proof. by rewrite -(LagrangeI G H) dvdn_mull. Qed.

Theorem Lagrange G H : H \subset G -> (#|H| * #|G : H|)%N = #|G|.
Proof. by move/setIidPr=> sHG; rewrite -{1}sHG LagrangeI. Qed.

Section Zpm.

Variable a : gT.

Definition Zpm (i : 'Z_#[a]) := a ^+ i.

Lemma ZpmM : {in Zp #[a] &, {morph Zpm : x y / x * y}}.
Proof.
rewrite /Zpm; case: (eqVneq a 1) => [-> | nta] i j _ _.
  by rewrite !expg1n ?mulg1.
by rewrite /= {3}Zp_cast ?order_gt1 // expg_mod_order expgD.
Qed.

Canonical Zpm_morphism := Morphism ZpmM.

Lemma im_Zpm : Zpm @* Zp #[a] = <[a]>.
Proof.
apply/eqP; rewrite eq_sym eqEcard cycle_subG /= andbC morphimEdom.
rewrite (leq_trans (leq_imset_card _ _)) ?card_Zp //= /Zp order_gt1.
case: eqP => /= [a1 | _]; first by rewrite imset_set1 morph1 a1 set11.
by apply/imsetP; exists 1%R; rewrite ?expg1 ?inE.
Qed.

Lemma injm_Zpm : 'injm Zpm.
Proof.
apply/injmP/dinjectiveP/card_uniqP.
rewrite size_map -cardE card_Zp //= {7}/order -im_Zpm morphimEdom /=.
by apply: eq_card => x; apply/imageP/imsetP=> [] [i Zp_i ->]; exists i.
Qed.

Lemma eq_expg_mod_order m n : (a ^+ m == a ^+ n) = (m == n %[mod #[a]]).
Proof.
have [->|] := eqVneq a 1; first by rewrite order1 !modn1 !expg1n eqxx.
rewrite -order_gt1 => lt1a; have ZpT: Zp #[a] = setT by rewrite /Zp lt1a.
have: injective Zpm by move=> i j; apply (injmP injm_Zpm); rewrite /= ZpT inE.
move/inj_eq=> eqZ; symmetry; rewrite -(Zp_cast lt1a).
by rewrite -[_ == _](eqZ (inZp m) (inZp n)) /Zpm /= Zp_cast ?expg_mod_order.
Qed.

End Zpm.

Lemma order_dvdn a n : #[a] %| n = (a ^+ n == 1).
Proof. by rewrite (eq_expg_mod_order a n 0) mod0n. Qed.

Lemma orderXgcd a n : #[a ^+ n] = #[a] %/ gcdn #[a] n.
Proof.
apply/eqP; rewrite eqn_dvd; apply/andP; split.
  rewrite order_dvdn -expgM -muln_divCA_gcd //.
  by rewrite expgM expg_order expg1n.
have [-> | n_gt0] := posnP n; first by rewrite gcdn0 divnn order_gt0 dvd1n.
rewrite -(dvdn_pmul2r n_gt0) divn_mulAC ?dvdn_gcdl // dvdn_lcm.
by rewrite order_dvdn mulnC expgM expg_order eqxx dvdn_mulr.
Qed.

(*  Gorenstein, 1.3.1 (i) *)
Lemma cycle_sub_group_copied (a : gT) m :
     m %| #[a] ->
  [set H : {group gT} | H \subset <[a]> & #|H| == m]
     = [set <[a ^+ (#[a] %/ m)]>%G].
Proof.
move=> m_dv_a; have m_gt0: 0 < m by apply: dvdn_gt0 m_dv_a.
have oam: #|<[a ^+ (#[a] %/ m)]>| = m.
  apply/eqP; rewrite [#|_|]orderXgcd -(divnMr m_gt0) muln_gcdl divnK //.
  by rewrite gcdnC gcdnMr mulKn.
apply/eqP; rewrite eqEsubset sub1set inE /= cycleX oam eqxx !andbT.
apply/subsetP=> X; rewrite in_set1 inE -val_eqE /= eqEcard oam.
case/andP=> sXa /eqP oX; rewrite oX leqnn andbT.
apply/subsetP=> x Xx; case/cycleP: (subsetP sXa _ Xx) => k def_x.
have: (x ^+ m == 1)%g by rewrite -oX -order_dvdn cardSg // gen_subG sub1set.
rewrite {x Xx}def_x -expgM -order_dvdn -[#[a]](Lagrange sXa) -oX mulnC.
rewrite dvdn_pmul2r // mulnK // => /dvdnP[i ->].
by rewrite mulnC expgM groupX // cycle_id.
Qed.

End Chap1_5.
