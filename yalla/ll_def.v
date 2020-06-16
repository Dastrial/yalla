(* ll library for yalla *)


(** * Linear Logic with explicit permutations *)
(* not cuts here, see ll_cut.v for cut admissibility and ll_prop.v for other properties *)

Require Import PeanoNat CMorphisms Lia.
Require Import Bool_more List_more List_Type_more Dependent_Forall_Type
               Permutation_Type_more CyclicPerm_Type Permutation_Type_solve
               CPermutation_Type_solve genperm_Type CyclicPerm.
Require Import dectype.
Require Export basic_misc formulas.

Require issue12394.




(** ** Fragments for proofs *)
Axiom eq_dt_dec : forall (E : DecType) (x y : @formula E), {x = y} + {x <> y}.


Section Param.
Variable Sset: DecType.
Notation formula := (@formula Sset).
Definition NoAxioms := (existT (fun x => x -> list formula) _ Empty_fun).
Notation Dependent_Forall_Type_forall_formula :=
  (Dependent_Forall_Type_forall (List.list_eq_dec (eq_dt_dec Sset))).


Definition pmix_none (n : nat) := false.
Definition pmix_all (n : nat) := true.
Definition pmix0 n :=
  match n with
  | 0 => true
  | _ => false
  end.
Definition pmix2 n :=
  match n with
  | 2 => true
  | _ => false
  end.
Definition pmix02 n :=
  match n with
  | 0 => true
  | 2 => true
  | _ => false
  end.

Definition pmix_ge_k k n := if (k <=? n) then true else false.

Definition pmix_le_k k n := if (n <=? k) then true else false.


(** Parameters for [ll] provability:
 - [pcut], [pmix0] and [pmix2] determine whether the corresponding rule is in the system or not;
 - [pperm] is [false] for exchange rule modulo cyclic permutations and [true] for exchange rule modulo arbitrary permutations;
 - [pgax] determines the sequents which are valid as axioms in proofs.
*)

Variant Rset :=
| co_rule : nat -> Rset (*co i sera la contraction d'arité i+2 *)
| mpx_rule : nat -> Rset
| dg_rule : Rset.

Record pfrag := mk_pfrag {
  pcut : bool ;
  pgax : { ptypgax : Type & ptypgax -> list formula } ;
  pmix : nat -> bool ;
  pperm : bool ;
  sig : Sset -> Rset -> bool ;
  leqg : Sset -> Sset -> bool ;
  leqf : Sset -> Sset -> bool ;
  lequ : Sset -> Sset -> bool}.

(** Order relation on proof fragments: [P] is more restrictive than [Q]. *)
Definition le_pfrag P Q :=
  (prod
    (Bool.leb (pcut P) (pcut Q))
  (prod
    (forall a, { b | projT2 (pgax P) a = projT2 (pgax Q) b })
  (prod
    (forall n, Bool.leb (pmix P n) (pmix Q n))
    (prod
    (Bool.leb (pperm P) (pperm Q))
    (prod
    (forall e r, Bool.leb (sig P e r) (sig Q e r))
    (prod (forall e e', Bool.leb (leqg P e e') (leqg Q e e'))
    (prod (forall e e', Bool.leb (leqf P e e') (leqf Q e e'))
    (forall e e', Bool.leb (lequ P e e') (lequ Q e e')) ))))))).

Lemma le_pfrag_trans : forall P Q R,
  le_pfrag P Q -> le_pfrag Q R -> le_pfrag P R.
Proof with myeeasy; try assumption.
  intros P Q R Hyp1 Hyp2.
  unfold le_pfrag in Hyp1.
  destruct Hyp1 as (Hc1 & Ha1 & Hm1 & Hp1 & Hs1 & Hlg1 & Hlf1 & Hlu1).
  unfold le_pfrag in Hyp2.
  destruct Hyp2 as (Hc2 & Ha2 & Hm2 & Hp2 & Hs2 & Hlg2 & Hlf2 & Hlu2).
  nsplit 8 ; try (eapply leb_trans ; myeeasy).
  - intros a.
    destruct (Ha1 a) as [b Heq].
    destruct (Ha2 b) as [c Heq2].
    exists c ; etransitivity...
  - intros n.
    apply leb_trans with (pmix Q n); [ apply Hm1 | apply Hm2 ].
  - intros e r.
    apply leb_trans with (sig Q e r); [ apply Hs1 | apply Hs2 ].
  - intros e e'.
    apply leb_trans with (leqg Q e e'); [ apply Hlg1 | apply Hlg2 ].
  - intros e e'.
    apply leb_trans with (leqf Q e e'); [ apply Hlf1 | apply Hlf2 ].
  - intros e e'.
    apply leb_trans with (lequ Q e e'); [ apply Hlu1 | apply Hlu2 ].
Qed.

Instance le_pfrag_po : PreOrder le_pfrag.
Proof.
split.
- nsplit 8 ; try reflexivity.
  simpl ; intros a.
  exists a ; reflexivity.
- intros P Q R.
  apply le_pfrag_trans.
Qed.

(* Unused
Definition eq_pfrag P Q :=
  prod (pcut P = pcut Q)
       (prod (prod (forall a, { b | projT2 (pgax P) a = projT2 (pgax Q) b})
                   (forall b, {a | projT2 (pgax P) a = projT2 (pgax Q) b}))
       (prod (forall n, pmix P n = pmix Q n)
             (pperm P = pperm Q))).

Lemma eq_pfrag_trans : forall P Q R,
    eq_pfrag P Q -> eq_pfrag Q R -> eq_pfrag P R.
Proof with myeeasy; try assumption.
  intros P Q R H1 H2.
  destruct H1 as (Hc1 & (Ha1 & Hb1) & Hm1 & Hp1).
  destruct H2 as (Hc2 & (Ha2 & Hb2) & Hm2 & Hp2).
  nsplit 4; try (etransitivity; eassumption).
  - split.
    + intros a.
      destruct (Ha1 a) as [a' Heq].
      destruct (Ha2 a') as [a'' Heq2].
      exists a'' ; etransitivity...
    + intros b.
      destruct (Hb2 b) as [b' Heq].
      destruct (Hb1 b') as [b'' Heq2].
      exists b'' ; etransitivity...
  - intros n.
    specialize (Hm1 n).
    specialize (Hm2 n).
    etransitivity; eassumption.
Qed.

Lemma eq_pfrag_sym : forall P Q,
    eq_pfrag P Q -> eq_pfrag Q P.
Proof with myeeasy; try eassumption.
  intros P Q H.
  destruct H as (Hc & (Ha & Hb) & Hm & Hp).
  nsplit 4; try (symmetry ; assumption ; fail)...
  - split.
    + intro a.
      destruct (Hb a) as (b & Heq).
      split with b.
      symmetry...
    + intro b.
      destruct (Ha b) as (a & Heq).
      split with a.
      symmetry...
  - intros n; symmetry; apply Hm...
Qed.

Lemma eq_pfrag_refl : forall P,
    eq_pfrag P P.
Proof with try reflexivity.
  intros P.
  nsplit 4...
  split; intro a; split with a...
Qed.
*)

(** Same proof fragment as [P] but with value [b] for [pcut]. *)
Definition cutupd_pfrag P b := mk_pfrag b (pgax P) (pmix P) (pperm P) (sig P) (leqg P) (leqf P) (lequ P).

Lemma cutupd_pfrag_true : forall P, le_pfrag P (cutupd_pfrag P true).
Proof.
intros P.
nsplit 8 ; try reflexivity.
- apply leb_true.
- intros a ; exists a ; reflexivity.
Qed.

(** Same proof fragment as [P] but with value [G] for [pgax]. *)
Definition axupd_pfrag P G := mk_pfrag (pcut P) G (pmix P) (pperm P) (sig P) (leqg P) (leqf P) (lequ P).

(** Same proof fragment as [P] but without the [cut] rule. *)
Definition cutrm_pfrag P := cutupd_pfrag P false.

Lemma cutrm_cutrm : forall P,
  cutrm_pfrag (cutrm_pfrag P) = cutrm_pfrag P.
Proof.
intros P.
unfold cutrm_pfrag ; unfold cutupd_pfrag.
reflexivity.
Qed.


(** Same proof fragment as [P] but with a different pmix *)
Definition pmixupd_pfrag P pmix := mk_pfrag (pcut P) (pgax P) pmix (pperm P) (sig P) (leqg P) (leqf P) (lequ P).

Definition pmixupd_point_pfrag P n b :=
  pmixupd_pfrag P (fun k => if (k =? n) then b else (pmix P k)).

Lemma pmixupd_point_comm P : forall n1 n2 b1 b2,
    n1 <> n2 ->
    forall k, pmix (pmixupd_point_pfrag (pmixupd_point_pfrag P n1 b1) n2 b2) k
            = pmix (pmixupd_point_pfrag (pmixupd_point_pfrag P n2 b2) n1 b1) k.
Proof with try reflexivity.
  intros n1 n2 b1 b2 Hneq k.
  case_eq (k =? n1) ; intros Heq1; case_eq (k =? n2); intros Heq2; simpl; rewrite Heq1; rewrite Heq2...
  exfalso.
  apply Hneq.
  transitivity k.
  - symmetry; apply EqNat.beq_nat_true; apply Heq1.
  - apply EqNat.beq_nat_true; apply Heq2.
Qed.

(** ** Rules *)

(** The main predicate: [ll] proofs.

The [nat] parameter is a size of proofs.
Choices between [plus] and [max] in binary cases are determined by the behaviour in cut admissibility.

All rules have their main formula at first position in the conclusion.
 - [ax_r]: identity rule restricted to propositional variables (general case proved later)
 - [ex_r]: exchange rule (parametrized by [pperm P] to determine allowed permutations)
 - [ex_wn_r]: exchange rule between [wn] formulas
 - [mix_r]: n-ary linear mix rule
 - [one_r]: one rule
 - [bot_r]: bot rule
 - [tens_r]: tensor rule (the order of lists is imposed by the cyclic permutation case)
 - [parr_r]: par rule
 - [top_r]: par rule
 - [plus_r1]: plus left rule
 - [plus_r2]: plus right rule
 - [with_r]: with rule
 - [oc_r]: promotion rule (standard shape)
 - [de_r]: dereliction rule
 - [wk_r]: weakening rule
 - [co_r]: contraction rule with [wn] context inserted between principal formulas to be general enough in the cyclic permutation case
 - [cut_r]: cut rule (the order of lists is matched with the [tens_r] case) (available only if [pcut P = true])
 - [gax_r]: generic axiom rule (parametrized by the predicate [pgax P] over sequents)
*)

Fixpoint mapwn expList formList :=
  match expList with
  |nil => @nil formula
  |h1 :: t1 => match formList with
    |nil => @nil formula
    |h2 :: t2 => wn h1 h2 :: mapwn t1 t2
    end
  end.

Fixpoint mapoc expList formList :=
  match expList with
  |nil => @nil formula
  |h1 :: t1 => match formList with
    |nil => @nil formula
    |h2 :: t2 => oc h1 h2 :: mapwn t1 t2
    end
  end.


Inductive ll P : list formula -> Type :=
| ax_r : forall X, ll P (covar X :: var X :: nil)
| ex_r : forall l1 l2, ll P l1 -> PCperm_Type (pperm P) l1 l2 -> ll P l2
| ex_wn_r : forall l1 lw lw' l2 e, ll P (l1 ++ map (wn e) lw ++ l2) ->
               Permutation_Type lw lw' -> ll P (l1 ++ map (wn e) lw' ++ l2)
| mix_r : forall L, is_true (pmix P (length L)) ->
               Forall_Type (ll P) L -> ll P (concat L)
| one_r : ll P (one :: nil)
| bot_r : forall l, ll P l -> ll P (bot :: l)
| tens_r : forall A B l1 l2, ll P (A :: l1) -> ll P (B :: l2) ->
                                   ll P (tens A B :: l2 ++ l1)
| parr_r : forall A B l, ll P (A :: B :: l) -> ll P (parr A B :: l)
| top_r : forall l, ll P (top :: l)
| plus_r1 : forall A B l, ll P (A :: l) -> ll P (aplus A B :: l)
| plus_r2 : forall A B l, ll P (A :: l) -> ll P (aplus B A :: l)
| with_r : forall A B l, ll P (A :: l) -> ll P (B :: l) ->
                               ll P (awith A B :: l)
| ocg_r : forall e A l, ll P (A :: map (fun p => wn (fst p) (snd p)) l) ->
          Forall (fun e' => is_true (leqg P e e')) (map (fun p => (fst p)) l) ->
          ll P (oc e A :: map (fun p => wn (fst p) (snd p)) l)
| ocf_r : forall e A l, ll P (A :: map (fun p => (snd p)) l) ->
          Forall (fun e' => is_true (leqf P e e')) (map (fun p => (fst p)) l) ->
          ll P (oc e A :: map (fun p => wn (fst p) (snd p)) l)
| ocu_r : forall e e' A B, ll P (A :: B :: nil) ->
          is_true (lequ P e e') -> ll P (oc e A :: wn e' B :: nil)
| mpx_r : forall i e A l, ll P ((repeat A i) ++ l) -> is_true (sig P e (mpx_rule i)) ->
            ll P ((wn e A) :: nil ++ l)
| co_r : forall i e A l, ll P ((repeat (wn e A) (i+2)) ++ l) -> is_true (sig P e (co_rule i)) ->
            ll P ((wn e A) :: nil ++ l)
| dg_r : forall e A l, ll P ((wn e (wn e A)) :: nil ++ l) -> is_true (sig P e dg_rule) ->
            ll P (wn e A :: nil ++ l)
| cut_r {f : pcut P = true} : forall A l1 l2,
    ll P (dual A :: l1) -> ll P (A :: l2) -> ll P (l2 ++ l1)
| gax_r : forall a, ll P (projT2 (pgax P) a).

Definition mix'_r P L : is_true (pmix P (length L)) ->
   ll P (flat_map (@projT1 _ (ll P)) L).
Proof.
intros Hmix.
rewrite flat_map_concat_map.
apply mix_r.
- rewrite map_length ; assumption.
- apply list_to_Forall.
Defined.

Section ll_ind.

  Context { P : pfrag }.

  Definition Forall_Proofs (Pred : forall l, ll P l -> Type) {L} (piL : Forall_Type (ll P) L) := Dependent_Forall_Type Pred piL.

  Lemma Forall_Proofs_to_Forall_Type : forall (Pred : forall l, ll P l -> Type) L (piL : Forall_Type (ll P) L),
      Forall_Proofs Pred piL -> 
      Forall_Type (fun x => Pred (projT1 x) (projT2 x)) (Forall_to_list piL).
  Proof with try assumption.
    intros Pred L piL PpiL.
    induction PpiL; now constructor.
  Qed.



  Fixpoint ll_nested_ind {l} (pi : ll P l): forall (Pred : forall l, ll P l -> Type),
           (forall X, Pred (covar X :: var X :: nil) (ax_r P X)) ->
           (forall l1 l2 pi p, Pred l1 pi -> Pred l2 (ex_r P l1 l2 pi p)) ->
           (forall l1 lw lw' l2 e pi p, Pred (l1 ++ map (wn e) lw ++ l2) pi ->
                     Pred (l1 ++ map (wn e) lw' ++ l2) (ex_wn_r P l1 lw lw' l2 e pi p)) ->
           (forall L eqpmix PL, Forall_Proofs Pred PL -> Pred (concat L) (mix_r P L eqpmix PL)) ->
           (Pred (one :: nil) (one_r P)) ->
           (forall l pi, Pred l pi -> Pred (bot :: l) (bot_r P l pi)) ->
           (forall A B l1 l2 pi1 pi2, Pred (A :: l1) pi1 -> Pred (B :: l2) pi2 ->
                     Pred (tens A B :: l2 ++ l1) (tens_r P A B l1 l2 pi1 pi2)) ->
           (forall A B l pi, Pred (A :: B :: l) pi -> Pred (parr A B :: l) (parr_r P A B l pi)) ->
           (forall l, Pred (top :: l) (top_r P l)) ->
           (forall A B l pi, Pred (A :: l) pi -> Pred (aplus A B :: l) (plus_r1 P A B l pi)) ->
           (forall A B l pi, Pred (A :: l) pi -> Pred (aplus B A :: l) (plus_r2 P A B l pi)) ->
           (forall A B l pi1 pi2, Pred (A :: l) pi1 -> Pred (B :: l) pi2 -> Pred (awith A B :: l) (with_r P A B l pi1 pi2)) ->
           (forall e A l pi pleq, Pred (A :: map (fun p => wn (fst p) (snd p)) l) pi -> Pred (oc e A :: map (fun p => wn (fst p) (snd p)) l) (ocg_r P e A l pi pleq)) ->
           (forall e A l pi pleq, Pred (A :: map (fun p => (snd p)) l) pi -> Pred (oc e A :: map (fun p => wn (fst p) (snd p)) l) (ocf_r P e A l pi pleq)) ->
           (forall e e' A B pi pleq, Pred (A :: B :: nil) pi -> Pred (oc e A :: wn e' B :: nil) (ocu_r P e e' A B pi pleq)) ->
           (forall i e A l pi p, Pred ((repeat A i) ++ l) pi -> Pred (wn e A :: l) (mpx_r P i e A l pi p)) ->
           (forall i e A l pi p, Pred ((repeat (wn e A) (i+2)) ++ l) pi -> Pred (wn e A :: l) (co_r P i e A l pi p)) ->
           (forall e A l pi p, Pred ((wn e (wn e A)) :: l) pi -> Pred (wn e A :: l) (dg_r P e A l pi p)) ->
           (forall f A l1 l2 pi1 pi2, Pred (dual A :: l1) pi1 -> Pred (A :: l2) pi2 ->
                     Pred (l2 ++ l1) (@cut_r P f A l1 l2 pi1 pi2)) ->
           (forall a, Pred (projT2 (pgax P) a) (gax_r P a)) ->
           Pred l pi
    :=
      fun Pred ax_case ex_case ex_wn_case mix_case one_case bot_case tens_case parr_case
               top_case plus_case1 plus_case2 with_case ocg_case ocf_case ocu_case mpx_case 
               co_case dg_case cut_case gax_case =>
      let rec_call {l : list formula} (pi : ll P l) :=
        (ll_nested_ind pi Pred ax_case ex_case ex_wn_case mix_case one_case bot_case tens_case parr_case
                               top_case plus_case1 plus_case2 with_case ocg_case ocf_case ocu_case mpx_case 
                               co_case dg_case cut_case gax_case) in
    match pi with
    | ax_r _ X => ax_case X
    | ex_r _ l1 l2 pi p => ex_case l1 l2 pi p (rec_call pi)
    | ex_wn_r _ l1 lw lw' l2 e pi p => ex_wn_case l1 lw lw' l2 e pi p (rec_call pi)
    | mix_r _ L eqpmix PL => mix_case L eqpmix PL (
                (fix ll_nested_ind_aux (L : list (list formula)) (PL : Forall_Type (ll P) L) : Forall_Proofs Pred PL :=
                   match PL with
                   | Forall_Type_nil _ => Dependent_Forall_Type_nil Pred
                   | @Forall_Type_cons _ _ l L Pil PiL => Dependent_Forall_Type_cons Pred l Pil PiL (rec_call Pil)
                                                            (ll_nested_ind_aux L PiL)
                   end) L PL)
    | one_r _ => one_case
    | bot_r _ l pi => bot_case l pi (rec_call pi)
    | tens_r _ A B l1 l2 pi1 pi2 => tens_case A B l1 l2 pi1 pi2 (rec_call pi1) (rec_call pi2)
    | parr_r _ A B l pi => parr_case A B l pi (rec_call pi)
    | top_r _ l => top_case l
    | plus_r1 _ A B l pi => plus_case1 A B l pi (rec_call pi)
    | plus_r2 _ A B l pi => plus_case2 A B l pi (rec_call pi)
    | with_r _ A B l pi1 pi2 => with_case A B l pi1 pi2 (rec_call pi1) (rec_call pi2)
    | ocg_r _ e A l pi pleq => ocg_case e A l pi pleq (rec_call pi)
    | ocf_r _ e A l pi pleq => ocf_case e A l pi pleq (rec_call pi)
    | ocu_r _ e e' A B pi pleq => ocu_case e e' A B pi pleq (rec_call pi)
    | mpx_r _ i e l A pi p => mpx_case i e l A pi p (rec_call pi)
    | co_r _ i e l A pi p => co_case i e l A pi p (rec_call pi)
    | dg_r _ e l A pi p => dg_case e l A pi p (rec_call pi)
    | @cut_r _ f A l1 l2 pi1 pi2 => cut_case f A l1 l2 pi1 pi2 (rec_call pi1) (rec_call pi2)
    | gax_r _ a => gax_case a
    end.

  Import EqNotations.

  Lemma ll_nested_ind' {l} (pi : ll P l): forall (Pred : forall l, ll P l -> Type),
            (forall X, Pred (covar X :: var X :: nil) (ax_r P X)) ->
            (forall l1 l2 pi p, Pred l1 pi -> Pred l2 (ex_r P l1 l2 pi p)) ->
            (forall l1 lw lw' l2 e pi p, Pred (l1 ++ map (wn e) lw ++ l2) pi ->
               Pred (l1 ++ map (wn e) lw' ++ l2) (ex_wn_r P l1 lw lw' l2 e pi p)) ->
            (forall L eqpmix, Forall_Type (fun x => Pred (projT1 x) (projT2 x)) L ->
               Pred _ (mix'_r P L eqpmix)) ->
            (Pred (one :: nil) (one_r P)) ->
            (forall l pi, Pred l pi -> Pred (bot :: l) (bot_r P l pi)) ->
            (forall A B l1 l2 pi1 pi2, Pred (A :: l1) pi1 -> Pred (B :: l2) pi2 ->
               Pred (tens A B :: l2 ++ l1) (tens_r P A B l1 l2 pi1 pi2)) ->
            (forall A B l pi, Pred (A :: B :: l) pi -> Pred (parr A B :: l) (parr_r P A B l pi)) ->
            (forall l, Pred (top :: l) (top_r P l)) ->
            (forall A B l pi, Pred (A :: l) pi -> Pred (aplus A B :: l) (plus_r1 P A B l pi)) ->
            (forall A B l pi, Pred (A :: l) pi -> Pred (aplus B A :: l) (plus_r2 P A B l pi)) ->
            (forall A B l pi1 pi2, Pred (A :: l) pi1 -> Pred (B :: l) pi2 ->
               Pred (awith A B :: l) (with_r P A B l pi1 pi2)) ->
            (forall e A l pi pleq, Pred (A :: map (fun p => wn (fst p) (snd p)) l) pi -> Pred (oc e A :: map (fun p => wn (fst p) (snd p)) l) (ocg_r P e A l pi pleq)) ->
            (forall e A l pi pleq, Pred (A :: map (fun p => (snd p)) l) pi -> Pred (oc e A :: map (fun p => wn (fst p) (snd p)) l) (ocf_r P e A l pi pleq)) ->
            (forall e e' A B pi pleq, Pred (A :: B :: nil) pi -> Pred (oc e A :: wn e' B :: nil) (ocu_r P e e' A B pi pleq)) ->
            (forall i e A l pi p, Pred ((repeat A i) ++ l) pi -> Pred (wn e A :: l) (mpx_r P i e A l pi p)) ->
            (forall i e A l pi p, Pred ((repeat (wn e A) (i+2)) ++ l) pi -> Pred (wn e A :: l) (co_r P i e A l pi p)) ->
            (forall e A l pi p, Pred ((wn e (wn e A)) :: l) pi -> Pred (wn e A :: l) (dg_r P e A l pi p)) ->
            (forall f A l1 l2 pi1 pi2, Pred (dual A :: l1) pi1 -> Pred (A :: l2) pi2 ->
              Pred (l2 ++ l1) (@cut_r P f A l1 l2 pi1 pi2)) ->
            (forall a, Pred (projT2 (pgax P) a) (gax_r P a)) ->
            Pred l pi.
  Proof with try eassumption.
    intros Pred ? ? ? Hmix ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ?.
    apply ll_nested_ind...
    intros L e f HP.
    enough (Pred (flat_map (projT1 (P:=ll P)) (Forall_to_list f))
                  (rew <- [fun l => ll P l] flat_map_concat_map (projT1 (P:=ll P)) (Forall_to_list f) in
                      mix_r P (map (projT1 (P:=ll P)) (Forall_to_list f))
                            (eq_ind_r (fun n => pmix P n = true)
                               (eq_ind_r (fun n => pmix P n = true) e (Forall_to_list_length L f))
                               (map_length (projT1 (P:=ll P)) (Forall_to_list f)))
                            (list_to_Forall (Forall_to_list f)))) as HL.
    { clear - HL.
      rewrite (flat_map_concat_map (@projT1 _ (ll P)) (Forall_to_list f)) in HL ;
        unfold eq_rect_r in HL ; simpl in HL.
      rewrite <- (Forall_to_list_to_Forall _ f).
      replace e with
          (rew [fun n : nat => pmix P n = true]
               f_equal (length (A:=list formula))
               (Forall_to_list_support L f) in
              eq_ind_r (fun n => pmix P n = true)
                       (eq_ind_r (fun n => pmix P n = true) e
                                 (Forall_to_list_length L f))
                       (map_length (projT1 (P:=ll P)) (Forall_to_list f))) by apply UIP_bool.
      rewrite <- (Forall_to_list_support L f) ; simpl ; assumption. }
    apply Hmix.
    clear e.
    induction HP ; simpl ; constructor...
  Qed.



End ll_ind.

Ltac induction_ll X L l l1 l2 lw lw' e pi e e' A B a H :=
  match type of H with
  | ll _ _ => apply (ll_nested_ind' H) ; [intros X
                            | intros l1 l2 pi Hpcperm IH
                            | intros l1 lw lw' l2 e pi Hperm IH
                            | intros L eqpmix IH
                            | 
                            | intros l pi IH
                            | intros A B l1 l2 pil pir IHl IHr
                            | intros A B l pi IH
                            | intros l
                            | intros A B l pi IH
                            | intros A B l pi IH
                            | intros A B l pil pir IHl IHr
                            | intros e A l pi plen IH
                            | intros e A l pi plen IH
                            | intros e e' A B pi pleq IH
                            | intros i e A l pi Hmix IH
                            | intros i e A l pi Hco IH
                            | intros e A l pi Hdg IH
                            | intros Hcut A l1 l2 pil pir Hl Hr
                            | intros a ]
  end.

(* Goal forall l P (Q: forall l, ll P l -> Type) (pi : ll P l), Q l pi.
intros.
induction_ll X L l'' l1 l2 lw lw' e pi' e e' A B a pi.
apply (ll_nested_ind' pi). - intros X. admit.
                            - intros l1 l2 pi' p IH. admit.
                            - intros l1 lw lw' l2 e pi' p IH. admit.
                            - intros L eqpmix IH. admit.
                            - admit.
                            - intros l'' pi' IH. admit.
                            - intros A B l1 l2 pil pir IHl IHr. admit.
                            - intros A B l'' pi' IH. admit.
                            - intros l''. admit.
                            - intros A B l'' pi' IH. admit.
                            - intros A B l'' pi' IH. admit.
                            - intros A B l'' pil pir IHl IHr. admit.
                            - intros e A l'' pi' pleq IH. admit.
                            - intros e A l'' pi' pleq IH. admit.
                            - intros e A B pi' pleq IH. admit.
                            - intros i e A l'' pi' p IH. admit.
                            - intros i e A l'' pi' p IH. admit.
                            - intros e A l'' pi' p IH. admit.
                            - intros f A l1 l2 pil pir Hl Hr. admit.
                            - intros a. admit.
- intros X. admit.
- Check ex_r. intros l1 l2 pi0 Hperm IH. Check ex_r.
induction_ll f X1 L l l1 l2 lw lw' e eqpmix p pi' pil pir e e' A B a plen pleq pi.*)


Instance ll_perm {P} : Proper ((@PCperm_Type _ (pperm P)) ==> Basics.arrow) (ll P).
Proof.
intros l1 l2 HP pi ; eapply ex_r ; eassumption.
Qed.

Fixpoint psize {P l} (pi : ll P l) :=
match pi with
| ax_r _ _ => 1
| ex_r _ _ _ pi0 _ => S (psize pi0)
| ex_wn_r _ _ _ _ _ e pi0 _ => S (psize pi0)
| mix_r _ L _ PL => S ((fix psize_Forall P L (PL : Forall_Type (ll P) L) {struct PL} :=
       match PL with
       | Forall_Type_nil _ => 0
       | @Forall_Type_cons _ _ l L Pl PL => (psize Pl) + (psize_Forall P L PL)
       end) P L PL)
| one_r _ => 1
| bot_r _ _ pi0 => S (psize pi0)
| tens_r _ _ _ _ _ pi1 pi2 => S (psize pi1 + psize pi2)
| parr_r _ _ _ _ pi0 => S (psize pi0)
| top_r _ _ => 1
| plus_r1 _ _ _ _ pi0 => S (psize pi0)
| plus_r2 _ _ _ _ pi0 => S (psize pi0)
| with_r _ _ _ _ pi1 pi2 => S (max (psize pi1) (psize pi2))
| ocg_r _ _ _ _ pi0 _ => S (psize pi0)
| ocf_r _ _ _ _ pi0 _ => S (psize pi0)
| ocu_r _ _ _ _ _ pi0 _ => S (psize pi0)
| mpx_r _ _ _ _ _ pi0 _ => S (psize pi0)
| co_r _ _ _ _ _ pi0 _ => S (psize pi0)
| dg_r _ _ _ _ pi0 _ => S (psize pi0)
| cut_r _ _ _ _ pi1 pi2 => S (psize pi1 + psize pi2)
| gax_r _ _ => 1
end.

Lemma psize_pos P : forall l (pi : @ll P l), 0 < psize pi.
Proof.
  intros l pi ; destruct pi; simpl; myeasy.
Qed.

Lemma psize_mix P : forall L eq FL,
    psize (mix_r P L eq FL) = S (Forall_Type_sum _ (fun _ pi => psize pi) L FL).
Proof with try assumption; try reflexivity.
  intros L eq FL.
  simpl.
  destruct eq.
  induction FL...
  simpl; rewrite 2 plus_n_Sm.
  rewrite IHFL...
Qed.

Lemma psize_inf_mix P : forall L eq FL l pi,
  In_Forall_Type (ll P) l pi FL -> psize pi < psize (mix_r P L eq FL).
Proof with try lia.
  intros L eq FL l pi Hin ; simpl ; clear eq.
  induction FL ; [inversion Hin | inversion Hin as [Hexist|]].
  - inversion Hexist; subst...
  - specialize (IHFL X)...
Qed.

(** List of the elements of [pgax P] used in [pi] *)
Fixpoint gax_elts {P l} (pi : ll P l) :=
match pi with
| ax_r _ _ => nil
| ex_r _ _ _ pi0 _ => gax_elts pi0
| ex_wn_r _ _ _ _ _ _ pi0 _ => gax_elts pi0
| mix_r _ L _ PL => (fix gax_elts_Forall P L (PL : Forall_Type (ll P) L) {struct PL} :=
       match PL with
       | Forall_Type_nil _ => nil
       | @Forall_Type_cons _ _ l L Pl PL => (gax_elts Pl) ++ (gax_elts_Forall P L PL)
       end) P L PL
| one_r _ => nil
| bot_r _ _ pi0 => gax_elts pi0
| tens_r _ _ _ _ _ pi1 pi2 => (gax_elts pi1) ++ (gax_elts pi2)
| parr_r _ _ _ _ pi0 => gax_elts pi0
| top_r _ _ => nil
| plus_r1 _ _ _ _ pi0 => gax_elts pi0
| plus_r2 _ _ _ _ pi0 => gax_elts pi0
| with_r _ _ _ _ pi1 pi2 => (gax_elts pi1) ++ (gax_elts pi2)
| ocg_r _ _ _ _ pi0 _ => gax_elts pi0
| ocf_r _ _ _ _ pi0 _ => gax_elts pi0
| ocu_r _ _ _ _ _ pi0 _ => gax_elts pi0
| mpx_r _ _ _ _ _ pi0 _ => gax_elts pi0
| co_r _ _ _ _ _ pi0 _ => gax_elts pi0
| dg_r _ _ _ _ pi0 _ => gax_elts pi0
| cut_r _ _ _ _ pi1 pi2 => (gax_elts pi1) ++ (gax_elts pi2)
| gax_r _ a => a :: nil
end.

Lemma gax_elts_mix {P} : forall L eq FL l pi, In_Forall_Type (ll P) l pi FL ->
  forall ax, In_Type ax (gax_elts pi) -> In_Type ax (gax_elts (mix_r P L eq FL)).
Proof with try assumption;try reflexivity.
  intros L eq FL; simpl; clear eq.
  induction FL; intros l' pi Hin; [inversion Hin| inversion Hin as [Heq|]].
  - inversion Heq; subst.
    intros ax Hin_ax.
    apply in_Type_or_app.
    left...
  - intros ax Hin_ax.
    apply in_Type_or_app.
    right.
    apply IHFL with l' pi...
Qed.

(* Unused
Lemma same_pfrag P Q : eq_pfrag P Q ->
                       forall l, ll P l -> ll Q l.
Proof with myeeasy.
  intros Heq l pi.
  induction pi using ll_nested_ind' ; try (constructor ; myeasy ; fail).
  - apply (ex_r _ l1)...
    destruct Heq as (_ & _ & _  & Hp).
    unfold PCperm_Type in p.
    unfold PCperm_Type.
    destruct (pperm P) ; destruct (pperm Q) ;
      simpl in Hp ; try inversion Hp...
  - apply (ex_wn_r _ l1 lw)...
  - assert ({L' : list (sigT (ll Q)) & (map (@projT1 _ (ll Q)) L') = (map (@projT1 _ (ll P)) L)}) as (L' & eqL').
    + destruct eqpmix.
      induction L.
      * split with nil.
        reflexivity.
      * inversion X; subst.
        destruct IHL as (L' & eq)...
        split with (existT (ll Q) (projT1 a) X0 :: L')...
        simpl.
        rewrite eq.
        reflexivity.
    + rewrite flat_map_concat_map; rewrite<- eqL'; rewrite<- flat_map_concat_map.
      apply mix'_r.
      destruct Heq as (_ & _ & Hpmix & _).
      specialize Hpmix with (length L).
      rewrite<- map_length with _ _ (@projT1 _ (ll Q)) L'.
      rewrite eqL'.
      rewrite map_length.
      case_eq (pmix Q (length L)); intros eq...
      rewrite eq, eqpmix in Hpmix.
      inversion Hpmix.
  - unfold eq_pfrag in Heq.
    destruct Heq as [Hcut _].
    rewrite f in Hcut.
    symmetry in Hcut.
    eapply (@cut_r _ Hcut)...
  - destruct Heq as (_ & (Hgax & _) & _).
    destruct (Hgax a) as [b Heq].
    rewrite Heq.
    apply gax_r.
Qed.
*)
(* fin nettoyage *)
Lemma stronger_pfrag P Q : le_pfrag P Q -> forall l, ll P l -> ll Q l.
Proof with myeeasy.
intros Hle l Hlproof.
(* apply (ll_nested_ind' Hlproof) with (Pred:=(fun l _ => ll Q l)).
revert Hlproof. apply ll_nested_ind' with (l:=l).
induction_ll X L l l1 l2 lw lw' e pi e e' A B a Hlproof.*)
induction Hlproof using ll_nested_ind'; try (constructor ; myeasy ; fail).
- apply (ex_r _ l1)...
  destruct Hle as (_ & _ & _  & Hp & _ ).
  unfold PCperm_Type in p.
  unfold PCperm_Type.
  destruct (pperm P) ; destruct (pperm Q) ;
    simpl in Hp ; try inversion Hp...
  apply cperm_perm_Type...
- apply (ex_wn_r _ l1 lw)...
- assert ({L' : list (sigT (ll Q)) & (map (@projT1 _ (ll Q)) L') = (map (@projT1 _ (ll P)) L)}) as (L' & eqL').
  + destruct eqpmix.
    induction L.
    * split with nil.
      reflexivity.
    * inversion_clear X as [|? ? pi].
      destruct IHL as (L' & eq)...
      split with (existT (ll Q) (projT1 a) pi :: L')...
      simpl.
      rewrite eq.
      reflexivity.
  + rewrite flat_map_concat_map; rewrite<- eqL'; rewrite<- flat_map_concat_map.
    apply mix'_r.
    destruct Hle as (_ & _ & Hpmix & _).
    specialize Hpmix with (length L).
    rewrite<- map_length with _ _ (@projT1 _ (ll Q)) L'.
    rewrite eqL'.
    rewrite map_length.
    case_eq (pmix Q (length L)); intros eq...
    rewrite eq, eqpmix in Hpmix.
    inversion Hpmix.
- apply ocg_r...
  destruct Hle as (_ & _ & _  & _ & _ & Hp & _).
  clear - pleq Hp.
  induction (map (fun p : Sset * formula => fst p) l0); constructor.
  + inversion pleq. 
      specialize Hp with e a. rewrite H1 in Hp...
  + inversion pleq. apply IHl... 
- apply ocf_r...
  destruct Hle as (_ & _ & _  & _ & _ & _ & Hp & _).
  clear - pleq Hp.
  induction (map (fun p : Sset * formula => fst p) l0).
  + left. 
  + right.
    * inversion pleq.
      specialize Hp with e a. rewrite H1 in Hp...
    * inversion pleq. apply IHl... 
- apply ocu_r...
  destruct Hle as (_ & _ & _  & _ & _ & _ & _ & Hp).
  clear - pleq Hp.
  unfold is_true in pleq.
  specialize Hp with e e'. rewrite pleq in Hp. unfold leb in Hp...
- apply mpx_r with i...
  destruct Hle as (_ & _ & _ & _ & Hp & _).
  specialize Hp with e (mpx_rule i). rewrite p in Hp...
- apply co_r with i...
  destruct Hle as (_ & _ & _ & _ & Hp & _).
  specialize Hp with e (co_rule i). rewrite p in Hp...
- apply dg_r...
  destruct Hle as (_ & _ & _ & _ & Hp & _).
  specialize Hp with e dg_rule. rewrite p in Hp...
- unfold le_pfrag in Hle.
  destruct Hle as [Hcut _].
  rewrite f in Hcut.
  simpl in Hcut...
  eapply (@cut_r _ Hcut)...
- destruct Hle as (_ & Hgax & _).
  destruct (Hgax a) as [b Heq].
  rewrite Heq.
  apply gax_r.
Qed.

(** *** Variants of rules *)

(** Multiplexing on a list of formulas *)
Lemma mpx_list_r {P} : forall l i l', ll P (flat_map (fun p => repeat (snd p) i) l ++ l') -> 
                       Forall (fun p => is_true (sig P (fst p) (mpx_rule i))) l ->
                       ll P ((map (fun p => wn (fst p) (snd p)) l) ++ l').
Proof with myeeasy.
induction l; intros i l' H...
- intro H1...
- intro H1. apply mpx_r with i.
  apply ex_r with ((map (fun p => wn (fst p) (snd p)) l) ++ l' ++ repeat (snd a) i).
  + apply IHl with i.
    * apply ex_r with (flat_map (fun p : Sset * formula => repeat (snd p) i) (a :: l) ++ l')...
      case_eq (pperm P); intro ppermH; unfold PCperm_Type; [perm_Type_solve|cperm_Type_solve].
    * inversion H1...
  + case_eq (pperm P); intro ppermH; unfold PCperm_Type; [perm_Type_solve|cperm_Type_solve].
  + inversion H1...
Qed.

Lemma wk_list_r {P} : forall l l', ll P l' -> 
                       Forall (fun p => is_true (sig P (fst p) (mpx_rule 0))) l ->
                       ll P ((map (fun p => wn (fst p) (snd p)) l) ++ l').
Proof with myeasy.
intros l l' Hp Hmpx0.
apply mpx_list_r with 0...
induction l.
- list_simpl...
- list_simpl ; apply IHl.
  inversion Hmpx0...
Qed.

(** Contraction on a list of formulas *)
Lemma co_list_r {P} : forall l i l', ll P (flat_map (fun p => repeat (wn (fst p) (snd p)) (i+2)) l ++ l') -> 
                       Forall (fun p => is_true (sig P (fst p) (co_rule i))) l ->
                       ll P ((map (fun p => wn (fst p) (snd p)) l) ++ l').
Proof with myeeasy.
induction l; intros i l' H...
- intro H1...
- intro H1. apply co_r with i.
  apply ex_r with ((map (fun p => wn (fst p) (snd p)) l) ++ l' ++ repeat (wn (fst a) (snd a)) (i+2)).
  + apply IHl with i.
    * apply ex_r with (flat_map (fun p : Sset * formula => repeat (wn (fst p) (snd p)) (i+2)) (a :: l) ++ l')...
      case_eq (pperm P); intro ppermH; unfold PCperm_Type; [perm_Type_solve|cperm_Type_solve].
    * inversion H1...
  + case_eq (pperm P); intro ppermH; unfold PCperm_Type; [perm_Type_solve|cperm_Type_solve].
  + inversion H1...
Qed.
(*Lemma co_const_list_r P : forall n A l,
      ll P (repeat (wn A) n ++ l) -> ll P ((wn A) :: l).
Proof with try assumption.
  intros n.
  induction n; intros A l pi.
  - apply wk_r...
  - apply co_r.
    apply IHn.
    simpl in pi.
    change (wn A :: repeat (wn A) n ++ l) with ((wn A :: repeat (wn A) n) ++ l) in pi.
    rewrite repeat_cons in pi.
    rewrite<- app_assoc in pi...
Qed.
*)

(** Special rules regarding the concat operator *)
Lemma co_list_gen_perm_r {P} (P_perm : pperm P = true) : forall L l0 l,
    Forall (fun p => is_true (sig P (fst p) (mpx_rule 0))) l0 ->
    Forall (fun p => is_true (sig P (fst p) (co_rule 0))) l0 ->
    ll P (l ++ flat_map (app (map (fun p => wn (fst p) (snd p)) l0)) L) ->
    ll P (l ++ (map (fun p => wn (fst p) (snd p)) l0) ++ concat L).
Proof with myeasy.
  intros L.
  induction L ; intros l0 l Hwk Hco pi.
  - apply ex_r with (map (fun p => wn (fst p) (snd p)) l0 ++ l ++ concat nil).
    + apply wk_list_r...
    + rewrite P_perm; simpl; perm_Type_solve.
  - apply ex_r with (map (fun p => wn (fst p) (snd p)) l0 ++ l ++ concat (a :: L)) ; [ | rewrite P_perm; simpl; try perm_Type_solve].
    apply co_list_r with 0...
    apply ex_r with ((l ++ (map (fun p => wn (fst p) (snd p)) l0 ++ a)) ++ map (fun p => wn (fst p) (snd p)) l0 ++ concat L) ; 
     [ | rewrite P_perm; simpl; clear ; induction l0 ; [perm_Type_solve | unfold flat_map ; perm_Type_solve ]].
    apply IHL...
    rewrite<- app_assoc.
    simpl in pi...
Qed.
(**)

Lemma ex_concat_r P : pperm P = true -> forall l A L,
      ll P (l ++ flat_map (cons A) L) -> ll P (l ++ repeat A (length L) ++ concat L).
Proof with try assumption.
  intros f l A L. revert f l A.
  induction L; intros f l A pi...
  simpl.
  apply ex_r with ((A :: l ++ a) ++ repeat A (length L) ++ concat L) ; [ | rewrite f; simpl; perm_Type_solve]...
  apply IHL...
  eapply ex_r with (l ++ (A :: a) ++ flat_map (cons A) L) ; [ | rewrite f; simpl; perm_Type_solve]...
Qed.


(** n-ary versions of tens and parr rules *)
Lemma tens_n_r P : forall L A, Forall_Type (ll P) (map (cons A) L) ->
  ll P (tens_n (length L) A :: concat L).
Proof with try assumption.
induction L; intros A FL.
- apply one_r.
- destruct L; list_simpl; inversion FL...
  subst.
  apply tens_r...
  apply IHL...
Qed.

Lemma parr_n_r P : forall l n A, ll P (repeat A n ++ l) ->
  ll P (parr_n n A :: l).
Proof with try assumption.
  intros l n; revert l.
  induction n; intros l A pi.
  - apply bot_r...
  - destruct n...
    apply parr_r.
    apply ex_r with (parr_n (S n) A :: (l ++ (A :: nil))); [ | PCperm_Type_solve].
    apply IHn.
    eapply ex_r ; [apply pi | PCperm_Type_solve].
Qed.

(** Permutation on mix *)
Lemma ex_mix_r {P} : forall L L' (eq : is_true (pmix P (length L))) (p : Permutation_Type L L'),
    Forall_Type (ll P) L -> ll P (concat L').
Proof with try assumption.
  intros L L' eq p FL.
  apply mix_r.
  - replace (length L') with (length L)...
    apply Permutation_Type_length...
  - apply forall_Forall_Type.
    intros l Hin.
    apply (@Forall_Type_forall (list formula) (ll P) L)...
    apply Permutation_Type_in_Type with L'...
    apply Permutation_Type_sym...
Qed.

(** *** Some tactics for manipulating rules *)
Ltac destruct_ll H f X l Hl Hr HP FL a :=
  match type of H with
  | ll _ _ => destruct H as [ X
                            | l ? Hl HP
                            | l ? ? ? Hl HP
                            | ? f FL
                            | 
                            | ? Hl
                            | ? ? ? ? Hl Hr
                            | ? ? ? Hl
                            | l
                            | ? ? ? Hl
                            | ? ? ? Hl
                            | ? ? ? Hl Hr
                            | ? ? Hl
                            | ? ? Hl
                            | ? ? Hl
                            | ? ? Hl
                            | f ? ? ? Hl Hr
                            | a ] ; subst
  end.

Ltac ll_swap :=
  match goal with
  | |- ll ?P (?a1 :: ?a2 :: nil) => eapply ex_r ; [ | apply PCperm_Type_swap ]
  end.
Ltac ll_swap_hyp H :=
  match goal with
  | H : ll ?P (?a1 :: ?a2 :: nil) |- _ =>
        eapply ex_r in H ;[ | apply PCperm_Type_swap ]
  end.
Tactic Notation "ll_swap" "in" hyp(H) := ll_swap_hyp H.


(** ** Some reversibility statements *)

Lemma bot_rev {P} : (forall a, In_Type bot (projT2 (pgax P) a) -> False) ->
  forall l1 l2, ll P (l1 ++ bot :: l2) -> ll P (l1 ++ l2).
Proof with myeeasy.
intros Hgax l1 l2 pi.
remember (l1 ++ bot :: l2) as l ; revert l1 l2 Heql.
induction pi using ll_nested_ind ; intros l1' l2' Heq ; subst.
- exfalso.
  destruct l1' ; inversion Heq.
  destruct l1' ; inversion H1.
  destruct l1' ; inversion H3.
- apply PCperm_Type_vs_elt_inv in p.
  destruct p as [(l3 & l4) Heq HP'].
  simpl in HP' ; simpl in Heq.
  apply IHpi in Heq...
  eapply ex_r...
  apply PEperm_PCperm_Type in HP' ; unfold id in HP'.
  apply PCperm_Type_sym.
  eapply PCperm_Type_trans ; [ apply PCperm_Type_app_comm | ].
  eapply PCperm_Type_trans ; [ apply HP' | ].
  apply PCperm_Type_app_comm.
- dichot_Type_elt_app_exec Heq ; subst.
  + rewrite app_assoc.
    eapply ex_wn_r...
    list_simpl ; apply IHpi ; list_simpl...
  + dichot_Type_elt_app_exec Heq1 ; subst.
    * exfalso.
      decomp_map Heq0 ; inversion Heq0.
    * list_simpl ; eapply ex_wn_r...
      rewrite 2 app_assoc.
      apply IHpi ; list_simpl...
- apply concat_elt in Heq as ([[[L1 L2] l1] l2] & eqb & eqt & eq); subst.
  apply Dependent_Forall_Type_app_inv in X as ((l1' & Fl1) & (l2' & Fl2)).
  inversion Fl2; subst.
  replace ((concat L1 ++ l1) ++ l2 ++ concat L2) with (concat (L1 ++ (l1 ++ l2) :: L2)) ;
    [ | rewrite concat_app; simpl; rewrite 3 app_assoc; reflexivity].
  apply mix_r...
  + rewrite app_length.
    rewrite app_length in eqpmix...
  + apply Forall_Type_app...
    apply Forall_Type_cons...
    apply (X _ _ eq_refl).
- exfalso.
  destruct l1' ; inversion Heq.
  destruct l1' ; inversion H1.
- destruct l1' ; inversion Heq ; subst...
  list_simpl ; eapply bot_r.
  apply IHpi...
- rewrite app_comm_cons in Heq ; dichot_Type_elt_app_exec Heq ; subst.
  + destruct l1' ; inversion Heq0 ; subst.
    list_simpl.
    rewrite app_assoc ; apply tens_r...
    rewrite app_comm_cons.
    apply IHpi2...
  + list_simpl.
    apply tens_r...
    rewrite app_comm_cons.
    apply IHpi1...
- destruct l1' ; inversion Heq ; subst.
  rewrite 2 app_comm_cons in IHpi.
  list_simpl ; eapply parr_r...
  rewrite 2 app_comm_cons.
  apply IHpi...
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; apply top_r...
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply plus_r1...
  rewrite app_comm_cons.
  apply IHpi...
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply plus_r2...
  rewrite app_comm_cons.
  apply IHpi...
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply with_r...
  + rewrite app_comm_cons.
    apply IHpi1...
  + rewrite app_comm_cons.
    apply IHpi2...
- exfalso.
  destruct l1' ; inversion Heq.
  symmetry in H1.
  decomp_map H1.
  inversion H1.
- exfalso.
  destruct l1' ; inversion Heq.
  symmetry in H1.
  decomp_map H1.
  inversion H1.
- exfalso.
  destruct l1'; inversion Heq.
  destruct l1'; inversion Heq.
  destruct l1'; inversion Heq.
- destruct l1' ; inversion Heq ; subst.
  list_simpl. eapply mpx_r...
  rewrite app_assoc. 
  apply IHpi; list_simpl...
- destruct l1' ; inversion Heq ; subst.
  list_simpl. eapply co_r...
  rewrite app_assoc. 
  apply IHpi; list_simpl...
- destruct l1' ; inversion Heq ; subst.
  list_simpl. eapply dg_r...
  rewrite app_assoc. rewrite app_comm_cons.
  apply IHpi; list_simpl...
- dichot_Type_elt_app_exec Heq ; subst.
  + rewrite app_assoc ; eapply cut_r...
    rewrite app_comm_cons.
    eapply IHpi2...
  + rewrite <- app_assoc ; eapply cut_r...
    rewrite app_comm_cons.
    eapply IHpi1...
- exfalso.
  apply (Hgax a) ; rewrite Heq.
  apply in_Type_elt.
Qed.

Lemma parr_rev {P} : (forall a A B, In_Type (parr A B) (projT2 (pgax P) a) -> False) ->
  forall A B l1 l2, ll P (l1 ++ parr A B :: l2) -> ll P (l1 ++ A :: B :: l2).
Proof with myeeasy.
intros Hgax A B l1 l2 pi.
remember (l1 ++ parr A B :: l2) as l.
revert A B l1 l2 Heql.
induction pi using ll_nested_ind ; intros A' B' l1' l2' Heq ; subst.
- exfalso.
  destruct l1' ; inversion Heq.
  destruct l1' ; inversion H1.
  destruct l1' ; inversion H3.
- apply PCperm_Type_vs_elt_inv in p.
  destruct p as [(l3 & l4) Heq HP'].
  simpl in HP'.
  apply IHpi in Heq...
  eapply ex_r...
  destruct (pperm P) ; simpl in HP' ; simpl.
  + apply Permutation_Type_sym.
    eapply Permutation_Type_trans ; [ apply Permutation_Type_app_comm | ].
    eapply Permutation_Type_trans ; [ | apply Permutation_Type_app_comm ].
    perm_Type_solve.
  + eapply cperm_Type_trans ; [ apply cperm_Type | ].
    list_simpl ; rewrite <- HP' ; cperm_Type_solve.
- dichot_Type_elt_app_exec Heq ; subst.
  + rewrite 2 app_comm_cons ; rewrite app_assoc.
    eapply ex_wn_r...
    list_simpl ; apply IHpi ; list_simpl...
  + dichot_Type_elt_app_exec Heq1 ; subst.
    * exfalso.
      decomp_map Heq0 ; inversion Heq0.
    * list_simpl ; eapply ex_wn_r...
      rewrite 2 app_assoc.
      apply IHpi ; list_simpl...
- apply concat_elt in Heq as ((((L1 & L2) & l1) & l2) & eqb & eqt & eq); subst.
  replace ((concat L1 ++ l1) ++ A' :: B' :: l2 ++ concat L2) with (concat (L1 ++ (l1 ++ A' :: B' :: l2) :: L2)) ;
    [ |rewrite concat_app; simpl; rewrite ? app_comm_cons; rewrite ? app_assoc; reflexivity].
  apply mix_r...
  + rewrite app_length.
    rewrite app_length in eqpmix...
  + destruct (Forall_Type_app_inv _ _ _ PL) as (Fl1 & Fl2).
    apply Forall_Type_app...
    inversion Fl2; subst.
    apply Forall_Type_cons...
    destruct (In_Forall_Type_elt _ _ _ _ PL).
    refine (Dependent_Forall_Type_forall_formula _ _ _ _ _ X i _ _ _ _ eq_refl).
- exfalso.
  destruct l1' ; inversion Heq.
  destruct l1' ; inversion H1.
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply bot_r...
  apply IHpi...
- rewrite app_comm_cons in Heq ; dichot_Type_elt_app_exec Heq ; subst.
  + destruct l1' ; inversion Heq0 ; subst.
    rewrite 2 app_comm_cons ; rewrite app_assoc ; apply tens_r...
    rewrite app_comm_cons.
    apply IHpi2...
  + rewrite <- app_assoc ; apply tens_r...
    rewrite app_comm_cons ; apply IHpi1...
- destruct l1' ; inversion Heq ; subst...
  list_simpl ; eapply parr_r...
  rewrite 2 app_comm_cons.
  apply IHpi...
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; apply top_r...
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply plus_r1...
  rewrite app_comm_cons.
  apply IHpi...
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply plus_r2...
  rewrite app_comm_cons.
  apply IHpi...
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply with_r...
  + rewrite app_comm_cons.
    apply IHpi1...
  + rewrite app_comm_cons.
    apply IHpi2...
- exfalso.
  destruct l1' ; inversion Heq.
  symmetry in H1.
  decomp_map H1.
  inversion H1.
-exfalso.
  destruct l1' ; inversion Heq.
  symmetry in H1.
  decomp_map H1.
  inversion H1.
-exfalso.
  destruct l1' ; inversion Heq.
  induction l1'.
  + discriminate.
  + inversion H1. induction l1'.
    * discriminate.
    * rewrite <- app_comm_cons in H3.  inversion H3. (* il y a plus simple je pense *)
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply mpx_r... rewrite app_assoc.
  apply IHpi. apply app_assoc.
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply co_r... rewrite app_assoc.
  apply IHpi. apply app_assoc.
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply dg_r... rewrite app_assoc. rewrite app_comm_cons.
  apply IHpi. list_simpl...
- dichot_Type_elt_app_exec Heq ; subst.
  + rewrite 2 app_comm_cons ; rewrite app_assoc ; eapply cut_r...
    rewrite app_comm_cons ; apply IHpi2...
  + rewrite <- app_assoc ; eapply cut_r...
    rewrite app_comm_cons ; apply IHpi1...
- exfalso.
  apply (Hgax a A' B') ; rewrite Heq.
  apply in_Type_elt.
Qed.

Lemma one_rev {P} : (forall a, In_Type one (projT2 (pgax P) a) -> False) ->
  forall l0, ll P l0 -> forall l1 l2, ll P (l1 ++ one :: l2) ->
  ll P (l1 ++ l0 ++ l2).
Proof with myeeasy.
intros Hgax l0 pi0 l1 l2 pi.
remember (l1 ++ one :: l2) as l.
revert l1 l2 Heql.
induction pi using ll_nested_ind ; intros l1' l2' Heq ; subst.
- exfalso.
  destruct l1' ; inversion Heq.
  destruct l1' ; inversion H1.
  destruct l1' ; inversion H3.
- apply PCperm_Type_vs_elt_inv in p.
  destruct p as [(l3 & l4) Heq HP'].
  simpl in HP' ; apply IHpi in Heq...
  eapply ex_r...
  destruct (pperm P) ; simpl in HP' ; simpl.
  + apply Permutation_Type_sym.
    eapply Permutation_Type_trans ; [ apply Permutation_Type_app_comm | ].
    eapply Permutation_Type_trans ; [ | apply Permutation_Type_app_comm ].
    perm_Type_solve.
  + eapply cperm_Type_trans ; [ apply cperm_Type | ].
    list_simpl ; rewrite <- HP' ; cperm_Type_solve.
- dichot_Type_elt_app_exec Heq ; subst.
  + rewrite 2 app_assoc.
    eapply ex_wn_r...
    list_simpl ; apply IHpi ; list_simpl...
  + dichot_Type_elt_app_exec Heq1 ; subst.
    * exfalso.
      decomp_map Heq0 ; inversion Heq0.
    * list_simpl ; eapply ex_wn_r...
      rewrite 2 app_assoc.
      apply IHpi ; list_simpl...
- apply concat_elt in Heq as ((((L1 & L2) & l1) & l2) & eqb & eqt & eq); subst.
  replace ((concat L1 ++ l1) ++ l0 ++ l2 ++ concat L2) with (concat (L1 ++ (l1 ++ l0 ++ l2) :: L2)) ;
    [ |rewrite concat_app; simpl; rewrite ? app_comm_cons; rewrite ? app_assoc; reflexivity].
  apply mix_r...
  + rewrite app_length.
    rewrite app_length in eqpmix...
  + destruct (Forall_Type_app_inv _ _ _ PL) as (Fl1 & Fl2).
    apply Forall_Type_app...
    inversion Fl2; subst.
    apply Forall_Type_cons...
    destruct (In_Forall_Type_elt _ _ _ _ PL).
    refine (Dependent_Forall_Type_forall_formula _ _ _ _ _ X i _ _ eq_refl).
- destruct l1' ; inversion Heq ; subst.
  + list_simpl...
  + destruct l1' ; inversion H1.
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply bot_r...
  apply IHpi...
- rewrite app_comm_cons in Heq ; dichot_Type_elt_app_exec Heq ; subst.
  + destruct l1' ; inversion Heq0 ; subst.
    rewrite <- app_comm_cons ; rewrite 2 app_assoc ; apply tens_r...
    list_simpl ; rewrite app_comm_cons ; apply IHpi2...
  + rewrite <- app_assoc ; apply tens_r...
    rewrite app_comm_cons ; apply IHpi1...
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply parr_r...
  rewrite 2 app_comm_cons ; apply IHpi...
- destruct l1' ; inversion Heq ; subst.
   list_simpl ; apply top_r...
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply plus_r1...
  rewrite app_comm_cons.
  apply IHpi...
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply plus_r2...
  rewrite app_comm_cons.
  apply IHpi...
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply with_r...
  + rewrite app_comm_cons.
    apply IHpi1...
  + rewrite app_comm_cons.
    apply IHpi2...
- exfalso.
  destruct l1' ; inversion Heq.
  symmetry in H1.
  decomp_map H1.
  inversion H1.
- exfalso.
  destruct l1' ; inversion Heq.
  symmetry in H1.
  decomp_map H1.
  inversion H1.
- exfalso.
  destruct l1' ; inversion Heq.
  symmetry in H1.
  induction l1'.
  + inversion H1.
  + inversion H1.
    induction l1'.
    * inversion H3.
    * inversion H3.
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply mpx_r...
  rewrite app_assoc.
  apply IHpi. list_simpl...
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply co_r...
  rewrite app_assoc.
  apply IHpi. list_simpl...
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply dg_r...
  rewrite app_assoc.
  rewrite app_comm_cons.
  apply IHpi. list_simpl...
- dichot_Type_elt_app_exec Heq ; subst.
  + rewrite 2 app_assoc ; eapply cut_r...
    list_simpl ; rewrite app_comm_cons ; apply IHpi2...
  + rewrite <- app_assoc ; eapply cut_r...
    rewrite app_comm_cons ; apply IHpi1...
- exfalso.
  apply (Hgax a) ; rewrite Heq.
  apply in_Type_elt.
Qed.

Lemma tens_one_rev {P} :
(forall a, In_Type one (projT2 (pgax P) a) -> False) ->
(forall a A, In_Type (tens one A) (projT2 (pgax P) a) -> False) ->
  forall A l1 l2, ll P (l1 ++ tens one A :: l2) -> ll P (l1 ++ A :: l2).
Proof with myeeasy.
intros Hgax1 Hgaxt A l1 l2 pi.
remember (l1 ++ tens one A :: l2) as l.
revert A l1 l2 Heql.
induction pi using ll_nested_ind ; intros A' l1' l2' Heq ; subst.
- exfalso.
  destruct l1' ; inversion Heq.
  destruct l1' ; inversion H1.
  destruct l1' ; inversion H3.
- apply PCperm_Type_vs_elt_inv in p.
  destruct p as [(l3 & l4) Heq HP'].
  simpl in HP' ; apply IHpi in Heq...
  simpl in Heq ; eapply ex_r...
  destruct (pperm P) ; simpl in HP' ; simpl.
  + apply Permutation_Type_sym.
    eapply Permutation_Type_trans ; [ apply Permutation_Type_app_comm | ].
    eapply Permutation_Type_trans ; [ | apply Permutation_Type_app_comm ].
    perm_Type_solve.
  + eapply cperm_Type_trans ; [ apply cperm_Type | ].
    list_simpl ; rewrite <- HP' ; cperm_Type_solve.
- dichot_Type_elt_app_exec Heq ; subst.
  + rewrite app_comm_cons ; rewrite app_assoc.
    eapply ex_wn_r...
    list_simpl ; apply IHpi ; list_simpl...
  + dichot_Type_elt_app_exec Heq1 ; subst.
    * exfalso.
      decomp_map Heq0 ; inversion Heq0.
    * list_simpl ; eapply ex_wn_r...
      rewrite 2 app_assoc.
      apply IHpi ; list_simpl...
- apply concat_elt in Heq as ((((L1 & L2) & l1) & l2) & eqb & eqt & eq); subst.
  replace ((concat L1 ++ l1) ++ A' :: l2 ++ concat L2) with (concat (L1 ++ (l1 ++ A' :: l2) :: L2)) ;
    [ |rewrite concat_app; simpl; rewrite ? app_comm_cons; rewrite ? app_assoc; reflexivity].
  apply mix_r...
  + rewrite app_length.
    rewrite app_length in eqpmix...
  + destruct (Forall_Type_app_inv _ _ _ PL) as (Fl1 & Fl2).
    apply Forall_Type_app...
    inversion Fl2; subst.
    apply Forall_Type_cons...
    destruct (In_Forall_Type_elt _ _ _ _ PL).
    refine (Dependent_Forall_Type_forall_formula _ _ _ _ _ X i _ _ _ eq_refl).
- destruct l1' ; inversion Heq ; subst.
  destruct l1' ; inversion H1.
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply bot_r...
  apply IHpi...
- rewrite app_comm_cons in Heq ; dichot_Type_elt_app_exec Heq ; subst.
  + destruct l1' ; inversion Heq0 ; subst.
    * rewrite <- (app_nil_l _) in pi1 ; eapply (one_rev Hgax1 _ pi2) in pi1...
    * rewrite <- app_comm_cons ; rewrite (app_comm_cons l0) ; rewrite app_assoc ; apply tens_r...
      rewrite app_comm_cons ; apply IHpi2...
  + rewrite <- app_assoc ; apply tens_r...
    rewrite app_comm_cons ; apply IHpi1...
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply parr_r...
  rewrite 2 app_comm_cons ; apply IHpi...
- destruct l1' ; inversion Heq ; subst.
   list_simpl ; apply top_r...
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply plus_r1...
  rewrite app_comm_cons.
  apply IHpi...
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply plus_r2...
  rewrite app_comm_cons.
  apply IHpi...
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply with_r...
  + rewrite app_comm_cons.
    apply IHpi1...
  + rewrite app_comm_cons.
    apply IHpi2...
- exfalso.
  destruct l1' ; inversion Heq.
  symmetry in H1.
  decomp_map H1.
  inversion H1.
- exfalso.
  destruct l1' ; inversion Heq.
  symmetry in H1.
  decomp_map H1.
  inversion H1.
- exfalso.
  destruct l1' ; inversion Heq.
  symmetry in H1.
  induction l1'.
  + inversion H1.
  + inversion H1.
    induction l1'.
    * inversion H3.
    * inversion H3.
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply mpx_r...
  rewrite app_assoc.
  apply IHpi. list_simpl...
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply co_r...
  rewrite app_assoc.
  apply IHpi. list_simpl...
- destruct l1' ; inversion Heq ; subst.
  list_simpl ; eapply dg_r...
  rewrite app_assoc.
  rewrite app_comm_cons.
  apply IHpi. list_simpl...
- dichot_Type_elt_app_exec Heq ; subst.
  + rewrite app_comm_cons ; rewrite app_assoc ; eapply cut_r...
    list_simpl ; rewrite app_comm_cons ; apply IHpi2...
  + rewrite <- app_assoc ; eapply cut_r...
    rewrite app_comm_cons ; apply IHpi1...
- exfalso.
  apply (Hgaxt a A') ; rewrite Heq.
  apply in_Type_elt.
Qed.

Lemma tens_rev {P} : (forall a A B, projT2 (pgax P) a = tens A B :: nil -> False) ->
  pcut P = false -> forall A B,
  ll P (tens A B :: nil) -> prod (ll P (A :: nil)) (ll P (B :: nil)).
Proof with myeeasy.
intros Hgax Hcut A B pi.
remember (tens A B :: nil) as l ; revert A B Heql ;
  induction pi using ll_nested_ind ; intros A' B' Heq ; subst ;
  try (now inversion Heq).
- apply PCperm_Type_sym in p.
  apply PCperm_Type_length_1_inv in p ; subst.
  apply IHpi...
- destruct l1 ; inversion Heq.
  + destruct lw' ; inversion H0 ; list_simpl in H0.
    symmetry in p ; apply Permutation_Type_nil in p ; subst.
    apply IHpi...
  + apply app_eq_nil in H1 ; destruct H1 ; subst.
    apply app_eq_nil in H1 ; destruct H1 ; subst.
    destruct lw' ; inversion H.
    symmetry in p ; apply Permutation_Type_nil in p ; subst.
    apply IHpi...
- change (tens A' B' :: nil) with (nil ++ tens A' B' :: nil) in Heq.
  apply concat_elt in Heq as ((((L1 & L2) & l1') & l2') & eqb & eqt & eqL); subst.
  destruct l1'.
  + destruct l2' ; try now inversion eqt.
    destruct (Dependent_Forall_Type_app_inv _ _ _ _ X) as ((FL1 & PL1) & (FL2 & PL2)).
    inversion PL2; subst.
    refine (X0 _ _ eq_refl).
  + exfalso.
    destruct app_cons_not_nil with formula (concat L1) l1' f...
- destruct l2 ; inversion Heq; subst.
  split...
- rewrite Hcut in f ; inversion f.
- exfalso.
  apply (Hgax a A' B')...
Qed.

Lemma plus_rev {P} : (forall a A B, projT2 (pgax P) a = aplus A B :: nil -> False) ->
  pcut P = false -> forall A B,
  ll P (aplus A B :: nil) -> sum (ll P (A :: nil)) (ll P (B :: nil)).
Proof with myeeasy.
intros Hgax Hcut A B pi.
remember (aplus A B :: nil) as l ; revert A B Heql ;
  induction pi using ll_nested_ind ; intros A' B' Heq ; subst ;
  try (now inversion Heq).
- apply PCperm_Type_sym in p.
  apply PCperm_Type_length_1_inv in p ; subst.
  apply IHpi...
- destruct l1 ; inversion Heq.
  + destruct lw' ; inversion H0 ; list_simpl in H0.
    symmetry in p ; apply Permutation_Type_nil in p ; subst.
    apply IHpi...
  + apply app_eq_nil in H1 ; destruct H1 ; subst.
    apply app_eq_nil in H1 ; destruct H1 ; subst.
    destruct lw' ; inversion H.
    symmetry in p ; apply Permutation_Type_nil in p ; subst.
    apply IHpi...
- change (aplus A' B' :: nil) with (nil ++ aplus A' B' :: nil) in Heq.
  apply concat_elt in Heq as ((((L1 & L2) & l1') & l2') & eqb & eqt & eqL); subst.
  destruct l1'.
  + destruct l2' ; try now inversion eqt.
    destruct (Dependent_Forall_Type_app_inv _ _ _ _ X) as ((FL1 & PL1) & (FL2 & PL2)).
    inversion PL2; subst.
    refine (X0 _ _ eq_refl).
  + exfalso.
    destruct app_cons_not_nil with formula (concat L1) l1' f...
- inversion Heq ; subst.
  left...
- inversion Heq ; subst.
  right...
- rewrite Hcut in f ; inversion f.
- exfalso.
  apply (Hgax a A' B')...
Qed.


(** *** Tensor-One Par-Bottom simplifications *)

Inductive munit_smp : formula -> formula -> Type :=
| musmp_var : forall X, munit_smp (var X) (var X)
| musmp_covar : forall X, munit_smp (covar X) (covar X)
| musmp_one : munit_smp one one
| musmp_bot : munit_smp bot bot
| musmp_tens : forall A1 A2 B1 B2, munit_smp A1 B1 -> munit_smp A2 B2 ->
                 munit_smp (tens A1 A2) (tens B1 B2)
| musmp_parr : forall A1 A2 B1 B2, munit_smp A1 B1 -> munit_smp A2 B2 ->
                 munit_smp (parr A1 A2) (parr B1 B2)
| musmp_zero : munit_smp zero zero
| musmp_top : munit_smp top top
| musmp_plus : forall A1 A2 B1 B2, munit_smp A1 B1 -> munit_smp A2 B2 ->
                 munit_smp (aplus A1 A2) (aplus B1 B2)
| musmp_with : forall A1 A2 B1 B2, munit_smp A1 B1 -> munit_smp A2 B2 ->
                 munit_smp (awith A1 A2) (awith B1 B2)
| musmp_oc : forall A B e, munit_smp A B -> munit_smp (oc e A) (oc e B)
| musmp_wn : forall A B e, munit_smp A B -> munit_smp (wn e A) (wn e B)
| musmp_to : forall A B, munit_smp A B -> munit_smp (tens one A) B
| musmp_pb : forall A B, munit_smp A B -> munit_smp (parr A bot) B.

Lemma munit_smp_id : forall A, munit_smp A A.
Proof.
induction A ; constructor ; assumption.
Qed.


Lemma munit_smp_map_wn : forall e l1 l2, Forall2_Type munit_smp (map (wn e) l1) l2 ->
  { l : _ & l2 = map (wn e) l & Forall2_Type munit_smp l1 l }.
Proof.
induction l1 ; intros l2 HF ; inversion HF ; subst.
- exists nil ; constructor.
- inversion X; subst.
  apply IHl1 in X0.
  destruct X0 as [ l'' Heq HF' ] ; subst.
  exists (B :: l'') ; constructor ; assumption.
Qed.

Lemma ceq_imp_fsteqmap : forall l1 l2, Forall2_Type munit_smp
    (map
       (fun p : Sset * formula =>
        wn (fst p) (snd p)) l1)
    (map
       (fun p : Sset * formula =>
        wn (fst p) (snd p)) l2) -> (map (fun p : Sset * formula => fst p) l1 =
map (fun p : Sset * formula => fst p) l2).
Proof.
induction l1.
- intros l2 H. list_simpl in H. induction l2. reflexivity. inversion H.
- induction l2.
  + intro H. inversion H.
  + intro H. inversion H.
  unfold map. inversion X. rewrite H7. specialize IHl1 with l2. inversion H. apply IHl1 in X3. unfold map in X3. rewrite X3. reflexivity.
Qed.

Lemma munit_smp_map_wn2 : forall l1 l2, Forall2_Type munit_smp (map (fun p => 
                         wn (fst p) (snd p)) l1) l2 -> 
                         { l : _ & l2 = (map (fun p => wn (fst p) (snd p)) l)
                         & Forall2_Type munit_smp (map (fun p => (snd p)) l1) (map (fun p => (snd p)) l) }.
Proof.
induction l1 ; intros l2 HF ; inversion HF ; subst.
- exists nil ; constructor.
- inversion X; subst.
  apply IHl1 in X0.
  destruct X0 as [ l'' Heq HF' ] ; subst.
  exists (((fst a), B) :: l'') ; constructor ; assumption.
Qed.

Lemma munit_repeat : forall l l' A B i, Forall2_Type munit_smp l l' -> munit_smp A B -> 
                              Forall2_Type munit_smp ((repeat A i) ++ l) ((repeat B i) ++ l').
Proof.
induction i.
- intros H _ ; list_simpl ; assumption.
- intros H1 H2.
  constructor ; auto.
Qed.

Lemma munit_elim {P} : (forall a, Forall_Type atomic (projT2 (pgax P) a)) ->
  forall l1, ll P l1 -> forall l2, Forall2_Type munit_smp l1 l2 -> ll P l2.
Proof with try eassumption.
intros Hgax l1 pi ; induction pi using ll_nested_ind ; intros l2' HF ;
  try now (inversion HF ; subst ;
           inversion X ; subst ;
           constructor ; apply IHpi ; try eassumption ;
           constructor ; eassumption).
- inversion HF as [ | C D lc ld Hc' HF'] ; subst.
  inversion HF' as [ | C' D' lc' ld' Hc'' HF''] ; subst.
  inversion HF'' ; subst.
  inversion Hc' ; subst.
  inversion Hc'' ; subst.
  apply ax_r.
- symmetry in p.
  eapply PCperm_Type_Forall2 in p as [la HP] ; [ | eassumption ].
  symmetry in HP.
  eapply ex_r ; [ | apply HP ].
  apply IHpi ; assumption.
- apply Forall2_Type_app_inv_l in HF as [(l'1, l'2) [HF1 HF2] Heq]; subst.
  apply Forall2_Type_app_inv_l in HF2 as [(l''1, l''2) [HF2 HF3] Heq]; subst.
  assert (HF4 := HF2).
  apply munit_smp_map_wn in HF2 as [ l''' Heq HF2 ] ; rewrite_all Heq ; clear Heq.
  symmetry in p.
  apply (Permutation_Type_map (wn e)) in p.
  eapply Permutation_Type_Forall2 in p as [la HP] ; [ | eassumption ].
  symmetry in HP.
  apply Permutation_Type_map_inv in HP ; destruct HP as [lb Heq HP] ; subst.
  symmetry in HP.
  eapply ex_wn_r ; [ | apply HP ].
  apply IHpi.
  repeat apply Forall2_Type_app...
- destruct (@concat_Forall2_Type formula) with formula L l2' munit_smp as [L' eq HF']...
  rewrite <- eq.
  apply mix_r.
  + replace (length L') with (length L)...
    apply Forall2_Type_length with (Forall2_Type munit_smp)...
  + apply forall_Forall_Type.
    intros l' Hin.
    destruct @Forall2_Type_in_r with (list formula) (list formula) L L' l'
                                     (Forall2_Type munit_smp) as (l & Hinl & Rll')...
    apply (In_Forall_Type_in _ _ _ PL) in Hinl as (pi' & Hinl).
    refine (Dependent_Forall_Type_forall_formula _ _ _ _ PL X Hinl _ Rll').
- inversion HF ; subst.
  inversion X ; inversion X0 ; subst.
  constructor.
- inversion HF ; subst.
  apply Forall2_Type_app_inv_l in X0 as [(l2', l1') [HF2 HF1] Heq]; subst.
  inversion X ; subst.
  + constructor ; [ apply IHpi1 | apply IHpi2 ] ; constructor...
  + apply (Forall2_Type_cons one one) in HF1 ; [ | constructor ].
    apply IHpi1 in HF1.
    apply (Forall2_Type_cons B y) in HF2...
    apply IHpi2 in HF2.
    assert (forall a, In_Type one (projT2 (pgax P) a) -> False) as Hgax1.
    { intros a Hone.
      eapply Forall_Type_forall in Hone; [ | apply Hgax].
      inversion Hone. }
    rewrite <- (app_nil_l _) in HF1 ; eapply (one_rev Hgax1 _ HF2) in HF1...
- inversion HF ; subst.
  inversion X ; subst.
  + constructor ; apply IHpi ; constructor ; try constructor...
  + apply (Forall2_Type_cons bot bot) in X0 ; [ | constructor ].
    apply (Forall2_Type_cons A y) in X0...
    apply IHpi in X0.
    rewrite <- (app_nil_l l') ; rewrite app_comm_cons.
    eapply bot_rev...
    intros a Hbot.
    eapply Forall_Type_forall in Hbot; [ | apply Hgax].
    inversion Hbot.
- inversion HF ; subst.
  inversion X ; subst.
  constructor ; [ apply IHpi1 | apply IHpi2 ] ; constructor...
- inversion HF ; subst.
  inversion X ; subst.
  apply munit_smp_map_wn2 in X0.
  inversion X0 ; subst.
  refine (ocg_r _ _ _ x _ _).
  + apply IHpi.
   constructor... inversion HF...
  + inversion HF. apply ceq_imp_fsteqmap in X4. rewrite <-X4. apply pleq.
- inversion HF ; subst.
  inversion X ; subst.
  apply munit_smp_map_wn2 in X0.
  inversion X0 ; subst.
  refine (ocf_r _ _ _ x _ _).
  + apply IHpi.
   constructor...
  + inversion HF. apply ceq_imp_fsteqmap in X4. rewrite <-X4. apply pleq.
- inversion HF ; subst.
  inversion X ; subst.
  inversion X0 ; subst.
  inversion X3 ; subst.
  inversion X2 ; subst.
  refine (ocu_r _ _ _ _ B1 _ _).
  + apply IHpi.
   constructor... constructor...
  + auto.
- inversion HF ; subst.
  inversion X ; subst.
  apply mpx_r with i...
  apply IHpi.
  apply munit_repeat ; auto.
- inversion HF ; subst.
  inversion X ; subst.
  apply co_r with i...
  apply IHpi.
  apply munit_repeat ; auto.
- inversion HF ; subst.
  inversion X ; subst.
  apply dg_r...
  apply IHpi.
  constructor...
  constructor...
- apply Forall2_Type_app_inv_l in HF as [(l', l'') [HF2 HF1] Heq]; subst.
  eapply cut_r ; [ assumption | apply IHpi1 | apply IHpi2 ] ;
    (apply Forall2_Type_cons ; [ apply munit_smp_id | ])...
- specialize Hgax with a.
  assert (projT2 (pgax P) a = l2') as Heq ; subst.
  { remember (projT2 (pgax P) a) as l.
    revert l2' Hgax HF ; clear.
    induction l ; intros l2 Hgax HF ; inversion HF ; subst ; f_equal.
    - inversion Hgax ; subst.
      destruct a ; inversion H0 ; inversion X ; subst ; reflexivity.
    - inversion Hgax ; subst.
      apply IHl... }
  constructor.
Qed.


(** ** Properties on axioms *)

(** Axiom expansion *)
Lemma ax_exp {P} : (forall e, is_true ( lequ P e e || leqf P e e ||
                         (leqg P e e && (sig P e (mpx_rule 1))) )) -> forall A, ll P (A :: dual A :: nil).
Proof with myeeasy.
intro ax_exp_ax.
induction A using dual_ind ; simpl.
- rewrite bidual ; ll_swap ; auto.
- ll_swap.
  apply ax_r.
- ll_swap.
  apply bot_r.
  apply one_r.
- ll_swap.
  apply parr_r.
  cons2app ; eapply ex_r ; [ | apply PCperm_Type_app_rot ].
  rewrite app_assoc.
  apply tens_r...
- ll_swap.
  apply top_r.
- eapply plus_r1 in IHA1.
  ll_swap in IHA1.
  eapply plus_r2 in IHA2.
  ll_swap in IHA2.
  ll_swap.
  apply with_r...
- change (oc e A :: wn e (dual A) :: nil)
    with (oc e A :: map (fun p => wn (fst p) (snd p)) ((e, dual A) :: nil)).
  specialize ax_exp_ax with e.
  inversion ax_exp_ax as [ax_exp_ax'].
  apply orb_true_elim in ax_exp_ax'.
  destruct ax_exp_ax'.
  + apply orb_true_elim in e0.
    destruct e0.
    * now apply ocu_r.
    * apply ocf_r; auto.
      now repeat constructor.
  + apply andb_true_iff in e0.
    destruct e0.
    apply ocg_r.
    * simpl.
      ll_swap in IHA.
      list_simpl ; ll_swap.
      apply (mpx_r _ 1)...
    * now repeat constructor.
Qed.

Lemma ax_gen_loc : forall P Q l, Bool.leb (pperm P) (pperm Q) ->
  (forall n , Bool.leb (pmix P n) (pmix Q n)) ->
  Bool.leb (pcut P) (pcut Q) ->
  (forall e r, Bool.leb (sig P e r) (sig Q e r)) ->
  (forall e e', Bool.leb (leqg P e e') (leqg Q e e')) ->
  (forall e e', Bool.leb (leqf P e e') (leqf Q e e')) ->
  (forall e e', Bool.leb (lequ P e e') (lequ Q e e'))->
  forall pi : ll P l,
  Forall_Type (fun a => ll Q (projT2 (pgax P) a)) (gax_elts pi) ->
  ll Q l.
Proof with myeeasy.
intros P Q l Hperm Hmix Hcut Hsig Hleqg Hleqf Hlequ pi.
induction pi using ll_nested_ind ; simpl ; intros Hgax ;
  try (destruct (Forall_Type_app_inv _ _ _ Hgax) as [Hgax1 Hgax2]) ;
  try (apply IHpi1 in Hgax1) ;
  try (apply IHpi2 in Hgax2) ;
  try (constructor ; intuition ; fail).
- apply IHpi in Hgax.
  eapply ex_r...
  destruct (pperm P) ; destruct (pperm Q) ; inversion Hperm ; simpl ; simpl in p...
  apply cperm_perm_Type...
- apply IHpi in Hgax.
  eapply ex_wn_r...
- apply mix_r.
  + specialize Hmix with (length L).
    rewrite eqpmix in Hmix.
    destruct (pmix Q (length L))...
  + apply forall_Forall_Type.
    intros l' Hin.
    destruct eqpmix.
    induction PL.
    * inversion Hin.
    * inversion Hin.
      -- subst.
         inversion X.
         apply inj_pair2_eq_dec in H2; 
           [ | apply List.list_eq_dec, List.list_eq_dec, eq_dt_dec ].
         assert (Pa = p) as Heq; subst.
         { apply issue12394.injection_list in H2; intuition.
           apply List.list_eq_dec, eq_dt_dec. }
         apply X0.
         apply Forall_Type_app_inv in Hgax; intuition.
      -- inversion X.
         apply inj_pair2_eq_dec in H2; [ | apply List.list_eq_dec, List.list_eq_dec, eq_dt_dec].
         assert (Pa = p /\ Fl = PL) as [-> ->].
         { apply issue12394.injection_list in H2; intuition.
           apply List.list_eq_dec, eq_dt_dec. }
         apply IHPL...
         apply Forall_Type_app_inv in Hgax; intuition.
- apply ocg_r ; [apply IHpi in Hgax|]...
  clear - pleq Hleqg ; induction l0.
  + list_simpl ; constructor.
  + list_simpl ; constructor.
    * list_simpl in pleq ; inversion pleq as [|? ? Hleqa]. 
      specialize Hleqg with e (fst a) ; rewrite Hleqa in Hleqg...
    * apply IHl0 ; inversion pleq...
- apply ocf_r ; [apply IHpi in Hgax|]...
  clear - pleq Hleqf ; induction l0.
  + list_simpl ; constructor.
  + list_simpl ; constructor.
    * list_simpl in pleq ; inversion pleq as [|? ? Hleqa]. 
      specialize Hleqf with e (fst a) ; rewrite Hleqa in Hleqf...
    * apply IHl0 ; inversion pleq...
- apply ocu_r ; [apply IHpi in Hgax|]...
  clear -pleq Hlequ.
  specialize Hlequ with e e' ; rewrite pleq in Hlequ...
- apply mpx_r with i ; [apply IHpi in Hgax|]...
  clear - Hsig p.
  specialize Hsig with e (mpx_rule i).
  rewrite p in Hsig...
- apply co_r with i ; [apply IHpi in Hgax|]...
  clear - Hsig p.
  specialize Hsig with e (co_rule i).
  rewrite p in Hsig...
- apply dg_r ; [apply IHpi in Hgax|]...
  clear - Hsig p.
  specialize Hsig with e dg_rule.
  rewrite p in Hsig...
- eapply cut_r...
  rewrite f in Hcut ; destruct (pcut Q) ; inversion Hcut ; simpl...
- inversion Hgax ; subst...
Qed.

Lemma ax_gen : forall P Q l, Bool.leb (pperm P) (pperm Q) ->
  (forall n, Bool.leb (pmix P n) (pmix Q n)) ->
  Bool.leb (pcut P) (pcut Q) ->
  (forall e r, Bool.leb (sig P e r) (sig Q e r)) ->
  (forall e e', Bool.leb (leqg P e e') (leqg Q e e')) ->
  (forall e e', Bool.leb (leqf P e e') (leqf Q e e')) ->
  (forall e e', Bool.leb (lequ P e e') (lequ Q e e'))->
  (forall a, ll Q (projT2 (pgax P) a)) ->
  ll P l -> ll Q l.
Proof.
intros P Q l Hperm Hpmix Hcut Hsig Hleqg Hleqf Hlequ Hgax pi.
apply (ax_gen_loc _ _ _ Hperm Hpmix Hcut Hsig Hleqg Hleqf Hlequ pi).
remember (gax_elts pi) as lax.
clear - Hgax ; induction lax ; intuition.
Qed.

Lemma ax_exp_frag {P} : (forall e, is_true ( lequ P e e || leqf P e e ||
                         (leqg P e e && (sig P e (mpx_rule 1))) )) -> forall l P', ll P' l ->
  le_pfrag P' (axupd_pfrag P (existT (fun x => x -> list formula) _
                                (fun a => match a with
                                          | inl x => projT2 (pgax P) x
                                          | inr x => x :: dual x :: nil
                                          end)))
    -> ll P l.
Proof with  try eassumption ; try reflexivity.
intros ax_exp_ax l P' pi Hlf.
eapply (ax_gen (axupd_pfrag P (existT (fun x => x -> list formula) _
                                (fun a => match a with
                                          | inl x => projT2 (pgax P) x
                                          | inr x => x :: dual x :: nil
                                          end))))...
- simpl ; intros a.
  destruct a.
  + apply gax_r.
  + apply ax_exp ; auto.
- eapply stronger_pfrag...
Qed.

Lemma ax_loc : forall P l (pi : ll P l),
  ll (axupd_pfrag P (existT (fun x => x -> list formula) (Fin.t (length (gax_elts pi)))
                       (fun n => projT2 (pgax P) (Vector.nth (Vector.of_list (gax_elts pi)) n)))) l.
Proof with myeasy.
intros P l pi.
refine (ax_gen_loc _ _ _ _ _ _ _ _ _ _ pi _)...
remember (gax_elts pi) as l0 ; clear.
remember l0 as l1.
enough (Forall_Type
  (fun a : projT1 (pgax P) =>
   ll
     (axupd_pfrag P
        (existT (fun x : Type => x -> list formula) (Fin.t (length l1))
           (fun n : Fin.t (length l1) => projT2 (pgax P) (Vector.nth (Vector.of_list l1) n)))) 
     (projT2 (pgax P) a)) l0).
{ subst ; assumption. }
rewrite <- app_nil_l in Heql1 ; subst.
remember nil as l ; clear ; revert l.
induction l0 ; intros l ; constructor...
- clear ; induction l.
  + rewrite app_nil_l.
    change (length (a :: l0)) with (S (length l0)).
    pose (Q := axupd_pfrag P
           (existT (fun x => x -> list formula) (Fin.t (length (a :: l0)))
                   (fun n => projT2 (pgax P) (Vector.nth (Vector.of_list (a :: l0)) n)))).
    replace (projT2 (pgax P) a) with (projT2 (pgax Q) Fin.F1) by reflexivity.
    apply gax_r.
  + eapply stronger_pfrag ; [ | apply IHl ].
    nsplit 8 ; simpl...
    intros a1 ; exists (Fin.FS a1)...
- cons2app ; rewrite app_assoc.
  apply IHl0.
Qed.

(** ** Extending sequents with a [wn] context *)

Lemma ext_wn_param P Q (Q_perm : pperm Q = true) : forall l l0,
  ll P l -> 
  (Forall (fun p => is_true(sig Q (fst p) (mpx_rule 0))) l0) ->
  (Forall (fun p => is_true(sig Q (fst p) (co_rule 0))) l0) ->
  (forall e, Forall (fun e' : Sset => is_true (leqg Q e e'))
    (map (fun p : Sset * formula => fst p) l0)) ->
  (forall e e', ((leqf P e e') = false)) ->
  (forall e e', ((lequ P e e') = false)) ->
  (forall e e', is_true (leqg P e e') -> is_true (leqg Q e e')) ->
  (forall e i, is_true (sig P e (mpx_rule i)) -> is_true (sig Q e (mpx_rule i)))->
  (forall e i, is_true (sig P e (co_rule i)) -> is_true (sig Q e (co_rule i)))->
  (forall e, is_true (sig P e dg_rule) -> is_true (sig Q e dg_rule))->
  (pcut P = true -> pcut Q = true) ->
  (forall a, ll Q (projT2 (pgax P) a ++ map (fun p => (wn (fst p)) (snd p)) l0)) ->
  (forall L, pmix P (length L) = true -> pmix Q (length L) = false ->
             forall (FL : Forall_Type (ll Q) (map (fun l => l ++ (map (fun p => (wn (fst p)) (snd p)) l0)) L)), 
                                  ll Q (concat L ++ map (fun p => (wn (fst p)) (snd p)) l0)) ->
  ll Q (l ++ map (fun p => (wn (fst p)) (snd p)) l0).
Proof with myeeasy.
intros l l0 pi Hwk Hco Hleqgall Hleqf Hlequ Hleqg Hmpx Hcoi Hdg Hpcut Hpgax Hpmix.
induction pi using ll_nested_ind ; try (now constructor).
- eapply ex_r ; [ | apply PCperm_Type_app_comm ]...
  apply wk_list_r...
  apply ax_r.
- eapply ex_r...
  apply PCperm_perm_Type in p.
  rewrite Q_perm.
  apply Permutation_Type_app_tail...
- list_simpl.
  eapply ex_wn_r...
  rewrite app_assoc in IHpi ; rewrite 2 app_assoc...
- case_eq (pmix Q (length L)); intro Q_mix.
  + apply ex_r with (map (fun p => (wn (fst p)) (snd p)) l0 ++ concat L) ; [ | PCperm_Type_solve].
    rewrite<- (app_nil_l _); apply co_list_gen_perm_r...
    rewrite app_nil_l.
    rewrite flat_map_concat_map.
    apply mix_r.
    * rewrite map_length...
    * apply forall_Forall_Type.
      intros l' Hin.
      apply in_Type_map_inv in Hin as (l1 & (eq & Hin)).
      apply (In_Forall_Type_in _ _ _ PL) in Hin as (pil1 & Hin).
      apply (Dependent_Forall_Type_forall_formula _ _ _ _ _ X) in Hin as pi.
      rewrite <- eq.
      apply ex_r with (l1 ++ map (fun p => (wn (fst p)) (snd p)) l0)...
      PCperm_Type_solve.
  + apply Hpmix...
    apply forall_Forall_Type.
    intros l' Hin.
    apply in_Type_map_inv in Hin as (l1 & (eq & Hin)).
    apply (In_Forall_Type_in _ _ _ PL) in Hin as (pil1 & Hin).
    apply (Dependent_Forall_Type_forall_formula _ _ _ _ _ X) in Hin as pi.
    rewrite <- eq...
- eapply ex_r ; [ | apply PCperm_Type_app_comm ]...
  apply wk_list_r...
  apply one_r.
- eapply ex_r ; [ | apply PCperm_Type_app_comm ]...
  apply co_list_r with 0...
  apply (ex_r _ (tens A B :: (l2 ++ map (fun p => (wn (fst p)) (snd p)) l0) ++ l1 ++ map (fun p => (wn (fst p)) (snd p)) l0)). 
  + apply tens_r... 
  + rewrite Q_perm. list_simpl. clear. induction l0. 
    * perm_Type_solve.
    * list_simpl. symmetry. rewrite ? (app_comm_cons l2). 
transitivity (wn (fst a) (snd a)
   :: (tens A B :: l2) ++ map (fun p : Sset * formula => wn (fst p) (snd p)) l0 ++
      l1 ++
      wn (fst a) (snd a)
      :: map (fun p : Sset * formula => wn (fst p) (snd p)) l0); [|
apply Permutation_Type_middle]. 
    apply Permutation_Type_cons... 
    transitivity ((wn (fst a) (snd a) :: tens A B :: l2) 
      ++ map (fun p : Sset * formula => wn (fst p) (snd p)) l0 ++
      l1 ++ 
      map (fun p : Sset * formula => wn (fst p) (snd p)) l0); [apply Permutation_Type_cons ; myeeasy ; symmetry ; assumption | perm_Type_solve]. 
- assert (((map (fun p : Sset * formula =>
            wn (fst p) (snd p)) l1) ++
            map (fun p : Sset * formula => wn (fst p) (snd p))l0) = 
         (map
            (fun p : Sset * formula =>
            wn (fst p) (snd p)) (l1++l0))).
  + clear. assert (forall l1, (map (fun p : Sset * formula => wn (fst p) (snd p)) l1) ++
map (fun p : Sset * formula => wn (fst p) (snd p)) l0 = map (fun p : Sset * formula => wn (fst p) (snd p)) (l1 ++ l0)) ;[|auto].
    induction l0 ; [intro l0 ; rewrite app_nil_r ; rewrite app_nil_r ;auto|].
    induction l2 ; [list_simpl |]... rewrite <- app_comm_cons. unfold map. unfold map in IHl2. rewrite <- IHl2. constructor.
  + rewrite <- app_comm_cons. rewrite H. apply ocg_r.
    * rewrite <- H...
    * assert ((map (fun p : Sset * formula => fst p) (l1 ++ l0)) = ((map (fun p : Sset * formula => fst p) l1) ++ (map (fun p : Sset * formula => fst p) l0))) as Heqmap ;[apply map_app| rewrite Heqmap].
      apply Forall_app.
      -- clear - Hleqg pleq ; induction l1 ; [list_simpl ; auto|].
         constructor. inversion pleq ; apply Hleqg ; auto.
         apply IHl1 ; inversion pleq...
      -- clear - Hleqgall ; induction l0 ; [list_simpl ; auto|].
         constructor ; specialize Hleqgall with e ; inversion Hleqgall...
- assert (l1=nil).
  + inversion pleq ; [induction l1 ; [auto | inversion H0]|].
    specialize Hleqf with e x ; rewrite H0 in Hleqf ; inversion Hleqf.
  + rewrite H ; list_simpl ; rewrite H in IHpi.
    apply ocg_r ; [apply IHpi | ].
    specialize Hleqgall with e ; assumption.
- specialize Hlequ with e e' ; rewrite pleq in Hlequ ; inversion Hlequ.
- apply mpx_r with i ; [|specialize Hmpx with e i ; apply Hmpx in p ; auto].
  apply (ex_r _ ((repeat A i ++ l1) ++ map (fun p : Sset * formula => wn (fst p) (snd p))
            l0))...  PCperm_Type_solve.
- apply co_r with i ; [|specialize Hcoi with e i ; apply Hcoi in p ; auto].
  apply (ex_r _ ((repeat (wn e A) (i+2) ++ l1) ++ map (fun p : Sset * formula => wn (fst p) (snd p))
            l0))...  PCperm_Type_solve.
- apply dg_r ; [|specialize Hdg with e ; apply Hdg in p ; auto].
  assumption.
- eapply ex_r ; [ | apply PCperm_Type_app_comm ]...
  apply co_list_r with 0...
  apply (ex_r _ ((l2 ++ map (fun p : Sset * formula => wn (fst p) (snd p)) l0) ++ l1 ++ map (fun p : Sset * formula => wn (fst p) (snd p)) l0)).
  + eapply cut_r...
    intuition.
  + clear - Q_perm ; induction l0 ; list_simpl ; myeeasy ; 
  rewrite Q_perm ;
  transitivity (wn (fst a) (snd a) ::
    l2 ++ map (fun p : Sset * formula => wn (fst p) (snd p)) l0 ++
      l1 ++ wn (fst a) (snd a):: map
           (fun p : Sset * formula => wn (fst p) (snd p))
           l0). symmetry. apply Permutation_Type_middle. apply Permutation_Type_cons ; myeeasy ;
  transitivity (wn (fst a) (snd a)
   :: l2 ++
   map (fun p : Sset * formula => wn (fst p) (snd p)) l0 ++
   l1 ++
    map (fun p : Sset * formula => wn (fst p) (snd p))
        l0). perm_Type_solve.  apply Permutation_Type_cons ; myeeasy ; rewrite Q_perm in IHl0 ; list_simpl in IHl0 ; myeeasy.
- apply Hpgax...
Qed.

(** By extending axioms of [P] with [map wn l0],
one can turn any proof of [l] in [P] into a proof of [l ++ map wn l0]. *)
Lemma ext_wn {P} {P_perm : pperm P = true} : forall l l0,
  ll P l ->
  (Forall (fun p => is_true(sig P (fst p) (mpx_rule 0))) l0) ->
  (Forall (fun p => is_true(sig P (fst p) (co_rule 0))) l0) ->
  (forall e, Forall (fun e' : Sset => is_true (leqg P e e'))
    (map (fun p : Sset * formula => fst p) l0)) ->
  (forall e e', ((leqf P e e') = false)) ->
  (forall e e', ((lequ P e e') = false)) ->
    ll (axupd_pfrag P ((existT (fun x => x -> list formula) _ (fun a => projT2 (pgax P) a ++ map (fun p => (wn (fst p)) (snd p)) l0))))
       (l ++ map (fun p => (wn (fst p)) (snd p)) l0).
Proof with myeeasy.
intros l l0 pi Hmpx0 Hco0 Hleqgl0 Hleqf Hlequ.
remember
  (axupd_pfrag P ((existT (fun x => x -> list formula) _ (fun a => projT2 (pgax P) a ++ map (fun p => (wn (fst p)) (snd p)) l0))))
  as Q.
eapply (ext_wn_param P Q) in pi...
- rewrite HeqQ...
- subst ;simpl...
- subst ;simpl...
- rewrite HeqQ...
- rewrite HeqQ...
  simpl. intros...
- rewrite HeqQ...
  simpl. intros...
- rewrite HeqQ...
  simpl. intros...
- rewrite HeqQ...
  simpl. intros...
- intros P_cut.
  rewrite HeqQ ; simpl...
- intros a.
  assert ({ b | projT2 (pgax P) a ++ map (fun p => (wn (fst p)) (snd p)) l0 = projT2 (pgax Q) b}) as [b Hgax]
    by (subst ; simpl ; exists a ; reflexivity).
  rewrite Hgax.
  apply gax_r.
- intros L P_mix Q_mix.
  rewrite HeqQ in Q_mix ; simpl in Q_mix.
  rewrite P_mix in Q_mix.
  inversion Q_mix.
Qed.

