(* formulas library for yalla *)

Require Import EqNat Equalities RelationClasses Lia.
Require Import funtheory List_more Bool_more.
Require Import PeanoNat Equalities.
Require Import dectype.
Require yalla_ax.


(** * Linear Logic formulas *)

(** ** Definition and main properties of formulas *)

(** A set of atoms for building formulas *)

Section Param.

Context { Sset : DecType }.

Definition Atom := yalla_ax.Atom.

(** Formulas *)
Inductive formula :=
| var : Atom -> formula
| covar : Atom -> formula
| one : formula
| bot : formula
| tens : formula -> formula -> formula
| parr : formula -> formula -> formula
| zero : formula
| top : formula
| aplus : formula -> formula -> formula
| awith : formula -> formula -> formula
| oc : Sset -> formula -> formula
| wn : Sset -> formula -> formula.



(** n-ary operators *)

Fixpoint tens_n n A :=
match n with
| 0 => one
| 1 => A
| S n => tens (tens_n n A) A
end.

Fixpoint parr_n n A :=
match n with
| 0 => bot
| 1 => A
| S n => parr A (parr_n n A)
end.

Fixpoint wn_n n e A :=
match n with
| 0 => A (* pourquoi il y avait un 0 => E => A ?*)
| S n => wn e (wn_n n e A)
end.

Lemma wn_n_wn : forall n A e, wn_n n e (wn e A) = wn_n (S n) e A.
Proof with try reflexivity.
intros n A e.
induction n...
simpl in *; rewrite IHn...
Qed.

Fixpoint oc_n n e A :=
match n with
| 0 => A
| S n => oc e (oc_n n e A)
end.

Lemma oc_n_oc : forall n A e, oc_n n e (oc e A) = oc_n (S n) e A.
Proof with try reflexivity.
intros n A e.
induction n...
simpl in *; rewrite IHn...
Qed.


(** Orthogonal / dual of a [formula] *)

(** (the dual of [tens] and [parr] is the one compatible with non-commutative systems) *)
Fixpoint dual A :=
match A with
| var x     => covar x
| covar x   => var x
| one       => bot
| bot       => one
| tens A B  => parr (dual B) (dual A)
| parr A B  => tens (dual B) (dual A)
| zero      => top
| top       => zero
| aplus A B => awith (dual A) (dual B)
| awith A B => aplus (dual A) (dual B)
| oc e A      => wn e (dual A)
| wn e A      => oc e (dual A)
end.

Lemma bidual : forall A, dual (dual A) = A.
Proof.
induction A ; simpl; (* ; fait une règle sur tous les subgoals ? *)
  try (rewrite IHA1 ; rewrite IHA2) ;
  try rewrite IHA ;
  try reflexivity.
Qed.

Lemma codual : forall A B, dual A = B <-> A = dual B.
Proof.
intros A B ; split ; intro H.
- rewrite <- bidual at 1. (*at 1. veut dire qu'on applique bidual 
sur le premier argument de l'égalité ?*)
  rewrite H; reflexivity.
- rewrite <- bidual.
  rewrite H; reflexivity.
Qed.

Lemma dual_inj : injective dual.
Proof.
intros A B H.
rewrite <- (bidual A).
rewrite <- (bidual B).
rewrite H; reflexivity.
Qed.

Lemma dual_tens_n : forall n A, dual (tens_n n A) = parr_n n (dual A).
Proof with try reflexivity.
induction n; intro A...
destruct n...
simpl in *; rewrite <- IHn...
Qed.

Lemma dual_parr_n : forall n A, dual (parr_n n A) = tens_n n (dual A).
Proof with try reflexivity.
induction n; intro A...
destruct n...
simpl in *; rewrite <- IHn...
Qed.

Lemma dual_wn_n : forall n A e, dual (wn_n n e A) = oc_n n e (dual A).
Proof with try reflexivity.
induction n; intros A e...
destruct n...
simpl in *; rewrite IHn... 
Qed.

Lemma dual_oc_n : forall n A e, dual (oc_n n e A) = wn_n n e (dual A).
Proof with try reflexivity.
induction n; intros A e...
destruct n...
simpl in *; rewrite IHn...
Qed.


Lemma dual_ind (A: formula) : forall (Pred : formula -> Type),
            (forall A, Pred A -> Pred (dual A)) ->
            (forall X, Pred (var X)) ->
            (Pred one) ->
            (forall A1 A2, Pred A1 -> Pred A2 -> Pred (tens A1 A2)) ->
            (Pred zero) ->
            (forall A1 A2, Pred A1 -> Pred A2 -> Pred (aplus A1 A2)) ->
            (forall A e, Pred A -> Pred (oc e A)) ->
            Pred A.
Proof.
induction A as [ | | | | | | | | | | | e].
- intros Pred _ Hvar _ _ _ _ _ ; auto.
- intros Pred Hdual Hvar _ _ _ _ _.
  specialize Hvar with a; apply Hdual in Hvar ; auto.
- intros Pred _ _ Hone _ _ _ _; auto.
- intros Pred Hdual _ Hone _ _ _ _.
  apply Hdual in Hone ; auto.
- intros Pred Hdual Hvar Hone Htens Hzero Haplus Hwn.
  specialize IHA1 with Pred ; apply IHA1 in Hdual as IHA1' ; auto.
  specialize IHA2 with Pred ; apply IHA2 in Hdual as IHA2' ; auto.
- intros Pred Hdual Hvar Hone Htens Hzero Haplus Hwn.
  specialize IHA1 with Pred ; apply IHA1 in Hdual as IHA1' ; auto ; apply Hdual in IHA1'.
  specialize IHA2 with Pred ; apply IHA2 in Hdual as IHA2' ; auto ; apply Hdual in IHA2'.
  specialize Htens with (dual A2) (dual A1) ; apply Hdual in Htens ; auto.
  simpl in Htens; auto ; specialize bidual with A1 as HA1 ; specialize bidual with A2 as HA2 ;
  rewrite HA1 in Htens ; rewrite HA2 in Htens ; auto.
- intros Pred _ _ _ _ Hzero _ _ ; auto.
- intros Pred Hdual _ _ _ Hzero _ _.
  apply Hdual in Hzero ; auto. 
- intros Pred Hdual Hvar Hone Htens Hzero Haplus Hwn.
  specialize IHA1 with Pred ; apply IHA1 in Hdual as IHA1' ; auto.
  specialize IHA2 with Pred ; apply IHA2 in Hdual as IHA2' ; auto.
- intros Pred Hdual Hvar Hone Htens Hzero Haplus Hwn.
  specialize IHA1 with Pred ; apply IHA1 in Hdual as IHA1' ; auto ; apply Hdual in IHA1'.
  specialize IHA2 with Pred ; apply IHA2 in Hdual as IHA2' ; auto ; apply Hdual in IHA2'.
  specialize Haplus with (dual A1) (dual A2) ; apply Hdual in Haplus ; auto.
  simpl in Haplus; auto ; specialize bidual with A1 as HA1 ; specialize bidual with A2 as HA2 ;
  rewrite HA1 in Haplus ; rewrite HA2 in Haplus ; auto.
- intros Pred Hdual Hvar Hone Htens Hzero Haplus Hwn.
  specialize IHA with Pred ; apply IHA in Hdual as IHA' ; auto.
- intros Pred Hdual Hvar Hone Htens Hzero Haplus Hwn.
  specialize IHA with Pred ; apply IHA in Hdual as IHA' ; auto ; apply Hdual in IHA'.
  specialize Hwn with (dual A) e ; apply Hdual in Hwn ; auto.
  simpl in Hwn ; auto ; specialize bidual with A as HA ; rewrite HA in Hwn ; auto.
Qed.

(** Size of a [formula] as its number of symbols *)
Fixpoint fsize A :=
match A with
| var X     => 1
| covar X   => 1
| one       => 1
| bot       => 1
| tens A B  => S (fsize A + fsize B)
| parr A B  => S (fsize A + fsize B)
| zero      => 1
| top       => 1
| aplus A B => S (fsize A + fsize B)
| awith A B => S (fsize A + fsize B)
| oc Sset A      => S (fsize A)
| wn Sset A      => S (fsize A)
end.

Lemma fsize_pos : forall A, 0 < fsize A.
Proof.
induction A; simpl; lia.
Qed.

Lemma fsize_dual : forall A, fsize (dual A) = fsize A.
Proof.
induction A ; simpl ;
  try (rewrite IHA1 ; rewrite IHA2) ;
  try rewrite IHA ;
  try reflexivity ;
  try lia.
Qed.

Lemma fsize_wn_n : forall n e A, fsize (wn_n n e A) = n + fsize A.
Proof with try reflexivity.
induction n; intros e A; simpl...
rewrite -> IHn...
Qed.

Lemma fsize_oc_n : forall n e A, fsize (oc_n n e A) = n + fsize A.
Proof with try reflexivity.
induction n; intros e A; simpl...
rewrite -> IHn...
Qed.

Ltac fsize_auto :=
  simpl ;
  repeat rewrite fsize_dual ;
  simpl ;
  match goal with
  | H: fsize _ < _ |- _ => simpl in H 
  | H: fsize _ <= _ |- _ => simpl in H
  | H: fsize _ = _ |- _ => simpl in H
  end ;
  lia.

(** Atomic [formula] *)
Inductive atomic_Prop : formula -> Prop :=
| atomic_Prop_var : forall x, atomic_Prop (var x)
| atomic_Prop_covar : forall x, atomic_Prop (covar x).

Inductive atomic : formula -> Type :=
| atomic_var : forall x, atomic (var x)
| atomic_covar : forall x, atomic (covar x).

Lemma atomic_Prop_atomic : forall A, atomic_Prop A -> atomic A. (* atomic A est un type, donc
on veut savoir si atomic A est habitée ? *)
Proof.
induction A; intros Hat;
  try (exfalso; inversion Hat; fail);
  constructor.
Qed.


(** ** Sub-formulas *)

(** First argument is a sub-formula of the second: *)
Inductive subform : formula -> formula -> Prop :=
| sub_id : forall A, subform A A
| sub_tens_l : forall A B C, subform A B -> subform A (tens B C)
| sub_tens_r : forall A B C, subform A B -> subform A (tens C B)
| sub_parr_l : forall A B C, subform A B -> subform A (parr B C)
| sub_parr_r : forall A B C, subform A B -> subform A (parr C B)
| sub_plus_l : forall A B C, subform A B -> subform A (aplus B C)
| sub_plus_r : forall A B C, subform A B -> subform A (aplus C B)
| sub_with_l : forall A B C, subform A B -> subform A (awith B C)
| sub_with_r : forall A B C, subform A B -> subform A (awith C B)
| sub_oc : forall A B e, subform A B -> subform A (oc e B)
| sub_wn : forall A B e, subform A B -> subform A (wn e B).

Lemma sub_trans : forall A B C, subform A B -> subform B C -> subform A C.
Proof with try assumption.
intros A B C Hl Hr ; revert A Hl ; induction Hr ; intros A' Hl ;
  try (constructor ; apply IHHr)...
Qed.

Instance sub_po : PreOrder subform.
Proof.
split.
- intros l.
  apply sub_id.
- intros l1 l2 l3.
  apply sub_trans.
Qed.

(** Each element of the first list is a sub-formula of some element of the second. *)
Definition subform_list l1 l2 := Forall (fun A => Exists (subform A) l2) l1.

Lemma sub_id_list : forall l l0, subform_list l (l0 ++ l).
Proof.
induction l as [|a] ; intros l0 ; constructor.
- induction l0.
  + constructor.
    apply sub_id.
  + apply Exists_cons_tl ; assumption.
- replace (l0 ++ a :: l) with ((l0 ++ a :: nil) ++ l).
  + apply IHl.
  + rewrite <- app_assoc ; reflexivity.
Qed.

Lemma sub_trans_list : forall l1 l2 l3,
  subform_list l1 l2 -> subform_list l2 l3 -> subform_list l1 l3.
Proof with try eassumption.
induction l1 as [|? ? IHlist] ; intros l2 l3 Hl Hr ; constructor.
- inversion Hl; subst.
  revert Hr H1 ; clear ; induction l2 as [|? ? IHlist2] ; intros Hr Hl; inversion Hl as [? ? Hsub|] ; subst.
  + inversion Hr as [|? ? Hexist Hforall] ; subst.
    inversion Hexist ; subst.
    * apply Exists_cons_hd.
      etransitivity...
    * apply Exists_cons_tl.
      revert H ; clear - Hsub ; induction l ; intro H ; inversion H ; subst.
      apply Exists_cons_hd.
      etransitivity...
      apply Exists_cons_tl.
      apply IHl...
  + inversion Hr ; subst.
    apply IHlist2...
- inversion Hl ; subst.
  eapply IHlist...
Qed.

Instance sub_list_po : PreOrder subform_list.
Proof.
split.
- intros l.
  rewrite <- app_nil_l.
  apply sub_id_list.
- intros l1 l2 l3.
  apply sub_trans_list.
Qed.

(* Unused
Require Import genperm_Type.

Lemma sub_perm_list :
  forall b l l1 l2, subform_list l l1 ->
    PCperm_Type b l1 l2 -> subform_list l l2.
Proof with try eassumption.
intros b l l1 l2 H1 HP ; revert H1 ; induction l ; intro H1.
- constructor.
- inversion H1 ; subst.
  constructor.
  + eapply PCperm_Type_Exists...
  + apply IHl...
Qed.
*)


(** ** Equality in [bool] *)

Fixpoint eqb_form A B :=
match A, B with
| var X, var Y => yalla_ax.ateq X Y
| covar X, covar Y => yalla_ax.ateq X Y
| one, one => true
| bot, bot => true
| tens A1 A2, tens B1 B2 => eqb_form A1 B1 && eqb_form A2 B2
| parr A1 A2, parr B1 B2 => eqb_form A1 B1 && eqb_form A2 B2
| top, top => true
| zero, zero => true
| awith A1 A2, awith B1 B2 => eqb_form A1 B1 && eqb_form A2 B2
| aplus A1 A2, aplus B1 B2 => eqb_form A1 B1 && eqb_form A2 B2
| oc e0 A1, oc e1 B1 => eqb e0 e1 && eqb_form A1 B1
| wn e0 A1, wn e1 B1 => eqb e0 e1 && eqb_form A1 B1
| _, _ => false
end.


Ltac induction_formula A A1 A2 X e:=
  induction A as [ X
                 | X
                 |
                 |
                 | A1 IHl A2 IHr
                 | A1 IHl A2 IHr
                 |
                 |
                 | A1 IHl A2 IHr
                 | A1 IHl A2 IHr
                 | e A IHform
                 | e A IHform].

Lemma eqb_eq_form : forall A B, eqb_form A B = true <-> A = B.
Proof with reflexivity.
induction_formula A Al Ar X e ; destruct B ; (split ; [ intros Heqb | intros Heq ]) ;
  try inversion Heqb as [Hax]; try (now inversion Heq); try reflexivity;
  try injection Heq; try intros Heq1; try intros Heq2.
- apply yalla_ax.ateq_eq in Hax ; subst...
- subst ; simpl.
  apply yalla_ax.ateq_eq...
- apply yalla_ax.ateq_eq in Hax ; subst...
- subst ; simpl.
  apply yalla_ax.ateq_eq...
- apply andb_true_iff in Hax.
  destruct Hax as [Hax1 Hax2].
  apply IHl in Hax1 ; apply IHr in Hax2 ; subst...
- subst ; simpl ; apply andb_true_iff.
  split ; [ apply IHl | apply IHr ]...
- apply andb_true_iff in Hax.
  destruct Hax as [Hax1 Hax2].
  apply IHl in Hax1 ; apply IHr in Hax2 ; subst...
- subst ; simpl ; apply andb_true_iff.
  split ; [ apply IHl | apply IHr ]...
- apply andb_true_iff in Hax.
  destruct Hax as [Hax1 Hax2].
  apply IHl in Hax1 ; apply IHr in Hax2 ; subst...
- subst ; simpl ; apply andb_true_iff.
  split ; [ apply IHl | apply IHr ]...
- apply andb_true_iff in Hax.
  destruct Hax as [Hax1 Hax2].
  apply IHl in Hax1 ; apply IHr in Hax2 ; subst...
- subst ; simpl ; apply andb_true_iff.
  split ; [ apply IHl | apply IHr ]...
- apply andb_true_iff in Hax. destruct Hax as (Hax' & Hax).
  apply eqb_eq in Hax'.
  apply IHform in Hax ; subst...
- simpl. apply andb_true_iff.
  split;[now apply eqb_eq|].
  rewrite <- Heq1. apply IHform. reflexivity.
- apply andb_true_iff in Hax. destruct Hax as (Hax' & Hax).
  apply eqb_eq in Hax'.
  apply IHform in Hax ; subst...
- simpl. apply andb_true_iff. split.
  + now apply eqb_eq.
  + rewrite <- Heq1. apply IHform. reflexivity.
Qed.

(* Unused
Fixpoint eqb_formlist l1 l2 :=
match l1, l2 with
| nil, nil => true
| cons A t1, cons B t2 => eqb_form A B && eqb_formlist t1 t2
| _, _ => false
end.

Lemma eqb_eq_formlist : forall l1 l2, eqb_formlist l1 l2 = true <-> l1 = l2.
Proof with reflexivity.
induction l1 ; destruct l2 ; (split ; [ intros Heqb | intros Heq ]) ;
  try inversion Heqb ; try inversion Heq ; try reflexivity.
- apply andb_true_iff in H0.
  destruct H0 as [H1 H2].
  apply eqb_eq_form in H1 ; apply IHl1 in H2 ; subst...
- subst ; simpl ; apply andb_true_iff.
  split ; [ apply eqb_eq_form | apply IHl1 ]...
Qed.
*)

(* Unused
(** * In with [bool] output for formula list *)
Fixpoint inb_form A l :=
match l with
| nil => false
| cons hd tl => eqb_form A hd || inb_form A tl
end.

Lemma inb_in_form : forall A l, is_true (inb_form A l) <-> In A l.
Proof with assumption.
induction l ; (split ; [ intros Heqb | intros Heq ]).
- inversion Heqb.
- inversion Heq.
- inversion Heqb ; subst.
  apply orb_true_iff in H0.
  destruct H0.
  + constructor.
    symmetry ; apply eqb_eq_form...
  + apply in_cons.
    apply IHl...
- inversion Heq ; subst.
  + simpl ; apply orb_true_iff ; left.
    apply eqb_eq_form ; reflexivity.
  + simpl ; apply orb_true_iff ; right.
    apply IHl...
Qed.
*)


(** ** Sub-formulas in [bool] *)

(** First argument is a sub-formula of the second: *)
Fixpoint subformb A B :=
eqb_form A B ||
match B with
| tens B1 B2 => subformb A B1 || subformb A B2
| parr B1 B2 => subformb A B1 || subformb A B2
| awith B1 B2 => subformb A B1 || subformb A B2
| aplus B1 B2 => subformb A B1 || subformb A B2
| oc e B1 => subformb A B1
| wn e B1 => subformb A B1
| _ => false
end.

Lemma subb_sub : forall A B, is_true (subformb A B) <-> subform A B.
Proof with try assumption; try reflexivity.
intros A B ; split ; intros Hyp ; induction_formula B Bl Br X e;
  try (now (inversion Hyp ; constructor)) ;
  try (now (destruct A ; simpl in Hyp ; inversion Hyp));
  try (simpl in Hyp;
       apply orb_true_elim in Hyp ; destruct Hyp as [ Hyp | Hyp ] ;
       [ | apply orb_true_elim in Hyp ; destruct Hyp as [ Hyp | Hyp ] ]; 
       (try (apply eqb_eq_form in Hyp ; subst)) ; now constructor; auto).
- destruct A ; simpl in Hyp ; try (now inversion Hyp).
  rewrite orb_false_r in Hyp.
  apply yalla_ax.ateq_eq in Hyp ; subst ; constructor.
- destruct A ; simpl in Hyp ; try (now inversion Hyp).
  rewrite orb_false_r in Hyp.
  apply yalla_ax.ateq_eq in Hyp ; subst ; constructor.
- simpl in Hyp.
  apply orb_true_elim in Hyp ; destruct Hyp as [ Hyp | Hyp ].
  + apply eqb_eq_form in Hyp ; subst ; constructor.
  + now constructor; auto.
- simpl in Hyp.
  apply orb_true_elim in Hyp ; destruct Hyp as [ Hyp | Hyp ].
  + apply eqb_eq_form in Hyp ; subst ; constructor.
  + now constructor; auto.
- inversion Hyp ; subst.
  simpl ; rewrite (proj2 (yalla_ax.ateq_eq _ _) eq_refl).
  constructor.
- inversion Hyp ; subst.
  simpl ; rewrite (proj2 (yalla_ax.ateq_eq _ _) eq_refl).
  constructor.
- inversion_clear Hyp as [  | ? ? ? Hyp' | ? ? ? Hyp' | | | |  | |   |  |  ].
  + unfold subformb.
    replace (eqb_form (tens Bl Br) (tens Bl Br)) with true
      by (symmetry ; apply eqb_eq_form; reflexivity)...
  + apply IHl in Hyp'.
    simpl ; rewrite Hyp' ; simpl.
    rewrite orb_true_r...
  + apply IHr in Hyp'.
    simpl ; rewrite Hyp' ; simpl.
    rewrite 2 orb_true_r...
- inversion_clear Hyp as [  | | | ? ? ? Hyp' | ? ? ? Hyp' | |  | |   |  |  ].
  + unfold subformb.
    replace (eqb_form (parr Bl Br) (parr Bl Br)) with true
      by (symmetry ; apply eqb_eq_form ; reflexivity)...
  + apply IHl in Hyp'.
    simpl ; rewrite Hyp' ; simpl.
    rewrite orb_true_r...
  + apply IHr in Hyp'.
    simpl ; rewrite Hyp' ; simpl.
    rewrite 2 orb_true_r...
- inversion_clear Hyp as [  | | | | | ? ? ? Hyp' | ? ? ? Hyp' | |   |  |  ].
  + unfold subformb.
    replace (eqb_form (aplus Bl Br) (aplus Bl Br)) with true
      by (symmetry ; apply eqb_eq_form; reflexivity)...
  + apply IHl in Hyp'.
    simpl ; rewrite Hyp' ; simpl.
    rewrite orb_true_r...
  + apply IHr in Hyp'.
    simpl ; rewrite Hyp' ; simpl.
    rewrite 2 orb_true_r...
- inversion_clear Hyp as [  | | | | | | | ? ? ? Hyp' | ? ? ? Hyp' | |  ].
  + unfold subformb.
    replace (eqb_form (awith Bl Br) (awith Bl Br)) with true
      by (symmetry ; apply eqb_eq_form ; reflexivity)...
  + apply IHl in Hyp'.
    simpl ; rewrite Hyp' ; simpl.
    rewrite orb_true_r...
  + apply IHr in Hyp'.
    simpl ; rewrite Hyp' ; simpl.
    rewrite 2 orb_true_r...
- inversion_clear Hyp as [  | | | | | | | | | ? ? ? Hyp' | ].
  + unfold subformb.
    replace (eqb_form (oc e B) (oc e B)) with true
      by (symmetry ; apply eqb_eq_form ; reflexivity)...
  + apply IHform in Hyp'.
    simpl ; rewrite Hyp' ; simpl.
    rewrite orb_true_r...
- inversion_clear Hyp as [  | | | | | | | | | | ? ? ? Hyp' ].
  + unfold subformb.
    replace (eqb_form (wn e B) (wn e B)) with true
      by (symmetry ; apply eqb_eq_form ; reflexivity)...
  + apply IHform in Hyp'.
    simpl ; rewrite Hyp' ; simpl.
    rewrite orb_true_r...
Qed.

Lemma subb_trans : forall A B C,
  is_true (subformb A B) -> is_true (subformb B C) -> is_true (subformb A C).
Proof.
intros A B C Hl Hr.
apply subb_sub in Hl.
apply subb_sub in Hr.
apply subb_sub.
etransitivity ; eassumption.
Qed.

(** Each element of the first list is a sub-formula of some element of the second. *)
Definition subformb_list l1 l2 := forallb (fun A => existsb (subformb A) l2) l1.

Lemma subb_sub_list : forall l1 l2, is_true (subformb_list l1 l2) <-> subform_list l1 l2.
Proof with try assumption.
intros l1 l2 ; split ; intros Hyp ; induction l1 ; try (now (inversion Hyp ; constructor)).
- unfold subformb_list in Hyp.
  apply forallb_Forall in Hyp.
  inversion Hyp as [|? ? Hyp'] ; subst.
  apply existsb_Exists in Hyp'.
  constructor.
  + clear - Hyp' ; induction l2 ; inversion Hyp' ; subst.
    * constructor.
      apply subb_sub...
    * apply Exists_cons_tl.
      apply IHl2...
  + apply IHl1.
    apply forallb_Forall...
- inversion Hyp as [|? ? Hyp']; subst.
  unfold subformb_list ; simpl.
  apply andb_true_iff ; split.
  + apply existsb_Exists.
    clear - Hyp' ; induction l2 ; inversion Hyp' ; subst.
    * constructor.
      apply subb_sub...
    * apply Exists_cons_tl.
      apply IHl2...
  + apply IHl1...
Qed.

Lemma subb_id_list : forall l l0, is_true (subformb_list l (l0 ++ l)).
Proof.
intros l l0.
apply subb_sub_list.
apply sub_id_list.
Qed.

Lemma subb_trans_list : forall l1 l2 l3,
  is_true (subformb_list l1 l2) -> is_true (subformb_list l2 l3) -> is_true (subformb_list l1 l3).
Proof.
intros l1 l2 l3 Hl Hr.
apply subb_sub_list in Hl.
apply subb_sub_list in Hr.
apply subb_sub_list.
etransitivity ; eassumption.
Qed.

End Param.


(****************************************************************************************

Require Import PeanoNat CMorphisms Lia.
Require Import Bool_more List_more List_Type_more Dependent_Forall_Type
               Permutation_Type_more CyclicPerm_Type Permutation_Type_solve
               CPermutation_Type_solve genperm_Type.
Require Export basic_misc.

(** ** Fragments for proofs *)

Definition NoAxioms := (existT (fun x => x -> list formula) _ Empty_fun).

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
Record pfrag := mk_pfrag {
  pcut : bool ;
  pgax : { ptypgax : Type & ptypgax -> list formula } ;
  pmix : nat -> bool ;
  pperm : bool }.

(** Order relation on proof fragments: [P] is more restrictive than [Q]. *)
Definition le_pfrag P Q :=
  prod
    (Bool.leb (pcut P) (pcut Q))
  (prod
    (forall a, { b | projT2 (pgax P) a = projT2 (pgax Q) b })
  (prod
    (forall n, Bool.leb (pmix P n) (pmix Q n))
    (Bool.leb (pperm P) (pperm Q)))).

Lemma le_pfrag_trans : forall P Q R,
  le_pfrag P Q -> le_pfrag Q R -> le_pfrag P R.
Proof with myeeasy; try assumption.
  intros P Q R H1 H2.
  unfold le_pfrag in H1.
  destruct H1 as (Hc1 & Ha1 & Hm1 & Hp1).
  unfold le_pfrag in H2.
  destruct H2 as (Hc2 & Ha2 & Hm2 & Hp2).
  nsplit 4 ; try (eapply leb_trans ; myeeasy).
  - intros a.
    destruct (Ha1 a) as [b Heq].
    destruct (Ha2 b) as [c Heq2].
    exists c ; etransitivity...
  - intros n.
    apply leb_trans with (pmix Q n); [ apply Hm1 | apply Hm2 ].
Qed.

Instance le_pfrag_po : PreOrder le_pfrag.
Proof.
split.
- nsplit 4 ; try reflexivity.
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
Definition cutupd_pfrag P b := mk_pfrag b (pgax P) (pmix P) (pperm P).

Lemma cutupd_pfrag_true : forall P, le_pfrag P (cutupd_pfrag P true).
Proof.
intros P.
nsplit 4 ; try reflexivity.
- apply leb_true.
- intros a ; exists a ; reflexivity.
Qed.

(** Same proof fragment as [P] but with value [G] for [pgax]. *)
Definition axupd_pfrag P G := mk_pfrag (pcut P) G (pmix P) (pperm P).

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
Definition pmixupd_pfrag P pmix := mk_pfrag (pcut P) (pgax P) pmix (pperm P).

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
| oc_r : forall A l e, ll P (A :: map (wn e) l) -> ll P (oc A :: map (wn e) l)
| mpx_r : forall A l, ll P (A :: l) -> ll P (wn A :: l)
| wk_r : forall A l, ll P l -> ll P (wn A :: l)
| co_r : forall A l, ll P (wn A :: wn A :: l) -> ll P (wn A :: l)
| cut_r {f : pcut P = true} : forall A l1 l2,
    ll P (dual A :: l1) -> ll P (A :: l2) -> ll P (l2 ++ l1)
| gax_r : forall a, ll P (projT2 (pgax P) a).
*)