From Coq Require Import List Lia.
(*
From OLlibs Require Import funtheory.
*)
From OLlibs Require Import dectype Permutation_Type.
Require Import ll_def microll.

Fixpoint ll2ll A :=
match A with
| var x     => @formulas.var nat_dectype unit_dectype x
| covar x   => @formulas.covar nat_dectype unit_dectype x
| tens A B  => formulas.tens (ll2ll A) (ll2ll B)
| parr A B  => formulas.parr (ll2ll A) (ll2ll B)
| one       => formulas.one
| bot       => formulas.bot
| awith A B => formulas.awith (ll2ll A) (ll2ll B)
| aplus A B => formulas.aplus (ll2ll A) (ll2ll B)
| top       => formulas.top
| zero      => formulas.zero
| oc A      => @formulas.oc _ unit_dectype tt (ll2ll A)
| wn A      => @formulas.wn _ unit_dectype tt (ll2ll A)
end.

(*
Lemma ll2ll_inj : injective ll2ll.
Proof.
intros A.
induction A ; intros B Heq ;
  destruct B ; inversion Heq ;
  try apply IHA in H0 ;
  try apply IHA1 in H0 ;
  try apply IHA2 in H1 ; subst ;
  reflexivity.
Qed.
*)

Lemma ll2ll_map_wn : forall l,
  map ll2ll (map wn l) =
  map (fun p => @formulas.wn _ unit_dectype (fst p) (snd p)) (map (fun x => (tt, x)) (map ll2ll l)).
Proof.
induction l; [ reflexivity | ].
now simpl ; rewrite IHl.
Qed.

(* TODO
Lemma ll2ll_map_wn_inv : forall l1 l2,
  map formulas.wn l1 = map ll2ll l2 ->
    { l2' | l2 = map wn l2' /\ l1 = map ll2ll l2' }.
Proof with try assumption ; try reflexivity.
induction l1 ; intros l2 Heq ;
  destruct l2 ; inversion Heq...
- exists nil ; split...
- apply IHl1 in H1.
  destruct f ; inversion H0 ; subst.
  destruct H1 as (l2' & Heq1 & H1) ; subst.
  exists (f :: l2') ; split...
Qed.
*)

Lemma transp_perm {A} : forall n (l : list A),
  Permutation_Type l (transp n l).
Proof with try reflexivity.
induction n; intros l; simpl; destruct l...
- destruct l...
  apply Permutation_Type_swap.
- apply Permutation_Type_cons...
  apply IHn.
Qed.

Lemma transp_map {A B} (f : A -> B) : forall n l,
  transp n (map f l) = map f (transp n l).
Proof with try reflexivity.
induction n; destruct l...
- destruct l; simpl...
- simpl; f_equal.
  apply IHn.
Qed.

Definition pfrag_ll := @mk_pfrag nat_dectype unit_dectype false (NoAxioms unit_dectype) pmix_none true
(*                               atoms      exp. sign.    cut   axioms                  mix       perm  *)
                                 (fun _ _ => true) (fun _ _ => true) (fun _ _ => false) (fun _ _ => false).
(*                               exponential constraints
                                 wn-rules          Girard prom.      funct. prom.       unary funct. prom. *)

Theorem ll2ll_proof : forall l, ll l -> ll_def.ll _ pfrag_ll (map ll2ll l).
Proof.
intros l pi; induction pi ; simpl; try (now constructor).
- apply (ex_r _ _ (map ll2ll l)); try assumption.
  simpl; rewrite <- transp_map.
  apply transp_perm.
- rewrite map_app.
  apply (ex_r _ _ (formulas.tens (ll2ll A) (ll2ll B) :: map ll2ll l2 ++ map ll2ll l1)).
  + now constructor.
  + simpl; apply Permutation_Type_cons; try reflexivity.
    apply Permutation_Type_app_comm.
- rewrite ll2ll_map_wn.
  apply ll_def.ocg_r.
  + rewrite <- ll2ll_map_wn; assumption.
  + assert (forall A (l : list A), Forall (fun _ => is_true true) l) as Htrue
      by (clear; intros A l; induction l as [|h tl]; auto).
    apply Htrue.
- now apply (ll_def.mpx_r _ _ 1).
- now apply (ll_def.mpx_r _ _ 0).
- now apply (ll_def.co_r _ _ 0).
Qed.
