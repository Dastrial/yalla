(* Unit-free MLL following Yalla schemas *)

From Coq Require Import Bool Wf_nat Lia.
From OLlibs Require Import dectype funtheory List_more List_Type Permutation_Type_more.

Import EqNotations.

Set Implicit Arguments.

(** * MLL formulas *)

Section Atoms.

(** A set of atoms for building formulas *)
Context { atom : DecType }.

Context { Sset : DecType }.

(** Formulas *)
Inductive formula :=
| var : atom -> formula
| covar : atom -> formula
| tens : formula -> formula -> formula
| parr : formula -> formula -> formula
| oc : Sset -> formula -> formula
| wn : Sset -> formula -> formula.

Notation "'ν' X" := (var X) (at level 12).
Notation "'κ' X" := (covar X) (at level 12).
Infix "⊗" := tens (at level 40).
Infix "⅋" := parr (at level 40).

(** ** Equality of [formula] in [bool] *)
Fixpoint eqb_form A B :=
match A, B with
| var X, var Y => eqb X Y
| covar X, covar Y => eqb X Y
| tens A1 A2, tens B1 B2 => eqb_form A1 B1 && eqb_form A2 B2
| parr A1 A2, parr B1 B2 => eqb_form A1 B1 && eqb_form A2 B2
| wn e1 A1, wn e2 A2 => eqb e1 e2 && eqb_form A1 A2
| oc e1 A1, oc e2 A2 => eqb e1 e2 && eqb_form A1 A2
| _, _ => false
end.

Lemma eqb_eq_form : forall A B, eqb_form A B = true <-> A = B.
Proof.
induction A; destruct B; (split; intros Heq); inversion Heq; auto.
- now apply eqb_eq in H0; subst.
- now subst; cbn; apply eqb_eq.
- now apply eqb_eq in H0; subst.
- now subst; cbn; apply eqb_eq.
- apply andb_true_iff in H0.
  destruct H0 as [H1 H2].
  now apply IHA1 in H1; apply IHA2 in H2; subst.
- now subst; cbn; apply andb_true_iff; split; [ apply IHA1 | apply IHA2 ].
- apply andb_true_iff in H0 as [H1 H2].
  now apply IHA1 in H1; apply IHA2 in H2; subst.
- now subst; cbn; apply andb_true_iff; split; [ apply IHA1 | apply IHA2 ].
- apply andb_true_iff in H0 ; destruct H0 as [Heqsign Heqform].
  apply IHA in Heqform ; apply eqb_eq in Heqsign ; subst ; reflexivity.
- subst ; cbn ; apply andb_true_iff ; split ; [apply eqb_eq ; auto | 
      destruct IHA with B as [_ IHAusefull] ; apply IHAusefull ; reflexivity].
- apply andb_true_iff in H0 ; destruct H0 as [Heqsign Heqform].
  apply IHA in Heqform ; apply eqb_eq in Heqsign ; subst ; reflexivity.
- subst ; cbn ; apply andb_true_iff ; split ; [apply eqb_eq ; auto | 
      destruct IHA with B as [_ IHAusefull] ; apply IHAusefull ; reflexivity].
Qed.

Definition formulas_dectype := {|
  car := formula;
  eqb := eqb_form;
  eqb_eq := eqb_eq_form |}.

(** ** Dual of a [formula] *)
Fixpoint dual A :=
match A with
| var x     => covar x
| covar x   => var x
| tens A B  => parr (dual B) (dual A)
| parr A B  => tens (dual B) (dual A)
| wn e A => oc e (dual A)
| oc e A => wn e (dual A)
end.
Notation "A ^" := (dual A) (at level 12, format "A ^").

Lemma bidual A : dual (dual A) = A.
Proof. now induction A; cbn; rewrite ? IHA1, ? IHA2, ? IHA. Qed.

Lemma codual A B : dual A = B <-> A = dual B.
Proof. now split; intro H; rewrite <- (bidual A), <- (bidual B), H, ? bidual. Qed.

Lemma dual_inj : injective dual.
Proof. now intros A B H; rewrite <- (bidual A), <- (bidual B), H. Qed.

(** ** Size of a [formula] as its number of symbols *)
Fixpoint fsize A :=
match A with
| var X    => 1
| covar X  => 1
| tens A B => S (fsize A + fsize B)
| parr A B => S (fsize A + fsize B)
| wn e A => S (fsize A)
| oc e A => S (fsize A)
end.

Lemma fsize_pos A : 0 < fsize A.
Proof. induction A; cbn; lia. Qed.

Lemma fsize_dual A : fsize (dual A) = fsize A.
Proof. induction A; cbn; rewrite ? IHA1, ? IHA2; lia. Qed.


Record pfrag := mk_pfrag {
  co_rule : list Sset -> Sset -> bool ;
  dg_rule : Sset -> Sset -> Sset -> bool}.

Notation mapwn := (map (fun p => wn (fst p) (snd p))).
Notation mapoc := (map (fun p => oc (fst p) (snd p))).

(** * MLL Proofs *)
Inductive ll P : list formula -> Type :=
| ax_r : forall X, ll P (covar X :: var X :: nil)
| ex_r : forall l1 l2, ll P l1 -> Permutation_Type l1 l2 -> ll P l2
| tens_r : forall A B l1 l2, ll P (A :: l1) -> ll P (B :: l2) -> ll P (tens A B :: l2 ++ l1)
| parr_r : forall A B l, ll P (A :: B :: l) -> ll P (parr A B :: l)
| oc_r : forall e A l, ll P (A :: l) ->
          ll P (oc e A :: (map (fun p => wn e p) l))
| de_r : forall e A l, ll P (A::l) -> ll P ((wn e A) :: l)
| co_r : forall e A l1 l2, ll P ((map (fun p=> wn p A) l1) ++ l2) ->
        is_true (co_rule P l1 e) -> ll P ((wn e A) :: nil ++ l2)
| dg_r : forall e e1 e2 A l, ll P ((wn e1 (wn e2 A)) :: nil ++ l) -> 
        is_true (dg_rule P e1 e2 e) -> ll P (wn e A :: nil ++ l).

Notation "⊢ l" := (ll l) (at level 70).

(** ** Size of proofs *)
Fixpoint psize {P l} (pi : ll P l) :=
match pi with
| ax_r _ _ => 1
| ex_r pi0 _ => S (psize pi0)
| tens_r pi1 pi2 => S (psize pi1 + psize pi2)
| parr_r pi0 => S (psize pi0)
| oc_r _ pi0 => S (psize pi0)
| de_r _ pi0 => S (psize pi0)
| co_r _ _ _ _ pi0 _ => S (psize pi0)
| dg_r _ pi0 _ => S (psize pi0)
end.

Lemma psize_pos l P (pi : ll P l) : 0 < psize pi.
Proof. destruct pi; cbn; lia. Qed.

Lemma psize_rew P l l' (pi : ll P l) (Heq : l = l') : psize (rew Heq in pi) = psize pi.
Proof. now subst. Qed.


(** * Cut Elimination *)

Ltac destruct_eqrefl H :=
list_simpl in H;
match goal with
| H : ?x = ?x |- _ => assert (H = eq_refl) as ->
                        by apply (Eqdep_dec.UIP_dec (@eq_dt_dec (list_dectype formulas_dectype)));
                      cbn
end.

Locate "rew".

(** Symmetric induction principle *)
Lemma sym_induction_ll (P : forall [A B l1 l2 l3 l4 Q], ll Q (l1 ++ A :: l2) -> ll Q (l3 ++ B :: l4)
                          -> Type) :
  (forall A B l1 l2 l3 l4 Q (pi1 : ll Q (l1 ++ A :: l2)) (pi2 : ll Q (l3 ++ B :: l4)),
     P pi2 pi1 -> P pi1 pi2) ->
  (forall X B l3 l4 Q (pi2 : ll Q (l3 ++ B :: l4)),
     P (ax_r Q X : ll Q (nil ++ covar X :: var X :: nil)) pi2) ->
  (forall X B l3 l4 Q (pi2 : ll Q (l3 ++ B :: l4)),
     P (ax_r Q X : ll Q ((covar X :: nil) ++ var X :: nil)) pi2) ->
  (forall A B l1 l2 l3 l4 l' Q (pi1 : ll Q l') (pi2 : ll Q (l3 ++ B :: l4))
     (HP : Permutation_Type l' (l1 ++ A :: l2)),
     P (rew (rew (surjective_pairing (proj1_sig (Permutation_Type_vs_elt_inv _ _ _ HP)))
              in proj2_sig (Permutation_Type_vs_elt_inv _ _ _ HP)) in pi1) pi2 ->
     P (ex_r pi1 HP) pi2) ->
  (forall A B C D l0 l1 l2 l3 l4 Q (pi0 : ll Q (C :: l0))
     (pi1 : ll Q (D :: l1 ++ A :: l2)) (pi2 : ll Q (l3 ++ B :: l4)),
     P (pi1 : ll Q ((D :: l1) ++ A :: l2)) pi2 ->
     P (rew <- (app_assoc (tens C D :: l1) (A :: l2) _) in tens_r pi0 pi1) pi2) ->
  (forall A B C D l0 l1 l2 l3 l4 Q (pi0 : ll Q (D :: l0))
     (pi1 : ll Q (C :: l1 ++ A :: l2)) (pi2 : ll Q (l3 ++ B :: l4)),
     P (pi1 : ll Q ((C :: l1) ++ A :: l2)) pi2 ->
     P (rew (app_assoc (tens C D :: l0) _ (A :: l2)) in tens_r pi1 pi0 ) pi2) ->
  (forall A B C D l1 l2 l3 l4 Q (pi1 : ll Q (C :: D :: l1 ++ A :: l2)) (pi2 : ll Q (l3 ++ B :: l4)),
     P (pi1 : ll Q ((C :: D :: l1) ++ A :: l2)) pi2 ->
     P (parr_r pi1 : ll Q ((parr C D :: l1) ++ A :: l2)) pi2) ->
  (forall A B C e l1 l2 l3 l4 Q (pi1 : ll Q (C :: l1 ++ A :: l2)) (pi2 : ll Q (l3 ++ B :: l4)),
     P (pi1 : ll Q ((C :: l1) ++ A :: l2)) pi2 ->
     P (oc_r e pi1: ll Q (nil ++ _)) pi2) ->
  (forall A B C e l1 l2 l3 l4 Q (pi1 : ll Q (C :: l1 ++ A :: l2)) (pi2 : ll Q (l3 ++ B :: l4)),
     P (pi1 : ll Q ((C :: l1) ++ A :: l2)) pi2 ->
     P (de_r e pi1: ll Q (((wn e C) :: l1) ++ A :: l2)) pi2) ->
  (forall A B C e s1 l1 l2 l3 l4 Q (pi1 : ll Q ((map (fun p => wn p C) s1 ++ l1) ++ A :: l2)) (pi2 : ll Q (l3 ++ B :: l4)) (pi3:is_true (co_rule Q s1 e)),
     P (pi1 : ll Q ((map (fun p => wn p C) s1 ++ l1) ++ A :: l2)) pi2 ->
     P (rew (app_assoc ((wn e C) :: l1) _ (A :: l2)) in 
        (co_r e C s1 (l1 ++ A :: l2) 
        (rew<- app_assoc (map (fun p=> wn p C) s1) l1 (A :: l2) in pi1) 
        (pi3:is_true (co_rule Q s1 e)))) pi2) ->



  (forall C D C' D' l2' l2'' Q (pi1' : ll Q (C :: l2')) (pi1'' : ll Q (D :: l2'')),
     (forall l3 l4 (pi2 : ll Q (l3 ++ C' :: l4)), P (pi1' : ll Q (nil ++ _)) pi2) ->
     (forall l3 l4 (pi2 : ll Q (l3 ++ D' :: l4)), P (pi1'' : ll Q (nil ++ _)) pi2) ->
     forall l4' l4'' (pi2' : ll Q (C' :: l4')) (pi2'' : ll Q (D' :: l4'')),
       P (tens_r pi1' pi1'' : ll Q (nil ++ _)) (tens_r pi2' pi2'' : ll Q (nil ++ _))) ->
  (forall C D C' D' l2 Q (pi1 : ll Q (C :: D :: l2)),
     (forall l3 l4 (pi2 : ll Q (l3 ++ C' :: l4)), P (pi1 : ll Q (nil ++ _)) pi2) ->
      forall l4 (pi2 : ll Q (C' :: D' :: l4)),
       P (parr_r pi1 : ll Q (nil ++ _)) (parr_r pi2 : ll Q (nil ++ _))) ->
  (forall C D C' D' l1' l1'' Q (pi1' : ll Q (C :: l1')) (pi1'' : ll Q (D :: l1'')),
     (forall l3 l4 (pi2 : ll Q (l3 ++ C' :: l4)), P (pi1' : ll Q (nil ++ _)) pi2) ->
     (forall l3 l4 (pi2 : ll Q (l3 ++ D' :: l4)), P (pi1'' : ll Q (nil ++ _)) pi2) ->
     forall l4 (pi2 : ll Q (D' :: C' :: l4)),
       P (tens_r pi1' pi1'' : ll Q (nil ++ _)) (parr_r pi2 : ll Q (nil ++ _))) ->
  forall A B l1 l2 l3 l4 Q (pi1 : ll Q (l1 ++ A :: l2)) (pi2 : ll Q (l3 ++ B :: l4)), P pi1 pi2
.

Proof.
intros Hsym Hax1 Hax2 Hex Htens1 Htens2 Hparr Htt Hpp Htp.
enough (forall c s A B s1 s2 (pi1 : ll s1) (pi2 : ll s2),
          s = psize pi1 + psize pi2 -> fsize A <= c -> fsize B <= c ->
          forall l1 l2 l3 l4 (Heq1 : s1 = l1 ++ A :: l2) (Heq2 : s2 = l3 ++ B :: l4),
          P A B l1 l2 l3 l4 (rew Heq1 in pi1) (rew Heq2 in pi2)) as IH
  by (now intros A B l1 l2 l3 l4 pi1 pi2;
          refine (IH (max (fsize A) (fsize B)) _ _ _ _ _ pi1 pi2 _ _ _ _ _ _ _ eq_refl eq_refl);
          try lia).
induction c as [c IHf0] using lt_wf_rect.
assert (forall A B, fsize A < c -> fsize B < c ->
          forall l1 l2 l3 l4 pi1 pi2, P A B l1 l2 l3 l4 pi1 pi2) as IHf
  by (now intros A B HA HB l1 l2 l3 l4 pi1 pi2;
          refine (IHf0 (max (fsize A) (fsize B)) _ _ A _ _ _ pi1 pi2 _ _ _ _ _ _ _ eq_refl eq_refl);
          try lia); clear IHf0.
induction s as [s IHp0] using lt_wf_rect.
assert (forall A B l1 l2 l3 l4 pi1 pi2, psize pi1 + psize pi2 < s -> fsize A <= c -> fsize B <= c ->
          P A B l1 l2 l3 l4 pi1 pi2) as IHp
  by (now intros A B l1 l2 l3 l4 pi1 pi2 Hp HA HB;
          refine (IHp0 _ Hp _ _ _ _ pi1 pi2 _ _ _ _ _ _ _ eq_refl eq_refl)); clear IHp0.
intros A B s1 s2 pi1 pi2 Heqs HA HB l1 l2 l3 l4 Heq1 Heq2; rewrite_all Heqs; clear s Heqs.
destruct pi1.
- destruct l1; inversion Heq1; subst; cbn in Heq1.
  + destruct_eqrefl Heq1; apply Hax1.
  + destruct l1; inversion Heq1; subst.
    * destruct_eqrefl Heq1; apply Hax2.
    * exfalso; destruct l1; inversion Heq1.
- subst; cbn; apply Hex, IHp; cbn; rewrite ? psize_rew; lia.
- destruct l1; inversion Heq1.
  + destruct pi2; subst; cbn in HA; destruct_eqrefl Heq1.
    * repeat (destruct l3; inversion Heq2); subst; destruct_eqrefl Heq2; apply Hsym;
        [ apply Hax1 | apply Hax2 ].
    * apply Hsym, Hex, IHp; cbn; rewrite ? psize_rew; lia.
    * destruct l3; inversion Heq2; subst; cbn in HB.
      -- destruct_eqrefl Heq2.
         apply Htt; intros; apply IHf; lia.
      -- apply Hsym.
         dichot_elt_app_inf_exec H1; subst.
         ++ replace (rew [ll] Heq2 in tens_r pi2_1 pi2_2)
               with (rew <- (app_assoc (tens A1 B1 :: l3) _ _) in tens_r pi2_1 pi2_2).
            ** apply Htens1, IHp; cbn; try lia.
            ** rewrite <- (rew_opp_l ll (app_assoc (tens A1 B1 :: l3) (B :: l) l1)).
               f_equal; rewrite rew_compose.
               now assert (eq_trans Heq2 (app_assoc (tens A1 B1 :: l3) (B :: l) l1) = eq_refl)
                     as -> by apply (Eqdep_dec.UIP_dec (@eq_dt_dec (list_dectype formulas_dectype)));
                   cbn.
         ++ replace (rew [ll] Heq2 in tens_r pi2_1 pi2_2)
               with (rew (app_assoc (tens A1 B1 :: l6) _ _) in tens_r pi2_1 pi2_2).
            ** apply Htens2, IHp; cbn; lia.
            ** rewrite <- (rew_opp_r ll (app_assoc (tens A1 B1 :: l6) l2 (B :: l4))).
               f_equal; unfold eq_rect_r; rewrite rew_compose.
               now assert (eq_trans Heq2 (eq_sym (app_assoc (tens A1 B1 :: l6) l2 (B :: l4)))
                         = eq_refl)
                     as -> by apply (Eqdep_dec.UIP_dec (@eq_dt_dec (list_dectype formulas_dectype)));
                   cbn.
    * destruct l3; inversion Heq2; subst; destruct_eqrefl Heq2; cbn in HB.
      -- apply Htp; intros; apply IHf; lia.
      -- apply Hsym, Hparr, IHp; cbn; lia.
  + subst; cbn.
    dichot_elt_app_inf_exec H1; subst.
    * change ((tens A0 B0 :: l1) ++ A :: l ++ l0) with (tens A0 B0 :: l1 ++ A :: l ++ l0) in Heq1.
      replace (rew [ll] Heq1 in tens_r pi1_1 pi1_2)
         with (rew <- (app_assoc (tens A0 B0 :: l1) _ _) in tens_r pi1_1 pi1_2).
      -- apply Htens1, IHp; cbn; lia.
      -- rewrite <- (rew_opp_l ll (app_assoc (tens A0 B0 :: l1) (A :: l) l0)).
           f_equal; rewrite rew_compose.
           now assert (eq_trans Heq1 (app_assoc (tens A0 B0 :: l1) (A :: l) l0) = eq_refl)
                 as -> by apply (Eqdep_dec.UIP_dec (@eq_dt_dec (list_dectype formulas_dectype)));
               cbn.
    * change ((tens A0 B0 :: l5 ++ l6) ++ A :: l2)
        with (tens A0 B0 :: (l5 ++ l6) ++ A :: l2) in Heq1.
      replace (rew [ll] Heq1 in tens_r pi1_1 pi1_2)
         with (rew (app_assoc (tens A0 B0 :: l5) _ _) in tens_r pi1_1 pi1_2).
      -- apply Htens2, IHp; cbn; lia.
      -- rewrite <- (rew_opp_r ll (app_assoc (tens A0 B0 :: l5) l6 (A :: l2))).
         f_equal; unfold eq_rect_r; rewrite rew_compose.
         now assert (eq_trans Heq1 (eq_sym (app_assoc (tens A0 B0 :: l5) l6 (A :: l2))) = eq_refl)
               as -> by apply (Eqdep_dec.UIP_dec (@eq_dt_dec (list_dectype formulas_dectype)));
             cbn.
- destruct l1; inversion Heq1.
  + destruct pi2; subst; cbn in HA; destruct_eqrefl Heq1.
    * repeat (destruct l3; inversion Heq2); subst; destruct_eqrefl Heq2; apply Hsym;
        [ apply Hax1 | apply Hax2 ].
    * apply Hsym, Hex, IHp; cbn; rewrite ? psize_rew; lia.
    * destruct l3; inversion Heq2; subst; cbn in HB.
      -- destruct_eqrefl Heq2.
         apply Hsym, Htp; intros; apply IHf; lia.
      -- apply Hsym; cbn.
         dichot_elt_app_inf_exec H1; subst.
         ++ change ((tens A1 B1 :: l3) ++ B :: l ++ l1)
              with (tens A1 B1 :: l3 ++ B :: l ++ l1) in Heq2.
            replace (rew [ll] Heq2 in tens_r pi2_1 pi2_2)
               with (rew <- (app_assoc (tens A1 B1 :: l3) _ _) in tens_r pi2_1 pi2_2).
            ** apply Htens1, IHp; cbn; lia.
            ** rewrite <- (rew_opp_l ll (app_assoc (tens A1 B1 :: l3) (B :: l) l1)).
               f_equal; rewrite rew_compose.
               now assert (eq_trans Heq2 (app_assoc (tens A1 B1 :: l3) (B :: l) l1) = eq_refl)
                     as -> by apply (Eqdep_dec.UIP_dec (@eq_dt_dec (list_dectype formulas_dectype)));
                   cbn.
         ++ change ((tens A1 B1 :: l0 ++ l5) ++ B :: l4)
              with (tens A1 B1 :: (l0 ++ l5) ++ B :: l4) in Heq2.
            replace (rew [ll] Heq2 in tens_r pi2_1 pi2_2)
               with (rew (app_assoc (tens A1 B1 :: l0) _ _) in tens_r pi2_1 pi2_2).
            ** apply Htens2, IHp; cbn; lia.
            ** rewrite <- (rew_opp_r ll (app_assoc (tens A1 B1 :: l0) l5 (B :: l4))).
               f_equal; unfold eq_rect_r; rewrite rew_compose.
               now assert (eq_trans Heq2 (eq_sym (app_assoc (tens A1 B1 :: l0) l5 (B :: l4)))
                         = eq_refl)
                     as -> by apply (Eqdep_dec.UIP_dec (@eq_dt_dec (list_dectype formulas_dectype)));
                   cbn.
    * destruct l3; inversion Heq2; subst; cbn in HB; destruct_eqrefl Heq2.
      -- apply Hpp; intros; apply IHf; lia.
      -- apply Hsym, Hparr, IHp; cbn; lia.
  + subst; cbn; destruct_eqrefl Heq1.
    apply Hparr, IHp; cbn; lia.
Qed.

Theorem cut A l1 l2 l3 l4 :
  ll (l1 ++ A :: l2) -> ll (l3 ++ dual A :: l4) -> ll (l3 ++ l2 ++ l1 ++ l4).
Proof.
intros pi1 pi2; assert (Heq := eq_refl (dual A)); revert pi1 pi2 Heq.
apply (sym_induction_ll (fun A B l1 l2 l3 l4 pi1 pi2 => B = dual A -> ll (l3 ++ l2 ++ l1 ++ l4)));
  clear A l1 l2 l3 l4; cbn; try now intuition subst.
- intros A B l1 l2 l3 l4 pi1 pi2 pi ->.
  apply (ex_r (pi (eq_sym (bidual A)))).
  rewrite (app_assoc l1), (app_assoc l3); apply Permutation_Type_app_comm.
- intros A B l1 l2 l3 l4 l' pi1 pi2 HP.
  destruct (Permutation_Type_vs_elt_inv A l1 l2 HP) as [(l1', l2') ->]; cbn in pi1, HP; cbn.
  intros pi0' pi0; apply pi0' in pi0; clear - HP pi0.
  apply (ex_r pi0).
  apply Permutation_Type_app_head; rewrite ? app_assoc; apply Permutation_Type_app_tail.
  transitivity (l1' ++ l2'); [ apply Permutation_Type_app_comm | ].
  transitivity (l1 ++ l2); [ | apply Permutation_Type_app_comm ].
  apply (Permutation_Type_app_inv _ _ _ _ _ HP).
- intros A B C D l0 l1 l2 l3 l4 pi1 pi2 pi3 pi4 ->.
  change (ll (l3 ++ (l2 ++ l0) ++ tens C D :: l1 ++ l4)).
  apply ex_r with (tens C D :: ((l1 ++ l4) ++ l3 ++ l2) ++ l0); [ apply tens_r; trivial | ].
  + apply (ex_r (pi4 eq_refl)).
    rewrite app_assoc; apply Permutation_Type_app_comm.
  + list_simpl; rewrite app_comm_cons, app_assoc, ? (app_assoc l3), (app_assoc (l3 ++ l2)).
    apply Permutation_Type_app_comm.
- intros A B C D l0 l1 l2 l3 l4 pi1 pi2 pi3 pi4' pi4; apply pi4' in pi4; clear pi4'.
  apply ex_r with (tens C D :: l0 ++ (l1 ++ l4) ++ l3 ++ l2); [ apply tens_r; trivial | ].
  + apply (ex_r pi4).
    rewrite app_assoc; apply Permutation_Type_app_comm.
  + list_simpl; rewrite app_comm_cons, ? (app_assoc l3), ? app_assoc, <- app_assoc.
    apply Permutation_Type_app_comm.
- intros A B C D l1 l2 l3 l4 pi1 pi2 pi3' pi3; apply pi3' in pi3; clear pi3'.
  apply ex_r with (parr C D :: (l1 ++ l4) ++ l3 ++ l2); [ apply parr_r, (ex_r pi3) | ].
  + rewrite app_assoc; apply Permutation_Type_app_comm.
  + list_simpl; rewrite app_comm_cons, ? app_assoc, <- app_assoc.
    apply Permutation_Type_app_comm.
- intros C D C' D' l1 l2 pi1 pi2 IHC IHD l0 pi0 Heq; injection Heq as -> ->.
  rewrite <- app_assoc; apply IHC; auto.
  now rewrite <- app_nil_l; apply IHD.
Qed.

End Atoms.
