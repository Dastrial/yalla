(* microyalla library for linear logic *)

Open Scope list_scope.

Require List.
(* only List.map from module List is used:
Fixpoint map {A B : Type} (f: A -> B) l :=
    match l with
      | nil => nil
      | a :: t => (f a) :: (map f t)
    end.
*)

(* Transpose elements of index n and n+1 in l *)
Fixpoint transp {A} n (l : list A) :=
match n, l with
| 0, x :: y :: r => y :: x :: r
| S n, x :: r => x :: transp n r
| _, r => r
end.


(* Adapted from yalla/formulas.v *)

(** A set of atoms for building formulas *)
Definition Atom := nat.

(** Formulas *)
Inductive formula : Set :=
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
| oc : formula -> formula
| wn : formula -> formula.


(* Adapted from yalla/ll_def.v *)

(** Rules *)
Inductive ll : list formula -> Type :=
| ax_r : forall X, ll (covar X :: var X :: nil)
| ex_t_r : forall n l, ll l -> ll (transp n l)
| one_r : ll (one :: nil)
| bot_r : forall l, ll l -> ll (bot :: l)
| tens_r : forall A B l1 l2, ll (A :: l1) -> ll (B :: l2) -> ll (tens A B :: l1 ++ l2)
| parr_r : forall A B l, ll (A :: B :: l) -> ll (parr A B :: l)
| top_r : forall l, ll (top :: l)
| plus_r1 : forall A B l, ll (A :: l) -> ll (aplus A B :: l)
| plus_r2 : forall A B l, ll (A :: l) -> ll (aplus B A :: l)
| with_r : forall A B l, ll (A :: l) -> ll (B :: l) -> ll (awith A B :: l)
| oc_r : forall A l, ll (A :: List.map wn l) -> ll (oc A :: List.map wn l)
| de_r : forall A l, ll (A :: l) -> ll (wn A :: l)
| wk_r : forall A l, ll l -> ll (wn A :: l)
| co_r : forall A l, ll (wn A :: wn A :: l) -> ll (wn A :: l).
