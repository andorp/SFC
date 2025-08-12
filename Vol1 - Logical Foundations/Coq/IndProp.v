Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export Logic.

Fixpoint div2 (n : nat) : nat :=
  match n with
    0 => 0
  | 1 => 0
  | S (S n) => S (div2 n)
  end.

Definition csf (n : nat) : nat :=
  if even n then div2 n
  else (3 * n) + 1.

Inductive Collatz_holds_for : nat -> Prop :=
  | Chf_one : Collatz_holds_for 1
  | Chf_even (n : nat) :
      even n = true ->
      Collatz_holds_for (div2 n) ->
      Collatz_holds_for n
  | Chf_odd (n : nat) :
      even n = false ->
      Collatz_holds_for ((3 * n) + 1) ->
      Collatz_holds_for n.

Example Collatz_holds_for_12 : Collatz_holds_for 12.
Proof.
  apply Chf_even. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_odd. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_odd. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_one.
Qed.

Theorem collatz : forall n ,
  n <> 0 -> Collatz_holds_for n.
Proof.
Admitted.

Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat)   :           le n n
  | le_S (n m : nat) : le n m -> le n (S m).

Notation "n <= m" := (le n m) (at level 70).

Example le_3_5 : 3 <= 5.
Proof. apply le_S, le_S, le_n. Qed.

Inductive clos_trans {X : Type} (R : X -> X -> Prop) : X -> X -> Prop :=
  | t_step (x y : X) : R x y -> clos_trans R x y
  | t_trans (x y z : X) :
      clos_trans R x y ->
      clos_trans R y z ->
      clos_trans R x z.

Inductive Person : Type :=
  Sage | Cleo | Ridley | Moss.

Inductive parent_of : Person -> Person -> Prop :=
  | po_SC : parent_of Sage Cleo
  | po_SR : parent_of Sage Ridley
  | po_CM : parent_of Cleo Moss.

Definition ancestor_of : Person -> Person -> Prop :=
  clos_trans parent_of.

Example ancestor_of_ex : ancestor_of Sage Moss.
Proof.
  apply t_trans with Cleo.
  - apply t_step, po_SC.
  - apply t_step, po_CM.
Qed.

Inductive clos_refl_trans {X : Type} (R : X -> X -> Prop) : X -> X -> Prop :=
  | rt_step (x y : X) : R x y -> clos_refl_trans R x y
  | rt_refl (x   : X) :          clos_refl_trans R x x
  | rt_trans (x y z : X) :
      clos_refl_trans R x y ->
      clos_refl_trans R y z ->
      clos_refl_trans R x z.

Definition cs (n m : nat) : Prop := csf n = m.

Definition cms n m := clos_refl_trans cs n m.

Conjecture collatz' : forall n, n <> 0 -> cms n 1.

Inductive rstc {X : Type} (R : X -> X -> Prop) : X -> X -> Prop :=
  | rstc_step (x y : X) : R x y -> rstc R x y
  | rstc_refl (x   : X) :          rstc R x x
  | rstc_sym  (x y : X) :
      rstc R x y ->
      rstc R y x
  | rstc_trans (x y z : X) :
      rstc R x y ->
      rstc R y z ->
      rstc R x z.

Inductive Perm3 {X : Type} : list X -> list X -> Prop :=
  | p3_swap12 (a b c : X) :
      Perm3 [a;b;c] [b;a;c]
  | p3_swap23 (a b c : X) :
      Perm3 [a;b;c] [a;c;b]
  | p3_trans (l1 l2 l3 : list X) :
      Perm3 l1 l2 ->
      Perm3 l2 l3 ->
      Perm3 l1 l3.

Theorem identityPerm3 :
  forall (X : Type) (a b c : X) ,
  Perm3 [a;b;c] [a;b;c].
Proof.
  intros X a b c.
  apply p3_trans with [a;c;b] ; apply p3_swap23.
Qed.

Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n))
  .

Example sixIsEven :
  ev 6.
Proof.
  apply ev_SS, ev_SS, ev_SS , ev_0.
Qed.

Theorem ev_double : forall n,
  ev (double n).
Proof.
  intros n.
  induction n as [|n IH].
  - apply ev_0.
  - simpl.
    apply ev_SS.
    assumption.
Qed.

Example Perm3_ex1 : Perm3 [1;2;3] [2;3;1].
Proof.
  apply p3_trans with [2;1;3].
  - apply p3_swap12.
  - apply p3_swap23.
Qed.

Theorem ev_inversion : forall (n : nat),
    ev n ->
    (n = 0) \/ (exists m, n = S (S m) /\ ev m).
Proof.
  intros n H1.
  destruct H1 as [|n H1].
  - left. reflexivity.
  - right.
    exists n.
    split.
    + reflexivity.
    + assumption.
Qed.

Theorem le_inversion : forall (n m : nat),
  le n m ->
  (n = m) \/ (exists m', m = S m' /\ le n m').
Proof.
  intros n m H1.
  destruct H1 as [n|n m H1].
  - left. reflexivity.
  - right.
    exists m.
    split.
    + reflexivity.
    + assumption.
Qed.