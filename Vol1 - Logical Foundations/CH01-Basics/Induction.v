Print LoadPath.

(* From LF Require Export Basics. *)

Theorem add_0_r_firsttry : forall (n:nat),
  n + 0 = n.
Proof.
  intros n.
  simpl.
Abort.

Theorem add_0_r : forall (n:nat),
  n + 0 = n.
Proof.
  intros n. induction n as [| m IHm ].
  - reflexivity.
  - simpl.
    rewrite -> IHm.
    reflexivity.
Qed.

Theorem minus_n_n : forall (n:nat),
  minus n n = 0.
Proof.
  induction n as [|m IHm].
  - reflexivity.
  - simpl.
    rewrite -> IHm.
    reflexivity.
Qed.

Theorem mul_0_r : forall (n:nat),
  n * 0 = 0.
Proof.
  induction n as [|m IHm].
  - reflexivity.
  - simpl.
    rewrite -> IHm.
    reflexivity.
Qed.

Theorem plus_n_Sm : forall (n m : nat),
  S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [|n' IHn'].
  - simpl.
    reflexivity.
  - simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem add_comm : forall (n m : nat),
  n + m = m + n.
Proof.
  intros n m.
  induction n as [|n' IHn'].
  - simpl.
    rewrite add_0_r.
    reflexivity.
  - simpl.
    rewrite IHn'.
    rewrite plus_n_Sm.
    reflexivity.
Qed.

Theorem add_assoc : forall (n m p : nat),
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [|n' IHn'].
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHn'.
    reflexivity.
Qed.