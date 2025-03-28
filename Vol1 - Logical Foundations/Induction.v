From LF Require Export Basics.

(* Require Export LF.Basics. *)

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

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S m => S (S (double m))
  end.

Lemma double_plus : forall (n:nat) , double n = n + n.
Proof.
  intros n.
  induction n as [|n IH].
  - reflexivity.
  - simpl.
    rewrite -> IH.
    rewrite <- plus_n_Sm.
    reflexivity.
Qed.

Theorem eqb_refl : forall (n:nat),
  (n =? n) = true.
Proof.
  intros n.
  induction n as [|n IH].
  - reflexivity.
  - simpl.
    apply IH.
Qed.

Theorem even_S : forall (n: nat),
  even (S n) = negb (even n).
Proof.
  intros n.
  induction n as [|n IH].
  - reflexivity.
  - rewrite IH.
    rewrite negb_involutive.
    reflexivity.
Qed.

Theorem mult_0_plus' : forall (n m : nat),
  (n + 0 + 0) * m = n * m.
Proof.
  intros n m.
  assert (n + 0 + 0 = n) as H.
    { rewrite add_comm.
      simpl.
      rewrite add_comm.
      reflexivity.
    }
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_rearrange_firsttry : forall (n m p q : nat),
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  (* We just need to swap (n + m) for (m + n)... seems
     like add_comm should do the trick! *)
  rewrite add_comm.
  (* Doesn't work... Coq rewrites the wrong plus! :-( *)
Abort.

Theorem plus_rearrange : forall (n m p q : nat),
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (n + m = m + n) as H.
    { rewrite add_comm. reflexivity. }
  rewrite H.
  reflexivity.
Qed.

Theorem add_assoc' : forall (n m p : nat),
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| n IHn] ; try reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.

Theorem add_comm' : forall (n m : nat),
  n + m = m + n.
Proof.
  intros n m.
  induction n as [|n IHn].
  - apply plus_n_O.
  - simpl.
    rewrite <- plus_n_Sm , IHn.
    reflexivity.
Qed.

Theorem eqnb_refl : forall (n : nat),
  (n =? n) = true.
Proof.
  intros n.
  induction n as [|n IHn].
  - reflexivity.
  - simpl.
    apply IHn.
Qed.

Theorem add_shuffle3 : forall (n m p : nat),
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite add_assoc.
  assert (n + m = m + n) as H. { apply add_comm. }
  rewrite H.
  rewrite <- add_assoc.
  reflexivity.
Qed.

Theorem plus_leb_compat_l : forall (n m p : nat),
  n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
  intros n m p H1.
  induction p as [|p IH].
  - simpl.
    apply H1.
  - simpl.
    apply IH.
Qed.

Theorem leb_refl : forall (n:nat),
  (n <=? n) = true.
Proof.
  intros n.
  induction n as [|n IHn].
  - reflexivity.
  - simpl.
    apply IHn.
Qed.

Theorem zero_neqb_S : forall (n:nat),
  0 =? (S n) = false.
Proof.
  intros n.
  reflexivity.
Qed.

Theorem andb_false_r : forall (b:bool),
  andb b false = false.
Proof.
  intros b.
  destruct b ; reflexivity.
Qed.

Theorem S_neqb_0 : forall (n:nat),
  (S n) =? 0 = false.
Proof.
  intros n.
  reflexivity.
Qed.

Theorem mult_1_l : forall (n:nat), 1 * n = n.
Proof.
  intros n.
  simpl.
  symmetry.
  apply plus_n_O.
Qed.

Theorem all3_spec : forall (b c : bool),
  orb
    (andb b c)
    (orb (negb b)
         (negb c))
  = true.
Proof.
  intros b c.
  destruct b,c ; reflexivity.
Qed.

Theorem mult_plus_distr_r : forall (n m p : nat),
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p.
  induction p as [|p IHp].
  - rewrite <- mult_n_O , <- mult_n_O, <- mult_n_O.
    reflexivity.
  - rewrite <- mult_n_Sm , <- mult_n_Sm , <- mult_n_Sm.
    rewrite <- (add_assoc (n * p) n (m * p + m)).
    rewrite (add_comm n (m * p + m)).
    rewrite <- (add_assoc (m * p) m n).
    rewrite (add_comm m n).
    rewrite (add_assoc (n * p) (m * p) (n + m)).
    rewrite IHp.
    reflexivity.
Qed.

Theorem mult_assoc : forall (n m p : nat),
  n * (m * p) = (n * m) * p.
Proof.
  intros n m p.
  induction n as [|n IHn].
  - reflexivity.
  - simpl.
    rewrite (mult_plus_distr_r m (n * m) p).
    rewrite IHn.
    reflexivity.
Qed.

Theorem add_shuffle3' : forall (n m p : nat),
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite (add_comm n (m + p)).
  rewrite (add_comm n p).
  rewrite (add_assoc m p n).
  reflexivity.
Qed.

Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin)
  .

Fixpoint incr (m:bin) : bin :=
  match m with
  | Z    => B1 Z
  | B0 n => B1 n        (* 2n     => 2n + 1             *)
  | B1 n => B0 (incr n) (* 2n + 1 => 2n + 2 = 2 (n + 1) *)
  end.

Fixpoint bin_to_nat (m:bin) : nat :=
  match m with
  | Z    => 0
  | B0 n =>     2 * (bin_to_nat n)
  | B1 n => 1 + 2 * (bin_to_nat n)
  end.

Theorem bin_to_nat_pres_incr : forall (b : bin),
  bin_to_nat (incr b) = 1 + bin_to_nat b.
Proof.
  intros b.
  simpl.
  induction b as [|b _|b IH] ; try reflexivity.
  - simpl.
    rewrite IH.
    rewrite <- (plus_n_O (S (bin_to_nat b))).
    rewrite <- (plus_n_O (bin_to_nat b)).
    rewrite (plus_n_Sm (bin_to_nat b) (bin_to_nat b)).
    reflexivity.
Qed.

