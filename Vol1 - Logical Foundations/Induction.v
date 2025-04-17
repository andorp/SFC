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
  | Z    => B1 Z        (*  0     => 2*0 + 1*)
  | B0 n => B1 n        (* 2n     => 2n + 1             *)
  | B1 n => B0 (incr n) (* 2n + 1 => 2n + 2 = 2 (n + 1) *)
  end.

Example test_bin_incr0 : (incr Z) = (B1 Z).
Proof. reflexivity. Qed.

Example test_bin_incr1 : (incr (B1 Z)) = B0 (B1 Z).
Proof. reflexivity. Qed.

Example test_bin_incr2 : (incr (B0 (B1 Z))) = B1 (B1 Z).
Proof. reflexivity. Qed.

Example test_bin_incr3 : (incr (B1 (B1 Z))) = B0 (B0 (B1 Z)).
Proof. reflexivity. Qed.

Example test_bin_incr4 : (incr (B0 Z)) = (B1 Z).
Proof. reflexivity. Qed.

Fixpoint bin_to_nat (m:bin) : nat :=
  match m with
  | Z    => 0
  | B0 n =>     2 * (bin_to_nat n)
  | B1 n => 1 + 2 * (bin_to_nat n)
  end.

Theorem bin_to_nat_incr : forall (b:bin) , bin_to_nat (incr b) = S (bin_to_nat b).
Proof.
  intros b. induction b as [|b _|b H1].
  - reflexivity.
  - reflexivity.
  - simpl.
    rewrite H1.
    rewrite <- plus_n_O.
    rewrite <- plus_n_O.
    rewrite <- plus_n_Sm.
    reflexivity.
Qed.

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

Fixpoint nat_to_bin (n:nat) : bin :=
  match n with
  | O     => Z
  | (S n) =>
    match nat_to_bin n with
    | Z    => B1 Z
    | B0 x => B1 x
    | B1 x => B0 (incr x)
    end
  end.

Example nat_to_bin_test1 : (nat_to_bin 0) = Z.
Proof. reflexivity. Qed.

Example nat_to_bin_test2 : (nat_to_bin 1) = B1 Z.
Proof. reflexivity. Qed.

Example nat_to_bin_test3 : (nat_to_bin 2) = B0 (B1 Z).
Proof. reflexivity. Qed.

Example nat_to_bin_test4 : (nat_to_bin 3) = B1 (B1 Z).
Proof. reflexivity. Qed.

Example nat_to_bin_test5 : (nat_to_bin 4) = B0 (B0 (B1 Z)).
Proof. reflexivity. Qed.

Theorem nat_bin_nat : forall n,
  bin_to_nat (nat_to_bin n) = n.
Proof.
  intros n.
  induction n as [|n IHn] ; try reflexivity.
  simpl.
  destruct (nat_to_bin n) as [|x|x] eqn:H1.
  - simpl.
    simpl in IHn.
    rewrite IHn.
    reflexivity.
  - simpl.
    simpl in IHn.
    rewrite IHn.
    reflexivity.
  - simpl.
    simpl in IHn.
    rewrite bin_to_nat_incr.
    simpl.
    rewrite <- plus_n_Sm.
    rewrite IHn.
    reflexivity.
Qed.

Lemma double_incr : forall (n : nat),
  double (S n) = S (S (double n)).
Proof.
  intros n.
  reflexivity.
Qed.

Definition double_bin (b:bin) : bin :=
  match b with
  | Z    => Z         (* 0    => 0    *)
  | B0 x => B0 (B0 x) (* 2x   => 2*2x *)
  | B1 x => B0 (B1 x) (* 2x+1 => 2(2x + 1) *)
  end.

Example double_bin_zero : double_bin Z = Z.
Proof. reflexivity. Qed.

Lemma double_incr_bin : forall (b:bin),
    double_bin (incr b) = incr (incr (double_bin b)).
Proof.
  intros b.
  destruct b as [|b|b]; reflexivity.
Qed.

Fixpoint normalize (b:bin) : bin :=
  match b with
  | Z    => Z
  | B0 b => double_bin (normalize b)
  | B1 b => B1 (normalize b)
  end.

Example normalize_test0 : (normalize Z) = Z.
Proof. reflexivity. Qed.

Example normalize_test1 : (normalize (B0 Z)) = Z.
Proof. reflexivity. Qed.

Example normalize_test2 : (normalize (B0 (B0 Z))) = Z.
Proof. reflexivity. Qed.

Example normalize_test3 : (normalize (B1 (B0 Z))) = B1 Z.
Proof. reflexivity. Qed.

Example normalize_test4 : (normalize (B1 (B0 (B0 Z)))) = B1 Z.
Proof. reflexivity. Qed.

Example normalize_test5 : (normalize (B0 (B1 (B0 (B0 Z))))) = B0 (B1 Z).
Proof. reflexivity. Qed.

Example lemma0Ex1 : (nat_to_bin (S O)) = incr (nat_to_bin O).
Proof. reflexivity. Qed.

Example lemma0Ex2 : (nat_to_bin (S (S O))) = incr (nat_to_bin (S O)).
Proof. reflexivity. Qed.

Example lemma0Ex3 : (nat_to_bin (S (S (S O)))) = incr (nat_to_bin (S (S O))).
Proof. reflexivity. Qed.

Lemma lemma0 : forall (n : nat) ,
  (nat_to_bin (S n)) = incr (nat_to_bin n).
Proof.
  intros n.
  destruct n as [|n].
  - reflexivity.
  - simpl.
    destruct (nat_to_bin n) ; reflexivity.
Qed.

Example lemma1Ex1 : nat_to_bin (O + O) = double_bin (nat_to_bin O).
Proof. reflexivity. Qed.

Example lemma1Ex2 : nat_to_bin (1 + 1) = double_bin (nat_to_bin 1).
Proof. reflexivity. Qed.

Example lemma1Ex3 : nat_to_bin (2 + 2) = double_bin (nat_to_bin 2).
Proof. reflexivity. Qed.

Lemma lemma1 : forall (n : nat) ,
  nat_to_bin (n + n) = double_bin (nat_to_bin n).
Proof.
  intros n.
  induction n as [|n IH].
  - reflexivity.
  - rewrite <- plus_n_Sm.
    rewrite (lemma0 (S n + n)).
    rewrite plus_Sn_m.
    rewrite (lemma0 (n + n)).
    rewrite IH.
    rewrite (lemma0 n).
    rewrite double_incr_bin.
    reflexivity.
Qed.

Theorem bin_nat_bin : forall (b:bin),
  nat_to_bin (bin_to_nat b) = normalize b.
Proof.
  intros b.
  induction b as [|b IH|b IH].
  - reflexivity.
  - simpl.
    rewrite
      <- (plus_n_O (bin_to_nat b)) ,
      (lemma1 (bin_to_nat b))      , 
      IH.
    reflexivity.
  - simpl.
    rewrite <- (plus_n_O (bin_to_nat b)).
    rewrite (lemma1 (bin_to_nat b)).
    rewrite IH.
    destruct (normalize b) ; reflexivity.
Qed.

