(* https://softwarefoundations.cis.upenn.edu/lf-current/Basics.html *)

Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday
  .

Definition next_working_day (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Compute (next_working_day friday).

Compute (next_working_day (next_working_day saturday)).

Example test_next_working_day :
  (next_working_day (next_working_day saturday)) = tuesday.
Proof.
  simpl.
  reflexivity.
Qed.

From Coq Require Export String.

Inductive bool : Type :=
  | true
  | false
  .

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1 b2 : bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1 b2 : bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Example test_orb1 : (orb true false) = true.
Proof. simpl. reflexivity. Qed.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5 : false || false || true = true.
Proof. simpl. reflexivity. Qed.

(* Exercise: 1 star, standard (nandb) *)

Definition nandb (b1:bool) (b2:bool) : bool :=
  negb (andb b1 b2).

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

Check true.

Check true : bool.
Check (negb true) : bool.

Check negb : bool -> bool.

Inductive rgb : Type :=
  | red
  | green
  | blue
  .

Inductive color : Type :=
  | black
  | white
  | primary (p : rgb)
  .

Definition monochrome (c : color) : bool :=
  match c with
  | black => true
  | white => true
  | primary p => false
  end.

Definition isred (c : color) : bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false
  end.

Module Playground.
  Definition foo : rgb := blue.
End Playground.

Definition foo : bool := true.

Check Playground.foo : rgb.
Check foo : bool.

Module TuplePlayground.

  Inductive bit : Type :=
    | B1
    | B0
    .

  Inductive nybble : Type :=
    | bits (b0 b1 b2 b3 : bit).

  Check (bits B1 B0 B1 B0) : nybble.

  Definition all_zero (nb : nybble) : bool :=
    match nb with
    | (bits B0 B0 B0 B0) => true
    | (bits _ _ _ _) => false
    end.

  Compute (all_zero (bits B1 B0 B1 B0)).
  Compute (all_zero (bits B0 B0 B0 B0)).

End TuplePlayground.

Module NatPlayground.

  Inductive nat : Type :=
    | O
    | S (n : nat)
    .

  Inductive otherNat : Type :=
    | stop
    | tick (foo : otherNat)
    .

  Definition pred (n : nat) : nat :=
    match n with
    | O => O
    | S n' => n'
    end.

End NatPlayground.

Check (S (S (S (S O)))).
(* ===> 4 : nat *)

Definition minustwo (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.

Compute (minustwo 4).
(* ===> 2 : nat *)

Check S : nat -> nat.
Check pred : nat -> nat.
Check minustwo : nat -> nat.

Fixpoint even (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.

Definition odd (n:nat) : bool :=
  negb (even n).

Example test_odd1: odd 1 = true.
Proof. simpl. reflexivity. Qed.

Example test_odd2: odd 4 = false.
Proof. Show. simpl. Show. reflexivity. Show. Qed.

Module NatPlayground2.

  Fixpoint plus (n : nat) (m : nat) : nat :=
    match n with
    | O => m
    | S n' => S (plus n' m)
    end.

  Compute (plus 3 2).
  (* ===> 5 : nat *)

  Fixpoint mult (n m : nat) : nat :=
    match n with
    | O => O
    | S n' => plus m (mult n' m)
    end.

  Example test_mult1: (mult 3 3) = 9.
  Proof. simpl. Show. reflexivity. Show. Qed.

  Fixpoint minus (n m:nat) : nat :=
    match n, m with
    | O , _ => O
    | S _ , O => n
    | S n', S m' => minus n' m'
    end.

End NatPlayground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
  | O => S O
  | S p => mult base (exp base p)
  end.

(* Exercise: 1 star, standard (factorial) *)

Fixpoint factorial (n:nat) : nat :=
  match n with
  | O   => S O
  | S n => mult (S n) (factorial n)
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. Show. reflexivity. Qed.

Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.


Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.

Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.

Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.

Check ((0 + 1) + 1) : nat.

Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O =>
    match m with
    | O => true
    | S m' => false
    end
  | S n' =>
    match m with
    | O => false
    | S m' => eqb n' m'
    end
  end.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
    match m with
    | O => false
    | S m' => leb n' m'
    end
  end.

Example test_leb1: leb 2 2 = true.
Proof. simpl. reflexivity. Qed.

Example test_leb2: leb 2 4 = true.
Proof. simpl. reflexivity. Qed.

Example test_leb3: leb 4 2 = false.
Proof. simpl. reflexivity. Qed.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

Example test_leb3': (4 <=? 2) = false.
Proof. simpl. reflexivity. Qed.

(* Exercise: 1 star, standard (ltb) *)

Definition ltb (n m : nat)
  : bool
  := (n <=? m) && negb (n =? m) .
  
Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

Example test_ltb1: (ltb 2 2) = false.
Proof. reflexivity. Qed.

Example test_ltb2: (ltb 2 4) = true.
Proof. reflexivity. Qed.

Example test_ltb3: (ltb 4 2) = false.
Proof. reflexivity. Qed.

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof. intros n. simpl. reflexivity. Show. Qed.

Theorem plus_O_n' : forall n : nat, 0 + n = n.
Proof. intros n. reflexivity. Qed.

Theorem plus_O_n'' : forall n : nat , 0 + n = n.
Proof. intros m. Show. reflexivity. Qed.

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof. intros n. Show. reflexivity. Show. Qed.

Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof. intros n. Show. reflexivity. Qed.

Theorem plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.
Proof.
  intros n m.
  intros H.
  rewrite -> H. (* subst. *)
  reflexivity.
Qed.

Print plus_id_example.

(* https://softwarefoundations.cis.upenn.edu/lf-current/Basics.html *)

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H1 H2.
  rewrite -> H1.
  rewrite <- H2.
  reflexivity.
Qed.

Theorem mult_n_0_m_0 : forall p q : nat,
  (p * 0) + (q * 0) = 0.
Proof.
  intros p q.
  rewrite <- mult_n_O.
  rewrite <- mult_n_O.
  reflexivity.
Qed.

Check mult_n_O.
(* ===> forall n : nat, 0 = n * 0 *)
Check mult_n_Sm.
(* ===> forall n m : nat, n * m + n = n * S m *)

(* Use mult_n_Sm and mult_n_0 to prove the following theorem. (Recall that 1 is S O.)  *)

Theorem mult_n_1 : forall p : nat,
  p * 1 = p.
Proof.
  intros p.
  rewrite <- mult_n_Sm.
  rewrite <- mult_n_O.
  simpl.
  reflexivity.
Qed.

Theorem plus_1_neq_0_firsttry : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n.
  simpl. (* does nothing! *)
Abort.

Theorem plus_1_neq_0 : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
Qed.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. (destruct b ; reflexivity).
Qed.

Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c.
  destruct b ; destruct c ; reflexivity.
Qed.

Theorem andb3_exchange :
  forall b c d, andb (andb b c) d = andb (andb b d) c.
Proof.
  intros b c d.
  destruct b ; destruct c ; destruct d ; reflexivity.
Qed.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c H1.

  destruct b
    ; destruct c
    ; try reflexivity
    ; simpl in H1
    ; rewrite <- H1
    ; reflexivity .
Qed.

Theorem plus_1_neq_0' : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros [|n] ; reflexivity.
Qed.

Theorem andb_commutative'' :
  forall b c, andb b c = andb c b.
Proof.
  intros [] [] ; reflexivity.
Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
  0 =? (n + 1) = false.
Proof.
  intros [] ; reflexivity.
Qed.
