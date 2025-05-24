From LF Require Export Poly.

Theorem silly1 : forall (n m : nat),
  n = m ->
  n = m.
Proof.
  intros n m eq.
  apply eq.
Qed.

Theorem silly2 : forall (n m o p : nat),
  n = m ->
  (n = m -> [n;o] = [m;p]) ->
  [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2.
  apply eq1.
Qed.

Theorem silly2a : forall (n m : nat),
  (n,n) = (m,m) ->
  (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
  [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2.
  apply eq1.
Qed.

Theorem silly_ex : forall p,
  (forall n, even n = true -> even (S n) = false) ->
  (forall n, even n = false -> odd n = true) ->
  even p = true ->
  odd (S p) = true.
Proof.
  intros p H1 H2 H3.
  apply H2, H1, H3.
Qed.

Theorem silly3 : forall (n m : nat),
  n = m ->
  m = n.
Proof.
  intros n m H.
  symmetry.
  assumption.
Qed.

Theorem rev_exercise1 : forall (l l' : list nat),
  l = rev l' ->
  l' = rev l.
Proof.
  intros l l' H1.
  rewrite H1.
  symmetry.
  apply rev_involutive.
Qed.

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity.
Qed.

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with [c;d].
  apply eq1.
  apply eq2.
Qed.

Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
  intros n m o p H1 H2.
  apply trans_eq with m ; assumption.
Qed.

Theorem S_injective : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H1.
  assert (H2: n = pred (S n)). { reflexivity. }
  rewrite H2. rewrite H1. simpl. reflexivity.
Qed.

Theorem S_injective' : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H.
  injection H as H.
  assumption.
Qed.

Theorem injection_ex1 : forall (n m o : nat),
  [n;m] = [o;o] ->
  n = m.
Proof.
  intros n m o H.
  injection H as H1 H2.
  subst.
  reflexivity.
Qed.

Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  j = z :: l ->
  x = y.
Proof.
  intros X x y z l j H1 H2.
  rewrite H2 in H1.
  injection H1 as H3 H4.
  subst.
  reflexivity.
Qed.

Theorem discriminate_ex1 : forall (n m : nat),
  false = true ->
  n = m.
Proof.
  intros n m H1.
  exfalso. (* exfalso changes the goal to False *)
  discriminate.
Qed.

Theorem discriminate_ex2 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n H1.
  exfalso. 
  discriminate.
Qed.

Example discriminate_ex3 :
  forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = [] ->
  x = z.
Proof.
  intros X x y z l j H1.
  exfalso.
  discriminate.
Qed.

Theorem eqb_0_l : forall n,
   0 =? n = true -> n = 0.
Proof.
  intros n.
  destruct n as [| n'] eqn:E.
  - intros H.
    reflexivity.
  - simpl.
    intros H.
    exfalso.
    discriminate.
Qed.

Theorem eqb_0_l' : forall n,
   0 =? n = true -> n = 0.
Proof.
  intros n H.
  destruct n as [| n].
  - reflexivity.
  - exfalso.
    discriminate.
Qed.

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
Proof.
  intros A B f x y H1.
  subst.
  reflexivity.
Qed.

Theorem silly4 : forall (n m p q : nat),
  (n = m -> p = q) ->
  m = n ->
  q = p.
Proof.
  intros n m p q H1 H2.
  symmetry in H2.
  apply H1 in H2.
  symmetry in H2.
  assumption.
Qed.
  
Theorem silly4' : forall (n m p q : nat),
  (n = m -> p = q) ->
  m = n ->
  q = p.
Proof.
  intros n m p q H1 H2.
  symmetry.
  apply H1.
  symmetry.
  assumption.
Qed.

Theorem specialize_example: forall n,
  (forall m, m * n = 0) ->
  n = 0.
Proof.
  intros n H1.
  specialize H1 with 1.
  simpl in H1.
  rewrite add_comm in H1.
  simpl in H1.
  assumption.
Qed.

Theorem specialize_example': forall n,
  (forall m, m * n = 0) ->
  n = 0.
Proof.
  intros n H1.
  specialize H1 with 1.
  simpl in H1.
  rewrite <- plus_n_O in H1.
  assumption.
Qed.

(* Varying the Induction Hypothesis *)