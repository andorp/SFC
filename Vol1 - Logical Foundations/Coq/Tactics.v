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

Theorem double_injective_FAILED : forall n m ,
  double n = double m ->
  n = m.
Proof.
  intros n m.
  induction n as [|n IH].
  - simpl.
    intros H1.
    destruct m as [| m'] eqn:E.
    + reflexivity.
    + discriminate H1.
  - intros H1.
    destruct m as [|m'] eqn:E.
    + discriminate H1.
    + f_equal.
Abort.

Theorem double_injective : forall n m,
  double n = double m ->
  n = m.
Proof.
  intros n.
  induction n as [| n IH].
  - simpl.
    intros m H1.
    destruct m as [| m].
    + reflexivity.
    + exfalso.
      discriminate H1.
  - intros m H1.
    destruct m as [| m].
    + exfalso.
      discriminate H1.
    + f_equal.
      apply IH.
      simpl in H1.
      injection H1 as H1.
      assumption.
Qed.

Theorem eqb_true : forall n m,
  n =? m = true -> n = m.
Proof.
  intros n.
  induction n as [|n IH].
  - intros m H1.
    destruct m as [| m].
    + reflexivity.
    + discriminate.
  - intros m H1.
    destruct m as [| m].
    + discriminate.
    + f_equal.
      apply IH.
      simpl in H1.
      assumption.
Qed.


Theorem plus_n_n_injective : forall n m,
  n + n = m + m ->
  n = m.
Proof.
  intros n.
  induction n as [|n IHn].
  - simpl.
    intros m H1.
    destruct m as [|m].
    + reflexivity.
    + discriminate.
  - simpl.
    intros m.
    destruct m as [|m].
    + simpl. intros H1. discriminate.
    + simpl.
      intros H1.
      rewrite IHn with m.
      1: reflexivity. 
      rewrite <- plus_n_Sm in H1.
      rewrite <- plus_n_Sm in H1.
      apply S_ in H1.
      apply S_injective in H1.
      assumption.
Qed.

Theorem double_injective_take2 : forall n m,
  double n = double m ->
  n = m.
Proof.
  intros n m.
  generalize dependent n.
Admitted.

Theorem nth_error_after_last: forall
  (n : nat) (X : Type) (l : list X),
  length l = n ->
  nth_error l n = None.
Proof.
  intros n X.
  induction n as [|n IHn] ; intros l.
  - destruct l as [|h l].
    + reflexivity.
    + discriminate.
  - destruct l as [|h l].
    + discriminate.
    + intro H1.
      simpl.
      rewrite IHn ; try reflexivity.
      simpl in H1.
      apply S_injective.
      assumption.
Qed.

(* TODO: Renaming *)
Theorem combine_split1 : forall X Y (l : list (X * Y)) ,
  combine (fst (split1 l)) (snd (split1 l)) = l.
Proof.
  intros X Y l.
  induction l as [|(x,y) l IH].
  - reflexivity.
  - simpl.
    rewrite IH.
    reflexivity.
Qed.

(* TODO: Use library *)
Lemma fst_inversion : forall X Y (z : (X * Y)) (x : X) (y : Y),
  z = (x,y) ->
  fst z = x.
Proof.
  intros X Y z x y H1.
  rewrite H1.
  reflexivity.
Qed.

(* TODO: Use library *)
Lemma snd_inversion : forall X Y (z : (X * Y)) (x : X) (y : Y),
  z = (x,y) ->
  snd z = y.
Proof.
  intros X Y z x y H1.
  rewrite H1.
  reflexivity.
Qed.

(* TODO: Renaming *)
Theorem combine_split2 : forall X Y (l : list (X * Y)) l1 l2,
  split1 l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y l l1 l2 H1.
  assert (H2 := H1).
  apply fst_inversion in H1.
  apply snd_inversion in H2.
  rewrite <- H1 , <- H2.
  apply combine_split1.
Qed.

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y l l1 l2 H1.
  apply combine_split2.
  rewrite <- H1.
  apply split1_split_eq.
Qed.
