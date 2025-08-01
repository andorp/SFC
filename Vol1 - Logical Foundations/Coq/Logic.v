
(* Conjunction *)

Check (forall n m : nat, n + m = m + n) : Prop.

Check 2 = 2 : Prop.

Check 3 = 2 : Prop.

Check forall n : nat, n = 2 : Prop.

Definition plus_claim : Prop := 2 + 2 = 4.

Check plus_claim : Prop.

Theorem plus_claim_is_true :
  plus_claim.
Proof. reflexivity. Qed.

Definition is_three (n : nat) : Prop :=
  n = 3.

Check is_three : nat -> Prop.

Definition injective {A B} (f : A -> B) : Prop :=
  forall x y : A, f x = f y -> x = y.

Lemma succ_inj : injective S.
Proof.
  intros x y H. injection H as H1. apply H1.
Qed.

Check @eq : forall A : Type, A -> A -> Prop.

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  split.
  - reflexivity.
  - reflexivity.
Qed.

Check @conj : forall A B : Prop, A -> B -> A /\ B.

Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply conj.
  - reflexivity.
  - reflexivity.
Qed.

Example plus_is_O :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n.
  destruct n as [|n] ; intros m.
  - intros H1.
    split.
    + reflexivity.
    + simpl in H1.
      assumption.
  - destruct m as [|m] ; intros H1.
    + split. 2: reflexivity.
      rewrite <- plus_n_O in H1.
      assumption.
    + split ; simpl in H1 ; discriminate.
Qed.

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [H1 H2].
  subst.
  reflexivity.
Qed.

Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  intros n m H1.
  apply plus_is_O in H1.
  destruct H1 as [H1 H2].
  subst.
  reflexivity.
Qed.

Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q [H1 _].
  assumption.
Qed.

Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros P Q [_ H1].
  assumption.
Qed.

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q [H1 H2].
  split ; assumption.
Qed.

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [H1 [H2 H3]].
  split ; try split ; assumption.
Qed.

(* Disjunction *)

Lemma factor_is_O:
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  intros n m [H1 | H2].
  - subst. reflexivity.
  - subst.
    symmetry.
    apply mult_n_O.
Qed.

Lemma or_intro_l : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B H1.
  left.
  assumption.
Qed.

Lemma apply_h1 :
  forall (A B : Prop) , A /\ B -> B /\ A.
Proof.
  intros A B H1.
  split.
  - apply H1.
  - apply H1.
Qed.

Lemma mult_is_O :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n.
  destruct n as [|n] ; intros m.
  - intros H1.
    left.
    reflexivity.
  - destruct m as [|m] ; intros H1.
    + right. reflexivity.
    + simpl in H1.
      discriminate.
Qed.

Theorem or_commut : forall P Q : Prop,
  P \/ Q -> Q \/ P.
Proof.
  intros P Q [H1 | H2].
  - right. assumption.
  - left. assumption.
Qed.

(* Definition not (P:Prop) := P -> False. *)
(* Check not : Prop -> Prop. *)
(* Notation "~ x" := (not x) : type_scope. *)

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  intros P H1.
  destruct H1.
Qed.

Theorem not_implies_our_not : forall (P:Prop),
  ~ P -> (forall (Q:Prop), P -> Q).
Proof.
  intros P H1 Q H2.
  contradiction.
Qed.

(* Notation "x <> y" := (~(x = y)) : type_scope. *)

Theorem zero_not_one : 0 <> 1.
Proof.
  (* unfold not. *)
  intros H1.
  discriminate.
Qed.

Theorem not_False :
  ~ False.
Proof.
  intros H1.
  assumption.
Qed.


Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  intros P Q [H1 H2].
  contradiction.
Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  intros P H1 H2.
  contradiction.
Qed.

Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q H1 H2 H3.
  apply H2 , H1.
  assumption.
Qed.

Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  intros P [H1 H2].
  contradiction.
Qed.

Theorem de_morgan_not_or : forall (P Q : Prop),
    ~ (P \/ Q) -> ~P /\ ~Q.
Proof.
  intros P Q H1.
  split ; intros H2 ; apply H1.
  - left. assumption.
  - right. assumption.
Qed.

Lemma not_S_pred_n : ~(forall n : nat, S (pred n) = n).
Proof.
  intros H1.
  specialize (H1 0).
  discriminate.
Qed.

Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros b H1.
  destruct b ; try reflexivity.
  contradiction.
Qed.

Lemma True_is_true : True.
Proof. apply I. Qed.

Definition disc_fn (n: nat) : Prop :=
  match n with
  | O   => True
  | S _ => False
  end.

Theorem disc_example : forall n, ~ (O = S n).
Proof.
  intros n contra.
  assert (H : disc_fn 0).
    { simpl.
      apply I.
    }
  rewrite contra in H.
  simpl in H.
  apply H.
Qed.

Theorem nil_is_not_cons :
  forall X (x : X) (xs : list X), ~ (nil = cons x xs).
Proof.
  intros X x xs contra.
  discriminate.
Qed.
  
Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

(* Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity)
                      : type_scope. *)

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  (* WORKED IN CLASS *)
  intros P Q [HAB HBA].
  split ; assumption.
Qed.

Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  intros b.
  split ; intros H.
  - destruct b ; try reflexivity.
    contradiction.
  - destruct b.
    + discriminate.
    + intros C.
      discriminate.
Qed.

Lemma apply_iff_example1:
  forall P Q R : Prop, (P <-> Q) -> (Q -> R) -> (P -> R).
Proof.
  intros P Q R H1 H2 H3.
  apply H2, H1.
  assumption.
Qed.

Theorem iff_refl : forall P : Prop,
  P <-> P.
Proof.
  intros P.
  split ; intros H1 ; assumption.
Qed.

Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R H1 H2.
  split ; intro H3.
  - apply H2 , H1. assumption.
  - apply H1 , H2. assumption.
Qed.

Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R.
  split ; intro H1.
  - destruct H1 as [H1 | [H1 H2]].
    + split ; left  ; assumption.
    + split ; right ; assumption.
  - destruct H1 as [[H1 | H1] [H2 | H2]] ; try (left ; assumption).
    right. split ; assumption.
Qed.

(* Setoids and Logical Equivalence *)

Lemma mul_eq_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - apply mult_is_O.
  - apply factor_is_O.
Qed.

Theorem or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R.
  split.
  - intros [H1 | [H1 | H1]].
    + left. left. assumption.
    + left. right. assumption.
    + right. assumption.
  - intros [[H1 | H1] | H1].
    + left. assumption.
    + right. left. assumption.
    + right. right. assumption.
Qed.

From Coq Require Import Setoids.Setoid.

Lemma mul_eq_0_ternary :
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mul_eq_0.
  rewrite mul_eq_0.
  rewrite or_assoc.
  reflexivity.
Qed.

(* Existential Quantification *)

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S m => S (S (double m))
  end.

Definition Even x := exists n : nat, x = double n.

(* Check Even : nat -> Prop. *)

Lemma four_is_Even : Even 4.
Proof.
  exists 2.
  reflexivity.
Qed.

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n [m H1].
  exists (2 + m).
  assumption.
Qed.

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros X P H1 [x H2].
  apply H2, H1.
Qed.


Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q.
  split ; intros H1.
  - destruct H1 as [x [H1 | H1]].
    + left. exists x. assumption.
    + right. exists x. assumption.
  - destruct H1 as [[x H1] | [x H1]] ; exists x.
    + left. assumption.
    + right. assumption.
Qed.

From LF Require Export Basics.
From LF Require Export Tactics.

Theorem leb_plus_exists : forall n m,
  n <=? m = true -> exists x, m = n+x.
Proof.
  intros n.
  induction n as [|n IHn] ; intros m.
  - destruct m as [|m] ; intros H1.
    + exists 0. reflexivity.
    + exists (S m). reflexivity.
  - destruct m as [|m] ; intros H1.
    + discriminate.
    + simpl in H1.
      apply (IHn m) in H1.
      destruct H1 as [x H1].
      exists x.
      rewrite H1.
      reflexivity.
Qed.

Theorem plus_exists_leb : forall n m, (exists x, m = n+x) -> n <=? m = true.
Proof.
  intros n.
  induction n as [|n IHn] ; intros m.
  - destruct m as [|m] ; intros [x H1] ; reflexivity.
  - destruct m as [|m] ; intros [x H1].
    + discriminate.
    + apply IHn.
      exists x.
      simpl in H1.
      apply S_injective in H1.
      assumption.
Qed.

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x = x' \/ In x l'
  end.

Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  (* WORKED IN CLASS *)
  simpl.
  right.
  right.
  right.
  left.
  reflexivity.
Qed.

(* Programming with Propositions *)

Theorem In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l ->
    In (f x) (map f l).
Proof.
  intros A B f l.
  induction l as [|h l IHl] ; intros x H1.
  - contradiction.
  - destruct H1 as [H1 | H1].
    + left. subst. reflexivity.
    + right. apply IHl. assumption.
Qed.

Theorem In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <->
    exists x, f x = y /\ In x l.
Proof.
  intros A B f l y.
  split.
  - induction l as [|h l IHl] ; intros H1.
    + contradiction.
    + destruct H1 as [H1 | H1].
      * exists h.
        split.
        { symmetry. assumption. }
        { left. reflexivity. }
      * apply IHl in H1.
        destruct H1 as [x [H1 H2]].
        exists x.
        split.
        { assumption. }
        { right. assumption. }
  - induction l as [|h l IHl] ; intros H1.
    + destruct H1 as [x [_ H1]].
      contradiction.
    + destruct H1 as [x [H1 [H2 | H2]]].
      * left. subst. reflexivity.
      * right.
        apply IHl.
        exists x.
        split ; assumption.
Qed.

Theorem In_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros A l.
  induction l as [|x l IHl] ; intros l' a.
  - split ; intros H1.
    + right. assumption.
    + destruct H1 as [H1 | H1].
      * contradiction.
      * assumption.
  - split ; intros H1.
    + destruct H1 as [H1 | H1].
      * subst. left. left. reflexivity.
      * apply IHl in H1.
        destruct H1 as [H1 | H1].
        { left. right. assumption. }
        { right. assumption. }
    + destruct H1 as [[H1 | H1] | H1].
      * subst. left. reflexivity.
      * right. apply IHl. left. assumption.
      * right. apply IHl. right. assumption.
Qed.

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop :=
  match l with
  | [] => True
  | (h :: t) => P h /\ All P t
  end.

Theorem All_In :
  forall T (P : T -> Prop) (l : list T),
  (forall x, In x l -> P x) <-> All P l.
Proof.
  intros T P l.
  split.
  - induction l as [|h l IHl] ; intros H1.
    + apply I.
    + simpl.
      split.
      * apply H1. left. reflexivity.
      * apply IHl. 
        intros x H2.
        apply H1.
        right.
        assumption.
  - induction l as [|h l IHl] ; intros H1 x H2.
    + contradiction. (* H2 *)
    + destruct H2 as [H2 | H2].
      * subst. apply H1.
      * apply IHl. 2:assumption.
        apply H1.
Qed.

(* Check odd.
Check even. *)

Definition combine_odd_even (Podd Peven : nat -> Prop) (n : nat) : Prop :=
  match odd n with
  | true  => Podd  n
  | false => Peven n
  end.

Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
    (odd n = true -> Podd n)   ->
    (odd n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  intros Podd Peven n H1 H2.
  unfold combine_odd_even.
  destruct (odd n).
  - apply H1. reflexivity.
  - apply H2. reflexivity.
Qed.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    odd n = true ->
    Podd n.
Proof.
  intros Podd Peven n H1 H2.
  unfold combine_odd_even in H1.
  (* destruct (odd n) eqn:H3 in H1.
  - assumption.
  - rewrite H2 in H3. discriminate. *)
  rewrite H2 in H1.
  assumption.
Qed.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    odd n = false ->
    Peven n.
Proof.
  intros Podd Peven n H1 H2.
  unfold combine_odd_even in H1.
  rewrite H2 in H1.
  assumption.
Qed.

(* Applying Theorems to Arguments *)

(* Working with Decidable Properties *)

From LF Require Export Induction.

Lemma even_double : forall k, even (double k) = true.
Proof.
  intros k.
  induction k as [|k IH].
  - reflexivity.
  - assumption.
Qed.

Lemma even_double_conv : forall n, exists k,
  n = if even n then double k else S (double k).
Proof.
  intros n.
  induction n as [|n IHn].
  - exists 0. reflexivity.
  - destruct (even n) eqn:H1; destruct IHn as [k H2].
    + exists k.
      rewrite even_S.
      rewrite H1. simpl. rewrite H2. reflexivity.
    + exists (S k).
      rewrite even_S, H1.
      simpl.
      rewrite H2.
      reflexivity.
Qed.

Theorem even_bool_prop : forall n,
  even n = true <-> Even n.
Proof.
  intros n. split ; intros H1.
  - destruct (even_double_conv n) as [k H2].
    exists k.
    rewrite H1 in H2.
    assumption.
  - destruct H1 as [k H2].
    rewrite H2.
    rewrite even_double.
    reflexivity.
Qed.

Theorem eqb_eq : forall n1 n2 : nat,
  n1 =? n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split ; intros H1.
  - apply eqb_true. assumption.
  - subst. rewrite eqb_refl. reflexivity.
Qed.

Example not_even_1001' : ~(Even 1001).
Proof.
  intros H1.
  apply even_bool_prop in H1.
  simpl in H1.
  discriminate.
Qed.

Lemma plus_eqb_example : forall n m p : nat,
  n =? m = true -> n + p =? m + p = true.
Proof.
  intros n m p H1.
  apply eqb_true in H1.
  subst.
  apply eqb_refl.
Qed.

Theorem andb_true_iff : forall b1 b2:bool,
  b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  intros b1 b2. split ; destruct b1 , b2 ; intros H1 ; try discriminate.
  - split ; reflexivity.
  - reflexivity.
  - destruct H1 as [H1 H2]. discriminate.
  - destruct H1 as [H1 H2]. discriminate.
  - destruct H1 as [H1 H2]. discriminate.
Qed.

Theorem orb_true_iff : forall b1 b2,
  b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
  intros b1 b2. split ; destruct b1 , b2 ; intros H1 ; try reflexivity.
  - left. reflexivity.
  - left. reflexivity.
  - right. reflexivity.
  - discriminate.
  - destruct H1 as [H1 | H1] ; discriminate.
Qed.

Theorem eqb_neq : forall x y : nat,
  x =? y = false <-> x <> y.
Proof.
  intros x y.
  split ; intros H1.
  - intros H2.
    subst.
    rewrite eqb_refl in H1.
    discriminate.
  - destruct (x =? y) eqn:H2.
    + apply eqb_true in H2.
      contradiction.
    + reflexivity.
Qed.

Fixpoint eqb_list
  {A : Type}
  (eqb : A -> A -> bool)
  (l1 l2 : list A) : bool :=
  match l1, l2 with
  | []     , []      => true
  | (_::_) , []      => false
  | []     , (_::_)  => false
  | (x::xs), (y::ys) => (eqb x y) && (eqb_list eqb xs ys)
  (* | (x::xs), (y::ys) => if (eqb x y) then (eqb_list xs ys) else false *)
  end.

Theorem eqb_list_true_iff :
  forall A (eqb : A -> A -> bool),
  (forall a1 a2, eqb a1 a2 = true <-> a1 = a2) ->
  forall l1 l2, eqb_list eqb l1 l2 = true <-> l1 = l2.
Proof.
  intros A eqb Eq l1.
  induction l1 as [|h1 l1 IH1] ; intros l2.
  - destruct l2 as [|h2 l2].
    + split ; reflexivity.
    + split ; intros H1 ; discriminate.
  - induction l2 as [|h2 l2 IH2].
    + split ; intros H1 ; discriminate.
    + split ; intros H1.
      * simpl in H1.
        apply andb_true_iff in H1.
        destruct H1 as [H1 H2].
        apply IH1 in H2.
        apply Eq in H1.
        subst.
        reflexivity.
      * simpl.
        apply andb_true_iff.
        injection H1.
        intros H2 H3.
        apply Eq in H3.
        apply IH1 in H2.
        split ; assumption.
Qed.

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | []      => true
  | (x::xs) => test x && forallb test xs
  end.

Theorem forallb_true_iff : forall X test (l : list X),
  forallb test l = true <-> All (fun x => test x = true) l.
Proof.
  intros X test l.
  induction l as [|h l IH].
  - split ; intros H1.
    + apply I.
    + reflexivity.
  - split ; intros H1.
    + simpl in H1.
      apply andb_true_iff in H1.
      destruct H1 as [H1 H2].
      apply IH in H2.
      split ; assumption.
    + destruct H1 as [H1 H2].
      apply IH in H2.
      simpl.
      apply andb_true_iff.
      split ; assumption.
Qed.

(* The Logic of Coq *)