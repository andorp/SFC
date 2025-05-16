From LF Require Export Induction.

Inductive natprod : Type :=
  | pair (n1 n2 : nat).

(* Check (pair 3 5) : natprod. *)

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.
Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

(* Compute (fst (pair 3 5)). *)

Notation "( x , y )" := (pair x y).

Definition fst' (p : natprod) : nat :=
  match p with
  | (x,y) => x
  end.

Definition snd' (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof. reflexivity. Qed.

Theorem surjective_pairing_stuck : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  simpl. (* Doesn't reduce anything! *)
Abort.

Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p. destruct p as [n m]. simpl. reflexivity.
Qed.

Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  intros p.
  destruct p as [x y].
  reflexivity.
Qed.

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).

Notation "[ ]" := nil.

Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].

Example notationTest1 : mylist1 = mylist2.
Proof. reflexivity. Qed.

Example notationTest2 : mylist1 = mylist3.
Proof. reflexivity. Qed.

Example notationTest3 : mylist2 = mylist3.
Proof. reflexivity. Qed.

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O        => nil
  | S count' => n :: (repeat n count')
  end.

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil    => O
  | h :: t => S (length t)
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil    => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.

Example test_app2: nil ++ [4;5] = [4;5].
Proof. reflexivity. Qed.

Example test_app3: [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.

Definition hd (default : nat) (l : natlist) : nat :=
  match l with
  | nil    => default
  | h :: t => h
  end.

Definition tl (l : natlist) : natlist :=
  match l with
  | nil    => nil
  | h :: t => t
  end.

Example test_hd1: hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.

Example test_hd2: hd 0 [] = 0.
Proof. reflexivity. Qed.

Example test_tl: tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.

Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
  | []     => []
  | 0 :: t =>      nonzeros t
  | h :: t => h :: nonzeros t
  end.

Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. reflexivity. Qed.

(* Fixpoint oddmembers (l:natlist) : natlist :=
  match l with
  | [] => []
  | n :: t =>
    match odd n with
    | true  => n :: oddmembers t
    | false =>      oddmembers t
    end
  end.

Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. reflexivity. Qed. *)

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1 , l2 with
  | []         , [] => []
  | []         , l2 => l2
  | l1         , [] => l1
  | (h1 :: t1) , (h2 :: t2) => h1 :: h2 :: alternate t1 t2
  end.

Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. reflexivity. Qed.

Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
Proof. reflexivity. Qed.

Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
Proof. reflexivity. Qed.

Example test_alternate4:
  alternate [] [20;30] = [20;30].
Proof. reflexivity. Qed.

Definition bag := natlist.

Fixpoint count (v : nat) (s : bag) : nat :=
  match s with
  | [] => 0
  | (h :: t) => if (Nat.eqb v h) then 1 + count v t else count v t
  end.

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof. reflexivity. Qed.

Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof. reflexivity. Qed.

Definition sum : bag -> bag -> bag := app.

Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. reflexivity. Qed.

Definition add (v : nat) (s : bag) : bag := v :: s.

Definition addx : nat -> bag -> bag := cons.

Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. reflexivity. Qed.

Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof. reflexivity. Qed.

Fixpoint member (v : nat) (s : bag) : bool :=
  match s with
  | [] => false
  | (h :: t) => if Nat.eqb h v then true else member v t
  end.

Example test_member1: member 1 [1;4;1] = true.
Proof. reflexivity. Qed.

Example test_member2: member 2 [1;4;1] = false.
Proof. reflexivity. Qed.

Fixpoint remove_one (v : nat) (s : bag) : bag :=
  match s with
  | [] => []
  | (h :: t) => if Nat.eqb h v then t else h :: remove_one v t
  end.

Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.

Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. reflexivity. Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
  match s with
  | [] => []
  | (h :: t) => if Nat.eqb h v then remove_all v t else h :: remove_all v t
  end.

Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.

Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. reflexivity. Qed.

Fixpoint included (s1 : bag) (s2 : bag) : bool :=
  match s1 with
  | [] => true
  | (h :: t) => member h s2 && included t (remove_one h s2)
  end.

Example test_included1: included [1;2] [2;1;4;1] = true.
Proof. reflexivity. Qed.

Example test_included2: included [1;2;2] [2;1;4;1] = false.
Proof. reflexivity. Qed.

Lemma nat_eqb_refl : forall (n : nat) ,
  Nat.eqb n n = Datatypes.true.
Proof.
  intros n.
  induction n as [|n IH].
  - reflexivity.
  - assumption. (* / apply IH *)
Qed.

Theorem add_inc_count : forall (x : nat) (b : bag) ,
  count x (add x b) = S (count x b).
Proof.
  intros x b.
  destruct b as [|h b] ; simpl.
  - rewrite nat_eqb_refl.
    reflexivity.
  - unfold add.
    rewrite nat_eqb_refl.
    reflexivity.
Qed.

Theorem nil_app : forall l : natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons n l' *)
    reflexivity.
Qed.

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite -> IHl1'. reflexivity.
Qed.

Theorem repeat_plus: forall c1 c2 n: nat,
    repeat n c1 ++ repeat n c2 = repeat n (c1 + c2).
Proof.
  intros c1 c2 n.
  induction c1 as [|c1 IH].
  - reflexivity.
  - simpl.
    rewrite IH.
    reflexivity.
Qed.

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | []     => []
  | h :: t => rev t ++ [h]
  end.

Example test_rev1: rev [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.

Example test_rev2: rev [] = [].
Proof. reflexivity. Qed.

 Theorem rev_length_firsttry : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - (* l = n :: l' *)
    (* This is the tricky case.  Let's begin as usual
       by simplifying. *)
    simpl.
    (* Now we seem to be stuck: the goal is an equality
       involving ++, but we don't have any useful equations
       in either the immediate context or in the global
       environment!  We can make a little progress by using
       the IH to rewrite the goal... *)
    rewrite <- IHl'.
    (* ... but now we can't go any further. *)
Abort.

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros l1 l2.
  induction l1 as [|h l1 IH].
  - reflexivity.
  - simpl.
    rewrite IH.
    reflexivity.
Qed.

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l.
  induction l as [|h l IH].
  - reflexivity.
  - simpl.
    rewrite (app_length (rev l) [h]).
    rewrite IH.
    simpl.
    rewrite <- (plus_n_Sm (length l)).
    rewrite <- plus_n_O.
    reflexivity.
Qed.

Theorem app_nil_r : forall (l : natlist) ,
  l ++ [] = l.
Proof.
  intros l.
  induction l as [|h l IH].
  - reflexivity.
  - simpl.
    rewrite IH.
    reflexivity.
Qed.

Theorem rev_app_distr : forall (l1 l2 : natlist) ,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros l1 l2.
  induction l1 as [|h l1 IH].
  - simpl.
    rewrite (app_nil_r (rev l2)).
    reflexivity.
  - simpl.
    rewrite IH.
    rewrite (app_assoc (rev l2) (rev l1) [h]).
    reflexivity.
Qed.

Lemma rev_app : forall (h : nat) (l : natlist),
  rev (h :: l) = rev l ++ [h].
Proof.
  intros h l.
  induction l as [|x l IH] ; reflexivity.
Qed.

Theorem rev_involutive : forall (l : natlist),
  rev (rev l) = l.
Proof.
  intros l.
  induction l as [|h l IH].
  - reflexivity.
  - simpl.
    rewrite (rev_app_distr (rev l) [h]).
    simpl.
    rewrite IH.
    reflexivity.
Qed.

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros l1 l2 l3 l4.
  induction l1 as [|h l1 IH].
  - simpl.
    rewrite app_assoc.
    reflexivity.
  - simpl.
    rewrite <- IH.
    reflexivity.
Qed.

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1 l2.
  induction l1 as [|h l1 IH].
  - simpl.
    reflexivity.
  - simpl.
    destruct h.
    + apply IH.
    + simpl.
      rewrite IH.
      reflexivity.
Qed.

Fixpoint eqblist (l1 l2 : natlist) : Datatypes.bool :=
  match l1 , l2 with
  | []         , []         => true
  | ( _ ::  _) , []         => false
  | []         , ( _ ::  _) => false
  | (h1 :: t1) , (h2 :: t2) => Nat.eqb h1 h2 && eqblist t1 t2
  end.

Example test_eqblist2 :
  eqblist [1;2;3] [1;2;3] = true.
Proof. reflexivity. Qed.

Example test_eqblist3 :
  eqblist [1;2;3] [1;2;4] = false.
Proof. reflexivity. Qed.

Theorem eqblist_refl : forall (l:natlist),
  true = eqblist l l.
Proof.
  intros l.
  induction l as [|h l IH].
  - reflexivity.
  - simpl.
    rewrite (nat_eqb_refl h).
    simpl.
    apply IH.
Qed.
