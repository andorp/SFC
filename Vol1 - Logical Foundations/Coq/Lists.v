From LF Require Export Induction.
Module NatList.

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

Fixpoint oddmembers (l:natlist) : natlist :=
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
Proof. reflexivity. Qed.