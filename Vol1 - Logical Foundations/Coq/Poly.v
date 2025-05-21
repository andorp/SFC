From LF Require Export Lists.

Inductive boollist : Type :=
  | bool_nil
  | bool_cons (b : bool) (l : boollist).

Inductive list (X:Type) : Type :=
  | nil
  | cons (x : X) (l : list X).

(* Check (cons nat 2 (cons nat 1 (nil nat)))
      : list nat. *)

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
  end.

(* Example test_repeat1 :
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).

Example test_repeat2 :
  repeat bool false 1 = cons bool false (nil bool). *)

Fixpoint repeat' X x count : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat' X x count')
  end.

(* Check repeat'
  : forall X : Type, X -> nat -> list X.

Check repeat
  : forall X : Type, X -> nat -> list X. *)

Fixpoint repeat'' X x count : list X :=
  match count with
  | 0 => nil _
  | S count' => cons _ x (repeat'' _ x count')
  end.

Arguments nil {X}.
Arguments cons {X}.
Arguments repeat {X}.

Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0        => nil
  | S count' => cons x (repeat''' x count')
  end.

Inductive list' {X:Type} : Type :=
  | nil'
  | cons' (x : X) (l : list').

Fixpoint app {X : Type} (l1 l2 : list X) : list X :=
  match l1 with
  | nil      => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil      => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil       => 0
  | cons _ l' => S (length l')
  end.

Fail Definition mynil := nil.

Definition mynil : list nat := nil.

Definition mynil' := @nil nat.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).

Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Definition list123''' := [1; 2; 3].

Theorem app_nil_r : forall (X:Type), forall (l:list X),
  l ++ [] = l.
Proof.
  intros X l.
  induction l as [|x l IH].
  - reflexivity.
  - simpl.
    rewrite IH.
    reflexivity.
Qed.

Theorem app_assoc : forall A (l m n:list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros A l m n.
  induction l as [|x l IH].
  - reflexivity.
  - simpl.
    rewrite IH.
    reflexivity.
Qed.

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros X l1 l2.
  induction l1 as [|x l IH].
  - reflexivity.
  - simpl.
    rewrite IH.
    reflexivity.
Qed.

Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros X l1 l2.
  induction l1 as [|x l1 IH].
  - simpl.
    symmetry.
    apply app_nil_r.
  - simpl.
    rewrite IH.
    symmetry.
    apply app_assoc.
Qed.

Theorem rev_involutive : forall (X : Type) (l : list X),
  rev (rev l) = l.
Proof.
  intros X l.
  induction l as [|x l IH].
  - reflexivity.
  - simpl.
    rewrite rev_app_distr.
    simpl.
    rewrite IH.
    reflexivity.
Qed.

Inductive prod (X Y : Type) : Type :=
| pair (x : X) (y : Y).

Arguments pair {X} {Y}.

Notation "( x , y )" := (pair x y).

Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X * Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

Fixpoint split {X Y : Type} (l : list (X * Y)) : (list X) * (list Y) :=
  match l with
  | [] => ([],[])
  | ((x,y) :: xys) =>
    match split xys with
    | (xs,ys) => (x::xs,y::ys)
    end
  end.

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof. reflexivity. Qed.

Module OptionPlayground.

Inductive option (X:Type) : Type :=
  | Some (x : X)
  | None.

Arguments Some {X}.

Arguments None {X}.

End OptionPlayground.

Fixpoint nth_error {X : Type} (l : list X) (n : nat)
                   : option X :=
  match l with
  | nil => None
  | a :: l' =>
    match n with
    | O    => Some a
    | S n' => nth_error l' n'
    end
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.

Example test_nth_error2 : nth_error [[1];[2]] 1 = Some [2].
Proof. reflexivity. Qed.

Example test_nth_error3 : nth_error [true] 2 = None.
Proof. reflexivity. Qed.


Definition hd_error {X : Type} (l : list X) : option X :=
  match l with
  | []       => None
  | (x :: _) => Some x
  end.

Example test_hd_error1 : hd_error [1;2] = Some 1.
Proof. reflexivity. Qed.

Example test_hd_error2 : hd_error [[1];[2]] = Some [1].
Proof. reflexivity. Qed.

Definition doit3times {X : Type} (f : X -> X) (n : X) : X :=
  f (f (f n)).

Fixpoint filter {X:Type} (test: X -> bool) (l:list X) : list X :=
  match l with
  | []     => []
  | h :: t =>
    if test h then h :: (filter test t)
    else filter test t
  end.

Example test_anon_fun':
  doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity. Qed.

Fixpoint map {X Y : Type} (f : X -> Y) (l : list X) : list Y :=
  match l with
  | []     => []
  | h :: t => (f h) :: (map f t)
  end.

Example test_map1: map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.

Lemma map_app : forall (X Y : Type) (f : X -> Y) (l1 l2 : list X),
  map f (l1 ++ l2) = map f l1 ++ map f l2.
Proof.
  intros X Y f l1 l2.
  induction l1 as [|x l1 IH].
  - reflexivity.
  - simpl.
    rewrite IH.
    reflexivity.
Qed.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros X Y f l.
  induction l as [|x l IH].
  - reflexivity.
  - simpl.
    rewrite <- IH.
    apply map_app.
Qed.
