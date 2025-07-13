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

(* TODO: Rename *)
Fixpoint split1 {X Y : Type} (l : list (X * Y)) : (list X) * (list Y) :=
  match l with
  | [] => ([],[])
  | ((x,y) :: xys) => (x::fst (split1 xys),y::snd (split1 xys))
  end.

(* TODO: Use lbirary function *)
Lemma tuple_inversion : forall X Y (z : (X * Y)) ,
  z = (fst z, snd z).
Proof.
  intros X Y z.
  destruct z as [x y].
  reflexivity.
Qed.

Lemma split1_split_eq : forall X Y (l : list (X * Y)) ,
  split1 l = split l.
Proof.
  intros X Y l.
  induction l as [|(x,y) l IH].
  - reflexivity.
  - simpl.
    rewrite (tuple_inversion _ _ (split l)).
    rewrite IH.
    reflexivity.
Qed.

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof. reflexivity. Qed.

(* Module OptionPlayground. *)

Inductive option (X:Type) : Type :=
  | Some (x : X)
  | None.

Arguments Some {X}.

Arguments None {X}.

(* End OptionPlayground. *)

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

Fixpoint flat_map {X Y: Type} (f: X -> list Y) (l: list X) : list Y :=
  match l with
  | []        => []
  | (x :: xs) => f x ++ flat_map f xs
  end.

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. reflexivity. Qed.

Definition
  option_map
    {X Y : Type}
    (f : X -> Y)
    (xo : option X) :
    option Y :=
  match xo with
  | None   => None
  | Some x => Some (f x)
  end.

Fixpoint fold {X Y: Type} (f : X -> Y -> Y) (l : list X) (b : Y) : Y :=
  match l with
  | nil    => b
  | h :: t => f h (fold f t b)
  end.

Definition constfun {X: Type} (x: X) : nat -> X :=
  fun (k:nat) => x.

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Example test_fold_length1 : fold_length [4;7;0] = 3.
Proof. reflexivity. Qed.

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
Proof.
  intros X l.
  induction l as [|x l IH].
  - reflexivity.
  - simpl.
    unfold fold_length.
    simpl.
    rewrite <- IH.
    reflexivity.
Qed.

Definition fold_map {X Y: Type} (f: X -> Y) (l: list X) : list Y
  := fold (fun x ys => f x :: ys) l [].

Theorem fold_map_correct : forall X Y (f : X -> Y) (l : list X),
  fold_map f l = map f l.
Proof.
  intros X Y f l.
  induction l as [|x l IH].
  - reflexivity.
  - simpl.
    unfold fold_map.
    simpl.
    rewrite <- IH.
    reflexivity.
Qed.

Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

Definition prod_uncurry' {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z := f (fst p) (snd p).

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z :=
  match p with
  | (x, y) => f x y
  end.

Theorem uncurry_curry :
  forall (X Y Z : Type)
  (f : X -> Y -> Z)
  x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  intros X Y Z f x y.
  reflexivity.
Qed.

Theorem uncurry_curry' :
  forall (X Y Z : Type)
  (f : X -> Y -> Z)
  x y,
  prod_curry (prod_uncurry' f) x y = f x y.
Proof.
  intros X Y Z f x y.
  reflexivity.
Qed.

Theorem curry_uncurry :
  forall (X Y Z : Type)
  (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
  intros X Y Z f p.
  destruct p as [x y].
  reflexivity.
Qed.

Fixpoint nth_errorx {X : Type} (l : list X) (n : nat) : option X :=
  match l with
  | []      => None
  | a :: l' => if n =? O then Some a else nth_errorx l' (pred n)
  end.

Module Church.

Definition cnat := forall X : Type, (X -> X) -> X -> X.

Definition zero : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => x.

Definition one : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f x.

Definition two : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f (f x).

Definition three : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f (f (f x)).

Definition zero' : cnat :=
  fun (X : Type) (succ : X -> X) (zero : X) => zero.

Definition one' : cnat :=
  fun (X : Type) (succ : X -> X) (zero : X) => succ zero.

Definition two' : cnat :=
  fun (X : Type) (succ : X -> X) (zero : X) => succ (succ zero).

Example zero_church_peano : zero nat S O = O.
Proof. reflexivity. Qed.

Example one_church_peano : one nat S O = S O.
Proof. reflexivity. Qed.

Example two_church_peano : two nat S O = S (S O).
Proof. reflexivity. Qed.

(* Definition cnat := forall X : Type, (X -> X) -> X -> X. *)
Definition scc (n : cnat) : cnat := fun X f x => f (n X f x).

Example scc_1 : scc zero = one.
Proof. 
  unfold scc.
  unfold zero.
  unfold one.
  reflexivity.
Qed.

Example scc_2 : scc one = two.
Proof. reflexivity. Qed.

Example scc_3 : scc two = three.
Proof. reflexivity. Qed.

Definition plus (n m : cnat) : cnat := fun X f x =>
  n X f (m X f x).

Example plus_1 : plus zero one = one.
Proof. reflexivity. Qed.

Example plus_2 : plus two three = plus three two.
Proof. reflexivity. Qed.

Example plus_3 :
  plus (plus two two) three = plus one (plus three three).
Proof. reflexivity. Qed.

(* n * m *)
Definition mult (n m : cnat) : cnat := fun X f x =>
  n X (m X f) x.

(*
n X f x => f (f (f ... x))
           ------ n ------

f (n X f x) => f (f (f (f ... x)))
*)

Example mult_1 : mult one one = one.
Proof. reflexivity. Qed.

Example mult_2 : mult zero (plus three three) = zero.
Proof. reflexivity. Qed.

Example mult_3 : mult two three = plus three three.
Proof. reflexivity. Qed.

Definition exp (n m : cnat) : cnat :=
  fun (X : Type) => m (X -> X) (n X).

Example exp_1 : exp two two = plus two two.
Proof. reflexivity. Qed.

Example exp_2 : exp three zero = one.
Proof. reflexivity. Qed.

Example exp_3 : exp three two = plus (mult two (mult two two)) one.
Proof. reflexivity. Qed.

End Church.

