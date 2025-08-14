import LF.Induction

structure Natprod where
  x : Nat
  y : Nat
  deriving
    Repr,
    DecidableEq

notation "[|" x ", " y "|]" => Natprod.mk x y

def fst (p : Natprod) : Nat := p.x

def snd (p : Natprod) : Nat := p.y

theorem surjecive_pairing
  (n m : Nat) :
  -------------
  [| n , m |] = [|fst [|n,m|], snd [|n,m|] |]
:= by rfl

theorem surjective_pairing_stuck -- or not :D --
  (p : Natprod) :
  p = [| fst p, snd p |]
:= by
  rfl

def swapPair (p : Natprod) : Natprod :=
  match p with
  | Natprod.mk x y => Natprod.mk y x

theorem snd_fst_is_swap
  (p : Natprod) :
  --------------------------------
  [| snd p , fst p |] = swapPair p
:= by rfl

theorem fst_sawp_is_snd
  (p : Natprod) :
  ---------------
  fst (swapPair p) = snd p
:= by rfl

inductive NatList : Type where
  | nil
  | cons (n : Nat) (l : NatList)

notation "[" "]" => NatList.nil
notation x ";" l => NatList.cons x l

-- def myList1 : NatList := 1 :: 2 :: []

def repeatn (n count : Nat) : NatList :=
  match count with
  | 0 => []
  | count' + 1 => n ; (repeatn n count')

def length : NatList -> Nat
  | []       => 0
  | (_ ; t) => length t + 1

def app : NatList -> NatList -> NatList
  | []      , ys => ys
  | (h ; t) , ys => h ; app t ys

-- notation x "++" y => (app x y)
infix:60 " ++ " => app

def hd (d : Nat) (l : NatList) :=
  match l with
  | []      => d
  | (h ; _) => h

def tl : NatList -> NatList
  | []      => []
  | (_ ; t) => t

def nonZeros : NatList -> NatList
  | [] => []
  | (0 ; xs) => nonZeros xs
  | (x ; xs) => x ; nonZeros xs

-- Not example as there is some _ bind resolution problem.
theorem testNonZeros :
  nonZeros (0;1;0;2;3;0;0;NatList.nil) = (1;2;3;NatList.nil)
:= by rfl

def oddMembers : NatList -> NatList
  | [] => []
  | x ; xs => if x % 2 = 1 then x ; oddMembers xs else oddMembers xs

theorem testOddMembers :
  oddMembers (0;1;0;2;3;0;0;[]) = 1;3;[]
:= by rfl

def countOddMembers : NatList -> Nat
  | []     => 0
  | x ; xs => if x % 2 = 1 then 1+countOddMembers xs else countOddMembers xs

theorem testCountOddMembers1:
  countOddMembers (1;0;3;1;4;5;[]) = 4
:= by rfl

theorem testCountOddMembers2:
  countOddMembers (0;2;4;[]) = 0
:= by rfl

theorem testCountOddMembers3:
  countOddMembers [] = 0
:= by rfl

def alternate : NatList -> NatList -> NatList
  | [] , l2 => l2
  | l1 , [] => l1
  | (h1 ; t1) , (h2 ; t2) => h1 ; h2 ; alternate t1 t2

theorem testAlternate1:
  alternate (1;2;3;[]) (4;5;6;[]) = (1;4;2;5;3;6;[])
:= by rfl

def Bag := NatList

def count (v : Nat) (s : Bag) : Nat :=
  match s with
  | []      => 0
  | (h ; t) => if h == v then Nat.succ (count v t) else count v t

def sum : Bag -> Bag -> Bag := app

def add (v : Nat) (s : Bag) : Bag := v ; s

def member (v : Nat) (s : Bag) : Bool :=
  match s with
  | [] => False
  | (h ; t) => if h == v then True else member v t

def removeOne (v : Nat) (s : Bag) : Bag :=
  match s with
  | [] => []
  | (h ; t) => if h == v then t else h ; removeOne v t

def removeAll (v : Nat) (s : Bag) : Bag :=
  match s with
  | [] => []
  | (h ; t) => if h == v then removeAll v t else h ; removeAll v t

def included (s1 : Bag) (s2 : Bag) : Bool :=
  match s1 with
  | [] => True
  | (h ; t) => member h s2 && included t (removeOne h s2)

theorem addIncCount
  (x : Nat)
  (b : Bag) :
  -----------
  count x (add x b) = .succ (count x b)
:= by
  cases b <;> simp [add, count]

theorem nilApp
  (l : NatList) :
  ---------------
  [] ++ l = l
:= by rfl

theorem predTailLength
  (l : NatList) :
  ---------------
  Nat.pred (length l) = length (tl l)
:= by cases l <;> rfl

theorem appAssoc
  (l1 l2 l3 : NatList) :
  ----------------------
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)
:= by
  induction l1 with
  | nil => rfl
  | cons x l1 ih =>
    simp [app]
    rw [ih]

theorem repeatPlus
  (c1 c2 n : Nat) :
  -----------------
  (repeatn n c1) ++ (repeatn n c2) = repeatn n (c1 + c2)
:= by
  induction c1 with
  | zero =>
    simp [repeatn,app]
  | succ n ih =>
    simp [repeatn,app]
    rw [ih]
    simp [Nat.succ_add,repeatn]

def rev (l : NatList) : NatList :=
  match l with
  | [] => .nil
  | h ; t => (rev t) ++ (h ; [])

theorem appLength
  (l1 l2 : NatList) :
  -------------------
  length (l1 ++ l2) = (length l1) + (length l2)
:= by
  induction l1 with
  | nil =>
    simp [app,length]
  | cons h l1 ih =>
    simp
      [ app
      , length
      , Nat.add_assoc
      , Nat.add_comm
      , <- Nat.add_assoc
      ]
    rw [Nat.add_comm, ih]

theorem revLength
  (l : NatList) :
  ---------------
  length (rev l) = length l
:= by
  induction l with
  | nil =>
    simp [rev]
  | cons h l ih =>
    simp [rev,length,appLength]
    rw [ih]

theorem appNilR
  (l : NatList) :
  ---------------
  l ++ [] = l
:= by
  induction l with
  | nil => rfl
  | cons h l ih =>
    rw [app, ih]

theorem revAppDist
  (l1 l2 : NatList) :
  -------------------
  rev (l1 ++ l2) = (rev l2) ++ (rev l1)
:= by
  induction l1 with
  | nil =>
    simp [app, rev, appNilR]
  | cons h l1 ih =>
    simp [app,rev]
    rw [ih,appAssoc]

theorem revApp
  (h : Nat)
  (l : NatList) :
  ---------------
  rev (h ; l) = rev l ++ (h ; [])
:= by cases l <;> simp [rev]

theorem revInvolutive
  (l : NatList) :
  ---------------
  rev (rev l) = l
:= by
  induction l with
  | nil =>
    simp [rev]
  | cons h l ih =>
    simp [rev,revAppDist,app]
    rw [ih]

theorem appAssoc4
  (l1 l2 l3 l4 : NatList) :
  -------------------------
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4
:= by
  induction l1 with
  | nil =>
    simp [app, appAssoc]
  | cons h l1 ih =>
    simp [app]
    rw [<- ih]

theorem nonZerosAppDist
  (l1 l2 : NatList) :
  -------------------
  nonZeros (l1 ++ l2) = (nonZeros l1) ++ (nonZeros l2)
:= by
  induction l1 with
  | nil =>
    simp [app, nonZeros]
  | cons h l1 ih =>
    simp [app]
    cases h with
    | zero =>
      simp [nonZeros, ih]
    | succ h =>
      simp [nonZeros, ih]
      rfl

def eqList (l1 l2 : NatList) : Bool :=
  match l1 , l2 with
  | []        , []        => true
  | (_ ; _)   , []        => false
  | []        , (_ ; _)   => false
  | (h1 ; t1) , (h2 ; t2) => h1 == h2 && eqList t1 t2

theorem eqListRefl
  (l : NatList) :
  ---------------
  true = eqList l l
:= by
  induction l with
  | nil =>
    rfl
  | cons h l ih =>
    simp [eqList]
    rw [ih]

theorem involutionInjective
  (f : Nat -> Nat)
  (hInv : (forall (n : Nat), n = f (f n))) :
  forall (n1 n2 : Nat), f n1 = f n2 -> n1 = n2
:= by
  intros n1 n2 h
  rw [hInv n1, hInv n2, h]

theorem revInjective
  (l1 l2 : NatList)
  (h : rev l1 = rev l2) :
  -----------------------
  l1 = l2
:= by
  rw [<- revInvolutive l1]
  rw [<- revInvolutive l2]
  rw [h]

inductive NatOption where
  | some (n : Nat)
  | none

def nthError (l : NatList) (n : Nat) : NatOption :=
  match l with
  | .nil => .none
  | .cons h t => match n with
    | .zero => .some h
    | .succ n => nthError t n

def optionElim (d : Nat) (o : NatOption) : Nat :=
  match o with
  | .some n => n
  | .none   => d

def hdError (l : NatList) : NatOption :=
  match l with
  | .nil      => .none
  | .cons h _ => .some h

theorem optionElimHd
  (l : NatList)
  (d : Nat)    :
  --------------
  hd d l = optionElim d (hdError l)
:= by
  induction l with
  | nil =>
    rfl
  | cons h l ih =>
    simp [hd,hdError,optionElim]

inductive Idx where
  | idx (n : Nat)
  deriving
    DecidableEq

theorem eqIdxRefl
  (x : Idx) :
  (x == x) = true
:= by
  cases x
  simp

inductive PartialMap where
  | empty
  | record (i : Idx) (v : Nat) (m : PartialMap)

def update
  (d : PartialMap)
  (x : Idx)
  (v : Nat)
:=
  PartialMap.record x v d

def find (x : Idx) (d : PartialMap) : NatOption :=
  match d with
  | .empty => .none
  | .record y v d' => if x == y then .some v else find x d'

theorem updateEq
  (d : PartialMap)
  (x : Idx)
  (v : Nat)       :
  -----------------
  find x (update d x v) = .some v
:= by
  simp [update, find]

theorem updateNEq
  (d  : PartialMap)
  (x  : Idx)
  (o  : Nat)
  (H1 : (x == y) = false) :
  -----------------
  find x (update d y o) = find x d
:= by
  simp [update, find]
  intros H2
  simp at H1
  contradiction
