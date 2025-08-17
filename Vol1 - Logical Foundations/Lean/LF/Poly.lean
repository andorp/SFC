
inductive BoolList where
  | bnil
  | bcons (b : Bool) (l : BoolList)

inductive list (X : Type) where
  | nil
  | cons (x : X) (l : list X)

def repeate (X : Type) (x : X) (c : Nat) : list X :=
  match c with
  | .zero   => .nil
  | .succ c => .cons x (repeate X x c)

def repeati {X : Type} (x : X) (c : Nat) : list X :=
  match c with
  | .zero   => .nil
  | .succ c => .cons x (repeati x c)

def app {X : Type} (l1 l2 : list X) : list X :=
  match l1 with
  | .nil => l2
  | .cons h t => .cons h (app t l2)

def rev {X : Type} (l1 : list X) : list X :=
  match l1 with
  | .nil => .nil
  | .cons h t => app (rev t) (.cons h .nil)

def length {X : Type} (l : list X) : Nat :=
  match l with
  | .nil => .zero
  | .cons _ l => .succ (length l)

theorem appNilR
  (X : Type)
  (l : list X) :
  --------------
  app l .nil = l
:= by
  induction l with
  | nil =>
    rfl
  | cons h l ih =>
    simp [app]
    rw [ih]

theorem appAssoc
  (X : Type)
  (l1 l2 l3 : list X) :
  ---------------------
  app l1 (app l2 l3) = app (app l1 l2) l3
:= by
  induction l1 with
  | nil =>
    rfl
  | cons h l1 ih =>
    simp [app]
    rw [ih]

theorem appLength
  (X : Type)
  (l1 l2 : list X) :
  ------------------
  length (app l1 l2) = (length l1) + (length l2)
:= by
  induction l1 with
  | nil =>
    simp [app, length]
  | cons h l1 ih =>
    simp [app, length]
    rw [Nat.add_assoc, <- Nat.add_comm (length l2) 1, <- Nat.add_assoc]
    rw [ih]

theorem revAppDistr
  (X : Type)
  (l1 l2 : list X) :
  ------------------
  rev (app l1 l2) = app (rev l2) (rev l1)
:= by
  induction l1 with
  | nil =>
    simp [app,rev]
    rw [appNilR]
  | cons h l1 ih =>
    simp [app,rev]
    rw [ih, appAssoc]

theorem revInvolutive
  (X : Type)
  (l : list X) :
  --------------
  rev (rev l) = l
:= by
  induction l with
  | nil => rfl
  | cons h l ih =>
    simp [rev,app]
    rw [revAppDistr]
    simp [rev,app]
    rw [ih]

inductive Product (X : Type) (Y : Type) where
  | product (x : X) (y : Y)

def fst {X Y : Type} (p : Product X Y) : X :=
  match p with
  | .product x _ => x

def snd {X Y : Type} (p : Product X Y) : Y :=
  match p with
  | .product _ y => y

-- structure ProductS (X : Type) (Y : Type) where
--   fst : X
--   snd : Y

def combine {X Y : Type} (lx : list X) (ly : list Y) : list (Product X Y) :=
  match lx, ly with
  | .nil       , .nil       => .nil
  | _          , .nil       => .nil
  | .nil       , _          => .nil
  | .cons x lx , .cons y ly => .cons (.product x y) (combine lx ly)

def split {X Y : Type} (l : list (Product X Y)) : Product (list X) (list Y) :=
  match l with
  | .nil => .product .nil .nil
  | .cons (.product x y) l => match split l with
    | .product xs ys => .product (.cons x xs) (.cons y ys)

def splitDef {X Y : Type} (l : list (Product X Y)) : Product (list X) (list Y) :=
  match l with
  | .nil => .product .nil .nil
  | .cons (.product x y) l =>
      .product
        (.cons x (fst (splitDef l)))
        (.cons y (snd (splitDef l)))

theorem splitSplitDefEq
  (X Y : Type)
  (l : list (Product X Y)) :
  -------------------
  splitDef l = split l
:= by
  induction l with
  | nil =>
    simp [split,splitDef]
  | cons x l ih =>
    simp [split,splitDef]
    rw [ih]
    simp [fst,snd]

theorem tupleInversion
  (X Y : Type)
  (z : Product X Y) :
  -------------------
  z = .product (fst z) (snd z)
:= by
  simp [fst,snd]

inductive option (X : Type) : Type where
  | some (x : X)
  | none

def nthError {X : Type} (l : list X) (n : Nat) : option X :=
  match l with
  | .nil => .none
  | .cons x l => match n with
    | .zero => .some x
    | .succ n => nthError l n

def filter {X : Type} (pred : X -> Bool) (l : list X) : list X :=
  match l with
  | .nil => .nil
  | .cons x l =>
    if pred x
      then .cons x (filter pred l)
      else (filter pred l)

def map {X Y : Type} (f : X -> Y) (l : list X) : list Y :=
  match l with
  | .nil => .nil
  | .cons x l => .cons (f x) (map f l)

theorem mapApp
  (X Y : Type)
  (f : X -> Y)
  (l1 l2 : list X) :
  ------------------
  map f (app l1 l2) = app (map f l1) (map f l2)
:= by
  induction l1 with
  | nil =>
    rfl
  | cons x l1 ih =>
    simp [map, app]
    rw [ih]

theorem mapRev
  (X Y : Type)
  (f : X -> Y)
  (l : list X) :
  --------------
  map f (rev l) = rev (map f l)
:= by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp [map,rev]
    rw [<- ih]
    rw [mapApp]
    simp [map]

def flatMap
      {X Y : Type}
      (f : X -> list Y)
      (l : list X) :
    ----------------
    list Y
:= match l with
  | .nil => .nil
  | .cons x l => app (f x) (flatMap f l)

def optionMap
      {X Y : Type}
      (f : X -> Y)
      (o : option X) :
    option Y
:= match o with
  | .none => .none
  | .some x => .some (f x)

def fold
  {X Y : Type}
  (f : X -> Y -> Y)
  (l : list X)
  (b : Y) :
  ---------
  Y
:= match l with
  | .nil => b
  | .cons x l => f x (fold f l b)

def constFun
  {X : Type}
  (x : X) :
  ---------
  Nat -> X
:= λ _ => x

def foldLength
  {X : Type}
  (l : list X) :
  ---------
  Nat
:= fold (fun _ n => Nat.succ n) l 0

theorem foldLengthCorrect
  (X : Type)
  (l : list X) :
  --------------
  foldLength l = length l
:= by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp [foldLength,length,fold]
    rw [<- ih]
    simp [foldLength]

def foldMap
  {X Y : Type}
  (f : X -> Y)
  (l : list X) :
  --------------
  list Y
:= fold (fun x ys => .cons (f x) ys) l .nil

theorem foldMapCorrect
  (X Y : Type)
  (f : X -> Y)
  (l : list X) :
  --------------
  foldMap f l = map f l
:= by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp [foldMap, map, fold]
    rw [<- ih]
    simp [foldMap]

def productCurry
  {X Y Z : Type}
  (f : Product X Y -> Z)
  (x : X)
  (y : Y) :
  ---------
  Z
:= f (.product x y)

def productUncurry
  {X Y Z : Type}
  (f : X -> Y -> Z)
  (p : Product X Y) :
  -------------------
  Z
:= match p with
  | .product x y => f x y

theorem uncurryCurry
  (X Y Z : Type)
  (f : X -> Y -> Z)
  (x : X)
  (y : Y) :
  ---------
  productCurry (productUncurry f) x y = f x y
:= by rfl

theorem curryUncurry
  (X Y Z : Type)
  (f : Product X Y -> Z)
  (p : Product X Y) :
  -------------------
  productUncurry (productCurry f) p = f p
:= by rfl

def CNat  := forall (X : Type) , (X -> X) -> (X -> X)

def CZero : CNat := fun (X : Type) (_ : X -> X) (x : X) => x
def COne  : CNat := fun (X : Type) (f : X -> X) (x : X) => f x

theorem zeroChurchPeano : CZero Nat .succ .zero = .zero
:= by rfl

def succ (c : CNat) : CNat := fun X f x => f (c X f x)

def plus (n m : CNat) : CNat := fun X f x => n X f (m X f x)

def mult (n m : CNat) : CNat := fun X f x => n X (m X f) x

def exp (n m : CNat) : CNat := fun X => m (X -> X) (n X)
