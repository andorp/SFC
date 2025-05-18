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
