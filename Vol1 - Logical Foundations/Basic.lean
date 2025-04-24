inductive Day where
  | monday
  | tuesday
  | wednedsay
  | thursday
  | friday
  | saturday
  | sunday
  deriving
    Repr,
    DecidableEq

-- @[simp] -- To make reduce with simp tactic.
def nextWorkingDay (d : Day) : Day :=
  match d with
  | Day.monday    => Day.tuesday
  | Day.tuesday   => Day.wednedsay
  | Day.wednedsay => Day.thursday
  | Day.thursday  => Day.friday
  | Day.friday    => Day.monday
  | Day.saturday  => Day.monday
  | Day.sunday    => Day.monday

-- example : nextWorkingDay (nextWorkingDay Day.saturday) = Day.tuesday := by
--   simp

example : nextWorkingDay (nextWorkingDay Day.saturday) = Day.tuesday := by
  rfl

namespace BoolExamples

  inductive Bool where
    | true
    | false
    deriving
      Repr,
      DecidableEq

  def negb (b : Bool) : Bool :=
    match b with
    | Bool.true  => Bool.false
    | Bool.false => Bool.true

  def andb (b1 b2 : Bool) : Bool :=
    match b1 with
    | Bool.true => b2
    | Bool.false => Bool.false

  def orb (b1 b2 : Bool) : Bool :=
    match b1 with
    | Bool.true => Bool.true
    | Bool.false => b2

  example : (orb Bool.true Bool.false) = Bool.true := by
    rfl

  infix:35 " && " => andb
  infix:30 " || " => orb

  #eval Bool.true && Bool.false

  example : (Bool.true || Bool.false) = Bool.true :=
    rfl

  def nandb (b1 b2 : Bool) : Bool :=
    negb (andb b1 b2)

  example : nandb Bool.true  Bool.false = Bool.true  := by rfl
  example : nandb Bool.false Bool.false = Bool.true  := by rfl
  example : nandb Bool.false Bool.true  = Bool.true  := by rfl
  example : nandb Bool.true  Bool.true  = Bool.false := by rfl

end BoolExamples

inductive RGB where
  | red
  | green
  | blue

inductive Color where
  | black
  | white
  | primary (p : RGB)

def monochrome (c : Color) : Bool :=
  match c with
  | Color.black     => true
  | Color.white     => true
  | Color.primary _ => false

def isred (c : Color) : Bool :=
  match c with
  | Color.primary RGB.red => true
  | _                     => false

inductive Bit where
  | b1
  | b0

inductive Nybble where
  | bits (x0 x1 x2 x3 : Bit)

theorem plusIdExample
  (n m : Nat)
  (h : n = m) :
  -------------
  n + n = m + m
:= by
    rw [h]

theorem plusIdExercise
  (n m o : Nat)
  (h1 : n = m)
  (h2 : m = o) :
  --------------
  n + m = m + o
:= by
  rw [h1]
  rw [h2]

theorem multN0M0
  (p q : Nat) :
  -------------
  (p * 0) + (q * 0) = 0
:= by
  simp

theorem multN0M0_2
  (p q : Nat) :
  -------------
  (p * 0) + (q * 0) = 0
:= by
  rw [Nat.mul_zero p]
  rw [Nat.mul_zero q]

theorem multN1
  (p : Nat) :
  -----------
  (p * 1) = p
:= by
  simp

theorem multN1_2
  (p : Nat) :
  -----------
  (p * 1) = p
:= by
  rw [Nat.mul_one p]

theorem plus1neq0
  (n : Nat) :
  -----------
  ((n + 1) != 0) = true
:= by
  cases n with
  | zero => simp
  | succ n => simp

theorem negInvolutive
  (b : Bool) :
  ------------
  !(!b) = b
:= by
  simp

theorem and_true_elim2
  (b c : Bool)
  (h1 : b && c = true) :
  ----------------------
  c = true
:= by
  cases b <;> cases c <;> simp [and] at h1 <;> try rfl

theorem and_true_elim3
  (b c : Bool)
  (h1 : b && c = true) :
  ----------------------
  c = true
:= by
  match b,c with
  | true, true  => rfl
  | true, false => contradiction
  | false,  x   => simp [and] at h1
