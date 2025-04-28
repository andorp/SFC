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

  -- #eval Bool.true && Bool.false

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

theorem identity_fn_applied_twice
  (f : Bool -> Bool)
  (h : forall (x : Bool), f x = x)
  (b : Bool) :
  --------------------------------
  f (f b) = b
:= by
  rw [h]
  rw [h]

theorem manual_grade_for_negative_fn_applied_twice
  (b : Bool) :
  !(!b) = b
:= by
  simp

theorem andb_eq_orb1
  (b c : Bool)
  (h : (b && c) = (b || c)) :
  ---------------------------
  b = c
:= by
  match b,c with
  | true , true  => rfl
  | true , false => contradiction
  | false, true  => simp [and,or] at h
  | false, false => rfl

theorem andb_eq_orb2
  (b c : Bool)
  (h : (b && c) = (b || c)) :
  ---------------------------
  b = c
:= by
  cases b <;> cases c <;> try rfl
  simp [and,or] at h
  contradiction

inductive Letter where
  | F | D | C | B | A
  deriving
    Repr,
    DecidableEq,
    Ord

inductive Modifier where
  | Minus | Natural | Plus
  deriving
    Repr,
    DecidableEq,
    Ord

inductive Grade where
  | Grade (l : Letter) (m : Modifier)
  deriving
    Repr,
    DecidableEq,
    Ord

inductive Comparison where
  | Lt | Eq | Gt
  deriving
    Repr,
    DecidableEq

def letterComparison0 (l1 l2 : Letter) : Comparison :=
  match l1 with
  | Letter.A => match l2 with
    | Letter.A => Comparison.Eq
    | _        => Comparison.Gt
  | Letter.B => match l2 with
    | Letter.A => Comparison.Lt
    | Letter.B => Comparison.Eq
    | _        => Comparison.Gt
  | Letter.C => match l2 with
    | Letter.A
    | Letter.B => Comparison.Lt
    | Letter.C => Comparison.Eq
    | _        => Comparison.Gt
  | Letter.D => match l2 with
    | Letter.A
    | Letter.B
    | Letter.C => Comparison.Lt
    | Letter.D => Comparison.Eq
    | _        => Comparison.Gt
  | Letter.F => match l2 with
    | Letter.F => Comparison.Eq
    | _        => Comparison.Lt

def letterComparison (l1 l2 : Letter) : Ordering := compare l1 l2

theorem letter_comparison_eq
  (l : Letter) :
  --------------
  letterComparison l l = Ordering.eq
:= by
  cases l <;> try rfl

def modifierComparison (m1 m2 : Modifier) : Ordering := compare m1 m2

def gradeComparison (g1 g2 : Grade) : Ordering := compare g1 g2

example :
  (gradeComparison
    (Grade.Grade Letter.A Modifier.Minus)
    (Grade.Grade Letter.B Modifier.Plus)
  = Ordering.gt)
:= by
  rfl

example :
  (gradeComparison
    (Grade.Grade Letter.A Modifier.Minus)
    (Grade.Grade Letter.A Modifier.Plus)
  = Ordering.lt)
:= by
  rfl

example :
  (gradeComparison
    (Grade.Grade Letter.F Modifier.Plus)
    (Grade.Grade Letter.F Modifier.Plus)
  = Ordering.eq)
:= by
  rfl

example :
  (gradeComparison
    (Grade.Grade Letter.B Modifier.Minus)
    (Grade.Grade Letter.C Modifier.Plus)
  = Ordering.gt)
:= by
  rfl

def lowerLetter (l : Letter) : Letter :=
  match l with
  | Letter.A => Letter.B
  | Letter.B => Letter.C
  | Letter.C => Letter.D
  | Letter.D => Letter.F
  | Letter.F => Letter.F

theorem lowerLetterIsF :
  -------------------------------
  lowerLetter Letter.F = Letter.F
:= by
  rfl

theorem lowerLetterLowers
  (l : Letter)
  (h : compare Letter.F l = Ordering.lt) :
  ----------------------------------------
  letterComparison (lowerLetter l) l = Ordering.lt
:= by
  cases l <;> try rfl
  contradiction

def lowerGrade (g : Grade) : Grade :=
  match g with
  | Grade.Grade Letter.F Modifier.Minus => Grade.Grade Letter.F Modifier.Minus
  | Grade.Grade l m => match m with
    | Modifier.Plus    => Grade.Grade              l  Modifier.Natural
    | Modifier.Natural => Grade.Grade              l  Modifier.Minus
    | Modifier.Minus   => Grade.Grade (lowerLetter l) Modifier.Plus

example :
  lowerGrade (Grade.Grade Letter.A Modifier.Plus)
  =
  Grade.Grade Letter.A Modifier.Natural
:= by
  rfl

example :
  lowerGrade (Grade.Grade Letter.A Modifier.Natural)
  =
  Grade.Grade Letter.A Modifier.Minus
:= by
  rfl

example :
  lowerGrade (Grade.Grade Letter.A Modifier.Minus)
  =
  Grade.Grade Letter.B Modifier.Plus
:= by
  rfl

example :
  lowerGrade (Grade.Grade Letter.F Modifier.Natural)
  =
  Grade.Grade Letter.F Modifier.Minus
:= by
  rfl

example :
  lowerGrade (Grade.Grade Letter.F Modifier.Minus)
  =
  Grade.Grade Letter.F Modifier.Minus
:= by
  rfl

example :
  (lowerGrade (lowerGrade (Grade.Grade Letter.B Modifier.Minus)))
  =
  Grade.Grade Letter.C Modifier.Natural
:= by
  rfl

example :
  (lowerGrade (lowerGrade (lowerGrade (Grade.Grade Letter.B Modifier.Minus))))
  =
  Grade.Grade Letter.C Modifier.Minus
:= by
  rfl

theorem lowerGradeLowers
  (g : Grade)
  (h : gradeComparison (Grade.Grade Letter.F Modifier.Minus) g = Ordering.lt) :
  -----------------------------------------------------------------------------
  gradeComparison (lowerGrade g) g = Ordering.lt
:= by
  cases g with
  | Grade l m =>
      cases l <;> cases m <;> try rfl
      contradiction

inductive Grd where
  | GrdDot (l : Letter) (m : Modifier)
  deriving
    Repr,
    DecidableEq,
    Ord

namespace Grd

def letter (g : Grd) : Letter :=
  match g with
  | GrdDot l _ => l

def modifier (g : Grd) : Modifier :=
  match g with
  | GrdDot _ m => m

end Grd

-- usage
-- #eval (Grd.GrdDot Letter.A Modifier.Plus).letter  -- → Letter.A

structure GradeX where
  letter   : Letter
  modifier : Modifier
  deriving
    Repr,
    DecidableEq

structure SuperGradeX extends GradeX where
  annotation : String
  deriving
    Repr,
    DecidableEq

instance : Coe SuperGradeX GradeX where
  coe g := { letter := g.letter , modifier := g.modifier }

def applyLatePolicy (lateDays : Nat) (g : Grade) : Grade :=
  if decide (lateDays < 9) then g
  else if decide (lateDays < 17) then lowerGrade g
  else if decide (lateDays < 21) then lowerGrade (lowerGrade g)
  else lowerGrade (lowerGrade (lowerGrade g))

theorem noPenalityForMostlyOnTime
  (lateDays : Nat)
  (g : Grade)
  (h : (lateDays < 9)) :
  -------------------------------
  applyLatePolicy lateDays g = g
:= by
  unfold applyLatePolicy
  simp [h]

theorem GradeLoweredOnce
  (lateDays : Nat)
  (g : Grade)
  (h1 : decide (lateDays < 9) = false)
  (h2 : decide (lateDays < 17) = true) :
  ------------------------
  applyLatePolicy lateDays g = lowerGrade g
:= by
  unfold applyLatePolicy
  rewrite [h1]
  rewrite [h2]
  simp

inductive Bin where
  | z
  | b0 (b : Bin)
  | b1 (b : Bin)
  deriving
    Repr,
    DecidableEq

def incr : Bin -> Bin
  | Bin.z    => Bin.b1 Bin.z
  | Bin.b0 b => Bin.b1 b
  | Bin.b1 b => Bin.b0 (incr b)

def binToNat : Bin -> Nat
  | Bin.z    => 0
  | Bin.b0 b =>     2 * (binToNat b)
  | Bin.b1 b => 1 + 2 * (binToNat b)

theorem binToNatIncr
  (b : Bin) :
  -----------
  binToNat (incr b) = Nat.succ (binToNat b)
:= by
  induction b with
  | z =>
      rfl
  | b0 x ih =>
      simp [incr, binToNat, Nat.add_comm 1 (2 * binToNat x)]
  | b1 x ih =>
      simp [incr, binToNat]
      rewrite [ih]
      simp [Nat.mul_add]
      simp [Nat.add_comm 1 (2 * binToNat x)]
