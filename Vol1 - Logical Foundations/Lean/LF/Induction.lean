import LF.Basic

theorem add_0_r
  (n : Nat) :
  -----------
  n + 0 = n
:= by
  cases n <;> rfl

theorem mul_0_r
  (n : Nat) :
  -----------
  (n * 0 = 0)
:= by
  cases n <;> rfl

theorem plus_n_Sm
  (n m : Nat) :
  -------------
  Nat.succ (n + m) = n + Nat.succ m
:= by
  cases n <;> rfl

theorem add_comm
  (n m : Nat) :
  -------------
  n + m = m + n
:= by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      simp [<- Nat.add_assoc m n 1]
      rw   [<- ih]
      rw   [Nat.add_assoc]
      rw   [<- Nat.succ_eq_one_add]
      rw   [Nat.add_one]
      rw   [plus_n_Sm]

theorem add_assoc
  (n m p : Nat) :
  ---------------
  n + (m + p) = (n + m) + p
:= by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      simp [Nat.succ_add]
      rw [ih]

def double (n : Nat) : Nat :=
  match n with
  | Nat.zero => Nat.zero
  | Nat.succ m => Nat.succ (Nat.succ (double m))

theorem double_plus
  (n : Nat) :
  ----------------
  double n = n + n
:= by
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    unfold double
    rw [ih]
    rw [Nat.succ_add]
    rfl

theorem mult_plus_distr
  (n m p : Nat) :
  -------------------------------
  (n + m) * p = (n * p) + (m * p)
:= by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [Nat.succ_mul]
    rw [Nat.add_assoc]
    rw [Nat.add_comm]
    rw [Nat.add_assoc (n * p) p (m * p)]
    rw [Nat.add_comm p (m * p)]
    rw [<- Nat.add_assoc]
    rw [<- ih]
    rw [Nat.add_assoc 1 m n]
    rw [Nat.succ_add]
    simp
    rw [Nat.succ_mul]
    rw [Nat.add_comm n m]

theorem mult_assoc
  (n m p : Nat) :
  -------------------------
  (n * m) * p = n * (m * p)
:= by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [Nat.succ_mul n (m * p)]
    rw [Nat.succ_mul n m]
    rw [mult_plus_distr]
    rw [ih]

inductive bin where
  | Z
  | B0 (b : bin)
  | B1 (b : bin)
  deriving
    Repr ,
    DecidableEq

def incrb (b : bin) : bin :=
  match b with
  | bin.Z    => bin.B1 bin.Z -- 0   => 2*0 + 1
  | bin.B0 b => bin.B1 b     -- 2*n => 2*n + 1
  | bin.B1 b => bin.B0 (incrb b)

def binToNatb (b : bin) : Nat :=
  match b with
  | bin.Z    =>                   0
  | bin.B0 b =>     2 * binToNatb b
  | bin.B1 b => 1 + 2 * binToNatb b

-- Theorem bin_to_nat_incr : forall (b:bin) , bin_to_nat (incr b) = S (bin_to_nat b).
theorem bin_to_nat_incr
  (b : bin) :
  -----------
  binToNatb (incrb b) = 1 + (binToNatb b)
:= by
  induction b with
  | Z => rfl
  | B0 b ih => rfl
  | B1 b ih =>
    simp [incrb,binToNatb]
    rewrite [ih]
    simp [<- Nat.add_assoc, Nat.mul_add]

@[simp]
def natToBinb (n:Nat) : bin :=
  match n with
  | Nat.zero => bin.Z
  | Nat.succ n => match natToBinb n with
    | bin.Z => bin.B1 bin.Z
    | bin.B0 x => bin.B1 x
    | bin.B1 x => bin.B0 (incrb x)

theorem natBinNat
  (n : Nat) :
  -----------
  binToNatb (natToBinb n) = n
:= by
  induction n with
  | zero => rfl
  | succ m ih =>
    cases h1 : (natToBinb m) with
    | Z =>
      simp [h1, binToNatb] at ih
      rw   [<- ih]
      rfl
    | B0 b =>
      simp [h1] at ih
      simp [h1, binToNatb]
      rw   [<- ih]
      simp [binToNatb, Nat.add_comm]
    | B1 b =>
      simp [h1,binToNatb] at ih
      simp [Nat.add_comm]
      rw   [h1]
      simp
      rw [
        Nat.add_comm,
        binToNatb,
        bin_to_nat_incr,
        <- ih,
        <- Nat.add_assoc,
        Nat.mul_add]

theorem double_incr
  (n : Nat) :
  -----------
  double (Nat.succ n) = Nat.succ (Nat.succ (double n))
:= by
  rfl

def doubleBin (b : bin) : bin :=
  match b with
  | .Z    => .Z
  | .B0 x => .B0 (.B0 x)
  | .B1 x => .B0 (.B1 x)

theorem doubleBinIncr
  (b : bin) :
  -----------
  doubleBin (incrb b) = incrb (incrb (doubleBin b))
:= by
  cases b <;> rfl

def normalize (b : bin) : bin :=
  match b with
  | .Z => .Z
  | .B0 b => doubleBin (normalize b)
  | .B1 b => .B1 (normalize b)

theorem incrNatToBin
  (n : Nat) :
  -----------
  (natToBinb (Nat.succ n)) = incrb (natToBinb n)
:= by
  match n with
  | .zero => rfl
  | .succ n =>
      simp
      cases (natToBinb n) <;> rfl

theorem natToBinDouble
  (n : Nat) :
  -----------
  natToBinb (n + n) = doubleBin (natToBinb n)
:= by
  induction n with
  | zero => rfl
  | succ n ih => rw
    [ Nat.add_succ
    , incrNatToBin
    , Nat.add_comm
    , <- Nat.add_assoc
    , Nat.add_succ
    , incrNatToBin
    , ih
    , incrNatToBin
    , doubleBinIncr
    ]

theorem doubleAsAdd
  (n : Nat) :
  -------------
  n + n = 2 * n
:= by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw
      [ Nat.add_assoc
      , Nat.add_comm
      , Nat.add_comm n 1
      , <- Nat.add_assoc
      , Nat.mul_add
      , <- ih
      ]
    simp
    rw [Nat.add_assoc]

theorem binNatBin
  (b : bin) :
  -----------
  natToBinb (binToNatb b) = normalize b
:= by
  induction b with
  | Z => rfl
  | B0 b0 ih =>
    simp [binToNatb, <- doubleAsAdd]
    rw [natToBinDouble, ih]
    simp [normalize]
  | B1 b1 ih =>
    simp [binToNatb, normalize, <- doubleAsAdd]
    rw [Nat.succ_add]
    rw [Nat.add_comm, Nat.add_zero]
    simp [natToBinb]
    rw [natToBinDouble, ih]
    cases (normalize b1) <;> rfl
