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
