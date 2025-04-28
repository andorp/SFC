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
      sorry
