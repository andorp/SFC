import LF.Basic

def plusClaim : Prop := 2 + 2 = 4

theorem plusClaimIsTrue : plusClaim
:= by rfl

def isThree (n : Nat) : Prop := n = 3

def injective {A B} (f : A -> B) : Prop :=
  forall x y : A , f x = f y -> x = y

theorem succInjective : injective Nat.succ
:= by
  simp [injective]

theorem andExample : 3 + 4 = 7 /\ 2 * 2 = 4
:= by constructor <;> rfl-- or apply And.intro

theorem plusIsZero
  (n m : Nat)
  (h1  : n + m = 0) :
  -------------------
  n = 0 /\ m = 0
:= by
  cases n with
  | zero =>
    simp [Nat.add] at h1
    simp
    assumption
  | succ n =>
    cases m <;> simp [Nat.add] at h1

theorem zeroPlusZero
  (n m : Nat)
  (h1  : n = 0 /\ m = 0) :
  ------------------------
  n + m = 0
:= by simp [h1]

theorem plusZeroIsMultZero
  (n m : Nat)
  (h1 : n + m = 0) :
  ------------------
  n * m = 0
:= by
  simp [plusIsZero] at h1
  simp [h1]

theorem andProj1
  (P Q : Prop) :
  --------------
  P /\ Q -> P
:= by
  intros h1
  simp [h1]

theorem andProj2
  (P Q : Prop) :
  --------------
  P /\ Q -> Q
:= by
  intros h1
  simp [h1]

theorem andComm
  (P Q : Prop) :
  --------------
  P /\ Q -> Q /\ P
:= by
  intros h1
  simp [h1]

theorem andAssoc
  (P Q R : Prop) :
  ----------------
  P /\ (Q /\ R) -> (P /\ Q) /\ R
:= by
  intros h1
  have ⟨ h2, h3, h4 ⟩ := h1
  simp [h2,h3,h4]

theorem factorIsZero
  (n m : Nat)
  (h : n = 0 \/ m = 0) :
  ----------------------
  n * m = 0
:= by
  cases h with
  | inl h =>
    simp [h]
  | inr h =>
    simp [h]

theorem orIntroLeft
  (A B : Prop)
  (a : A) :
  ---------
  A \/ B
:= by
  simp [a]

theorem multIsZero
  (n m : Nat)
  (h : n * m = 0) :
  -----------------
  n = 0 \/ m = 0
:= by
  induction n with
  | zero =>
    simp
  | succ n =>
    induction m with
    | zero =>
      simp
    | succ m =>
      contradiction

theorem orComm
  (P Q : Prop)
  (h : P \/ Q) :
  --------------
  Q \/ P
:= by
  cases h with
  | inl h =>
    simp [h]
  | inr h =>
    simp [h]

theorem exFalsoQuodlibet
  (P : Prop) :
  ------------
  False -> P
:= by
  intros h1
  contradiction

theorem notImpliesOurNot
  (P  : Prop)
  (h1 : ¬ P) :
  -------
  (forall (Q : Prop) , P -> Q)
:= by
  intros Q h2
  contradiction

theorem zeroNotOne :
  (0 ≠ 1)
:= by
  intros h1
  contradiction

theorem notFalse :
  ¬ False
:= by
  intros h1
  assumption

theorem contradictionImpliesAnything
  (P Q : Prop)
  (h : P /\ ¬ P) :
  --------------
  Q
:= by
  have ⟨ h1 , h2 ⟩ := h
  contradiction

theorem doubleNeg
  (P : Prop)
  (h : P) :
  ---------
  ¬ ¬ P
:= by
  intro h1
  contradiction

theorem contrapositive
  (P Q : Prop)
  (h1 : P -> Q) :
  --------------
  ¬ Q -> ¬ P
:= by
  intros h2 h3
  apply h2
  apply h1
  assumption

theorem notBothTrueAndFalse
  (P : Prop) :
  --------------
  (¬ (P /\ ¬P))
:= by
  intros h
  have ⟨ h1 , h2 ⟩ := h
  contradiction

theorem deMorganNotOr
  (P Q : Prop)
  (h1 : ¬ (P \/ Q)) :
  ------------------
  ¬P /\ ¬Q
:= by
  constructor <;> intros h2 <;> apply h1
  . left
    assumption
  . right
    assumption

theorem notTrueIsFalse
  (b : Bool)
  (h : b ≠ true) :
  ----------------
  b = false
:= by
  cases b with
  | false => rfl
  | true  => contradiction

def discFn (n : Nat) : Prop :=
  match n with
  | .zero => True
  | .succ _ => False

theorem discExample
  (n : Nat) :
  -----------
  ¬ (Nat.zero = n.succ)
:= by
  intros contra
  simp [discFn] at contra

theorem nilIsNotCons
  (X : Type)
  (x : X)
  (xs : List X) :
  ---------------
  ¬ (List.nil = List.cons x xs)
:= by
  intros contra
  contradiction

def iff (P Q : Prop) := (P -> Q) /\ (Q -> P)

-- This is <-> in Lean4
notation x "<=>" y => iff x y

theorem iffSym
  (P Q : Prop)
  (h : P <=> Q) :
  ---------------
  (Q <=> P)
:= by
  have ⟨ h1 , h2 ⟩ := h
  constructor <;> assumption

theorem iffSymL
  (P Q : Prop)
  (h : P <-> Q) :
  ---------------
  (Q <-> P)
:= by
  have ⟨ h1 , h2 ⟩  := h
  constructor <;> assumption

theorem notTrueIffFalse
  (b : Bool) :
  ------------
  (b ≠ true <-> b = false)
:= by
  constructor <;> intros h1
  . cases b with
    | false => rfl
    | true => contradiction
  . cases b <;> intros h2 <;> contradiction

theorem applyIffExample
  (P Q R : Prop)
  (h1 : P <-> Q)
  (h2 : Q -> R) :
  ---------------
  (P -> R)
:= by
  intros h3
  apply h2
  have ⟨ h4 , h5 ⟩ := h1
  apply h4
  assumption

theorem iffRfl
  (P : Prop) :
  ------------
  P <-> P
:= by
  constructor <;> intros h1 <;> assumption

theorem iffTrans
  (P Q R : Prop)
  (h1 : P <-> Q)
  (h2 : Q <-> R) :
  ----------------
  P <-> R
:= by
  constructor <;> intros h3
  . apply h2.mp
    apply h1.mp
    assumption
  . apply h1.mpr
    apply h2.mpr
    assumption

theorem orDistributesOverAnd
  (P Q R : Prop) :
  ----------------
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R)
:= by
  constructor <;> intros h1
  . cases h1 with
    | inl h1 =>
      constructor <;> left <;> assumption
    | inr h1 =>
      have ⟨ h2 , h3 ⟩ := h1
      constructor <;> right <;> assumption
  . cases h1 with
    | intro h1 h2 =>
      cases h1 with
      | inl h1 =>
        left
        assumption
      | inr h1 =>
        cases h2 with
        | inl h2 =>
          left
          assumption
        | inr h2 =>
          right
          trivial

theorem mulEqZero
  (n m : Nat) :
  -------------
  (n * m = 0 <-> n = 0 \/ m = 0)
:= by
  constructor
  . apply multIsZero
  . apply factorIsZero

theorem orAssoc
  (P Q R : Prop) :
  ----------------
  P \/ (Q \/ R) <-> (P \/ Q) \/ R
:= by
  constructor <;> intros h1
  . cases h1 with
    | inl h1 => left; left; assumption
    | inr h1 => cases h1 with
      | inl h1 => left; right; assumption
      | inr h1 => right; assumption
  . cases h1 with
    | inl h1 => cases h1 with
      | inl h1 => left; assumption
      | inr h1 => right; left; assumption
    | inr h1 => right; right; assumption

def double (n : Nat) : Nat :=
  match n with
  | .zero   => .zero
  | .succ n => .succ (.succ (double n))

def Even x := exists (n : Nat) , x = double n

theorem fourIsEven : Even 4
:= by
  exists 2

theorem distNotExist
  (X : Type)
  (P : X -> Prop)
  (h : forall x , P x) :
  ----------------------
  ¬ (exists x , ¬ P x)
:= by
  intros h1
  have ⟨ h2 , h3 ⟩ := h1
  apply h3
  apply h

theorem distExistsOr
  (X : Type)
  (P Q : X -> Prop) :
  -------------------
  (∃ x, P x \/ Q x) <-> (∃ x, P x) \/ (∃ x, Q x)
:= by
  constructor <;> intros h1
  . have ⟨ h2 , h3 ⟩ := h1
    cases h3 with
    | inl h3 => left; exists h2
    | inr h3 => right; exists h2
  . cases h1 with
    | inl h1 =>
      have ⟨ h2, h3 ⟩ := h1
      exists h2
      left
      assumption
    | inr h1 =>
      have ⟨ h2, h3 ⟩ := h1
      exists h2
      right
      assumption

theorem lebPlusExists
  (n m : Nat)
  (h : (n <= m)) :
  -----------------------
  ∃ x , m = n + x
:= by
  revert m
  induction n with
  | zero =>
    intros m
    cases m with
    | zero =>
      intros h1
      exists 0
    | succ m =>
      intros h1
      exists (.succ m)
      simp
  | succ n ihn =>
    intros m
    cases m with
    | zero =>
      intros h1
      simp at h1
    | succ m =>
      intros h1
      simp at h1
      have ⟨ x, h3 ⟩ := ihn m h1
      exists x
      rw [h3]
      rw [Nat.add_assoc n x 1]
      rw [Nat.add_assoc n 1 x]
      rw [Nat.add_comm x 1]

theorem plusExistsLeb
  (n m : Nat)
  (h : ∃ x, m = n + x) :
  ----------------------
  n <= m
:= by
  revert m
  induction n <;> intros m
  case zero => cases m <;> intros h1 <;> simp
  case succ n ih => cases m with
    | zero =>
      intros h1
      exfalso
      have ⟨ x , h2 ⟩ := h1
      rw
        [ Nat.add_assoc n 1 x
        , Nat.add_comm 1 x
        , <- Nat.add_assoc n x 1
        , Nat.add_succ
        ] at h2
      contradiction
    | succ m =>
      intros h1
      have ⟨ x , h2 ⟩ := h1
      simp
      apply ih
      exists x
      rw
        [ Nat.add_assoc n 1 x
        , Nat.add_comm 1 x
        , <- Nat.add_assoc n x 1
        , Nat.add_succ m 0
        , Nat.add_succ (n + x)
        ] at h2
      simp at h2
      assumption

def In
  {A : Type}
  (x : A)
  (l : List A) :
  --------------
  Prop
:= match l with
  | .nil => False
  | .cons y l => y = x \/ In x l

theorem InMap
  (A B : Type)
  (f : A -> B)
  (l : List A)
  (x : A)
  (h : In x l) :
  --------------
  In (f x) (List.map f l)
:= by
  revert x
  induction l with
  | nil =>
    intros x h1
    contradiction
  | cons y l ih =>
    intros x h1
    simp [In] at h1
    cases h1 with
    | inl h2 =>
      left
      rw [h2]
    | inr h2 =>
      right
      apply ih
      assumption

theorem InMapIff
  (A B : Type)
  (f : A -> B)
  (l : List A)
  (y : B) :
  ---------
  In y (List.map f l) <-> ∃ x, f x = y /\ In x l
:= by
  constructor
  . induction l with
    | nil =>
      intros h1
      contradiction
    | cons x l ih =>
      intros h1
      cases h1 with
      | inl h1 =>
        exists x
        constructor
        . assumption
        . left; rfl
      | inr h1 =>
        have h2 := ih h1
        have ⟨ z , ⟨ h4, h5 ⟩ ⟩ := h2
        exists z
        constructor
        . assumption
        . right; assumption
  . induction l with
    | nil =>
      intros h1
      have ⟨ x , ⟨ h2, h3 ⟩ ⟩ := h1
      contradiction
    | cons x l ih =>
      intros h1
      have ⟨ z , ⟨ h2 , h3 ⟩ ⟩ := h1
      cases h3 with
      | inl h3 =>
        subst h3
        left
        assumption
      | inr h3 =>
        right
        apply ih
        exists z
