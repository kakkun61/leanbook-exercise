#check true
#check True

example (P : Prop) (h : P) : P := by
  exact h

example (P : Prop) (h : P) : P := by
  assumption

#eval True → False

example (P Q : Prop) (h1 : P → Q) (h2 : Q → P) : P ↔ Q := by
  constructor
  · apply h1
  · apply h2

example (P Q : Prop) (h1 : P → Q) (h2 : Q → P) : P ↔ Q := by
  constructor
  · exact h1
  · exact h2

example (P Q : Prop) (h1 : P → Q) (h2 : Q → P) : P ↔ Q := by
  constructor
  apply h1
  apply h2

example (P Q : Prop) (h1 : P → Q) (h2 : Q → P) : P ↔ Q := by
  constructor
  case mp => apply h1
  case mpr => apply h2

example (P Q : Prop) (hq : Q) : (Q → P) ↔ P := by
  constructor
  intro h
  exact h hq
  intro hp hq
  exact hp

example (P Q : Prop) (h : P ↔ Q) : P = Q := by
  rw [h]

example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  cases h with
  | inl hp =>
    right
    exact hp
  | inr hq =>
    left
    exact hq

-- 3.1.8 練習問題 の 1
example (P Q : Prop) : (¬ P ∨ Q) → (P → Q) := by
  intro h1
  intro h2
  cases h1 with
  | inl h =>
    contradiction
  | inr h =>
    exact h

-- 3.1.8 練習問題 の 2
example (P Q : Prop) : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q := by
  constructor
  case mp =>
    intro h1
    constructor
    case left =>
      intro h
      apply h1
      left
      exact h
    case right =>
      intro h
      apply h1
      right
      exact h
  case mpr =>
    intro h1
    intro h2
    cases h2 with
    | inl hl =>
      apply h1.left
      exact hl
    | inr hr =>
      apply h1.right
      exact hr

-- GitHub Copilot で解いてもらった
example (P Q R : Prop) : P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R) := by
  intro h
  cases h.right with
  | inl hl =>
    left
    constructor
    · exact h.left
    · exact hl
  | inr hr =>
    right
    constructor
    · exact h.left
    · exact hr

example
  (P Q R S : Prop) :
  (P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S) → (P ∨ Q) ∧ (R ∨ S) := by
  intro hyp
  constructor
  · cases hyp with
    | inl hyp' =>
      left
      exact hyp'.left
    | inr hyp' =>
      cases hyp' with
      | inl hyp'' =>
        left
        exact hyp''.left
      | inr hyp'' =>
        cases hyp'' with
        | inl hyp''' =>
          right
          exact hyp'''.left
        | inr hyp''' =>
          right
          exact hyp'''.left
  · cases hyp with
    | inl hyp' =>
      left
      exact hyp'.right
    | inr hyp' =>
      cases hyp' with
      | inl hyp'' =>
        right
        exact hyp''.right
      | inr hyp'' =>
        cases hyp'' with
        | inl hyp''' =>
          left
          exact hyp'''.right
        | inr hyp''' =>
          right
          exact hyp'''.right
