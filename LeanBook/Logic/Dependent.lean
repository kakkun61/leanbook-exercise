inductive MyList (α : Type) : Type where
  | nil
  | cons (a : α) (l : List α)

inductive MyVector (α : Type) : Nat → Type where
  | nil : MyVector α 0
  | cons {n : Nat} (a : α) (l : MyVector α n) : MyVector α (n + 1)

-- 3.7.4 練習問題 (1)
example : List ((α : Type) × α) := [⟨Nat, 42⟩, ⟨Bool, false⟩]

-- 3.7.4 練習問題 (2)
example : {α : Type} → {n : Nat} → (a : α) → (v : MyVector α n) → MyVector α (n + 1) :=
  MyVector.cons
