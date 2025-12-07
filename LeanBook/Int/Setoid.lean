structure Point where
  x : Int
  y : Int

#check { x := 1, y := 2 : Point }

#check Point.mk 1 2

#check Point.x

#eval
  let p : Point := { x := 1, y := 2 }
  Point.x p + p.x

example {α : Type} : Equivalence (fun x y : α => x = y) := by
  constructor
  · intro a
    rfl
  · intro a b h
    rw [h]
  · intro a b c h1 h2
    rw [h1, h2]

example {α : Type} (sr : Setoid α) (x y : α) : sr.r x y = (x ≈ y) := by
  rfl

/- 7.1.4 練習問題 -/
example {α : Type} : Equivalence (fun _ _ : α => True) := by
  constructor
  · intro a
    trivial
  · intro a b h
    trivial
  · intro a b c h1 h2
    trivial
