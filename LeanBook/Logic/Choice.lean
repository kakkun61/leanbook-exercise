#check Classical.em
#print axioms Classical.em
#check Classical.choice

/-- 関数の全射性 -/
def Surjective {X Y : Type} (f : X → Y) : Prop :=
  ∀ y : Y, ∃ x : X, f x = y

/-- Surjective を使用する例：恒等関数は全射 -/
example : Surjective (fun x : Nat => x) := by
  intro y
  exists y

def Surjective' (X Y : Type) (f : X → Y) : Prop :=
  ∀ y : Y, ∃ x : X, f x = y

/-- Surjective を使用する例：恒等関数は全射 -/
example : Surjective' Nat Nat (fun x : Nat => x) := by
  intro y
  exists y

variable {X Y : Type}

/-- 全射であるような関数 f : X → Y に対して、その右逆関数 g : Y → X を返すような高階関数 -/
noncomputable def inverse (f : X → Y) (hf : Surjective f) : Y → X := by
  intro y
  have : Nonempty {x // f x = y} := by
    let ⟨x, hx⟩ := hf y
    exact ⟨⟨x, hx⟩⟩
  have x := Classical.choice this
  exact x.val

-- 3.5.4 練習問題
/-- 「二重否定の除去」の二重否定 -/
/- 排中律を使用しない -/
theorem double_negation_elim' (P : Prop) : ¬¬ (¬¬ P → P) := by
  intro hyp_not__not_not_p_to_p
  sorry

-- Classical.choice に依存していないことを確認してください
#print axioms double_negation_elim'
