/-- 人間たちの集合 -/
opaque Human : Type

/-- 愛の関係 -/
opaque Love : Human → Human → Prop

@[inherit_doc]
infix:50 "-♥→" => Love

/-- すべての人に愛されているアイドルが存在する -/
def IdolExists :=
  ∃ idol : Human, ∀ h : Human, h -♥→ idol

/-- 誰にでも好きな人の 1 人くらいいる -/
def EveryoneLovesSomeone :=
  ∀ h : Human, ∃ tgt : Human, h -♥→ tgt

/-- すべての人を愛している博愛主義者（philanthropist）が存在する -/
def PhilanExists : Prop := ∃ philan : Human, ∀ h : Human, philan -♥→ h

def EveryoneLoved : Prop := ∃ h : Human, ∃ lover : Human, lover -♥→ h

example : PhilanExists → EveryoneLoved := by
  sorry

/-- 練習問題 3.3.4 -/
example : IdolExists → EveryoneLovesSomeone := by
  intro hyp_idol_exists
  intro human
  obtain ⟨idol, hyp_the_idol_exists⟩ := hyp_idol_exists
  have hyp_human_loves_idol : human -♥→ idol := by
    exact hyp_the_idol_exists human
  exists idol

example (α : Type) (P : α → Prop) :
  (∀ x, P x) → (∃ x, P x) ∨ (∀ x, ¬ P x) := by
 sorry

example (α : Type) (P Q : α → Prop) :
  (∀ x, P x → Q x) → (∀ x, P x) → (∀ x, Q x) := by
  sorry

example (α : Type) (P Q : α → Prop) :
  (∃ x, P x ∧ Q x) → (∃ x, P x) ∧ (∃ x, Q x) := by
  sorry

example (α : Type) (P Q : α → Prop) :
  (∀ x, P x ∨ Q x) → (∀ x, P x) ∨ (∃ x, Q x) := by
  sorry

example (α : Type) (P Q : α → Prop) :
  (∀ x, P x → Q x) → (∃ x, P x) → (∃ x, Q x) := by
  sorry
