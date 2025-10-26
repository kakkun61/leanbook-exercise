import LeanBook.NatSemiring.Mult

/-- 分配法則を適用して足し算を式の外側に持ってくるタクティク -/
macro "distrib" : tactic => `(tactic| simp only [MyNat.mul_add, MyNat.add_mul])

-- #check distrib

/-- 分配法則を適用して足し算を式の外側に持ってくるタクティク -/
macro "distrib" : tactic => `(tactic| focus
  simp only [MyNat.mul_add, MyNat.add_mul]
  simp only [MyNat.mul_zero, MyNat.zero_mul, MyNat.mul_one, MyNat.one_mul]
  ac_rfl
)

/-- 数値リテラルを 1 + 1 + ··· + 1 に分解するための補題 -/
theorem unfoldNatLit (x : Nat) : (OfNat.ofNat (x + 2) : MyNat) = (OfNat.ofNat (x + 1) : MyNat) + 1 :=
  rfl

/-- 自然数を 1 + 1 + ··· + 1 に分解する -/
macro "expand_num" : tactic => `(tactic| focus
  simp only [unfoldNatLit]
  -- 標準の Nat の和を簡単な形にする
  simp only [Nat.reduceAdd]
  -- OfNat.ofNat を消す
  dsimp only [OfNat.ofNat]
  simp only [
    show MyNat.ofNat 1 = 1 from rfl,
    show MyNat.ofNat 0 = 0 from rfl
  ]
)

/-- expand_num タクティクのテスト -/
example (n : MyNat) : 3 * n = 2 * n + 1 * n := by
  expand_num

  -- 数値が 1 + 1 + ··· + 1 に分解された
  guard_target =ₛ (1 + 1 + 1) * n = (1 + 1) * n + 1 * n
  simp only [MyNat.add_mul]

/-- 分配法則を適用して足し算を式の外側に持ってくる -/
macro "distrib" : tactic => `(tactic| focus
  expand_num -- expand_num を使用する
  simp only [
    MyNat.mul_add,
    MyNat.add_mul,
    MyNat.mul_zero,
    MyNat.zero_mul,
    MyNat.mul_one,
    MyNat.one_mul
  ]
  ac_rfl
)

/-- distrib タクティクのテスト -/
example (m n : MyNat) : (m + 4) * n + n = m * n + 5 * n := by
  distrib

/-- 自然数を 1 + 1 + ··· + 1 に分解する -/
macro "expand_num" : tactic => `(tactic| focus
  try simp only [unfoldNatLit, Nat.reduceAdd] -- try を付け加える
  try dsimp only [OfNat.ofNat] -- try を付け加える
  try simp only [ -- try を付け加える
    show MyNat.ofNat 1 = 1 from rfl,
    show MyNat.ofNat 0 = 0 from rfl
  ]
)

/-- 分配法則を適用して足し算を式の外側に持ってくる -/
macro "distrib" : tactic => `(tactic| focus
  expand_num
  try simp only [ -- try を付け加える
    MyNat.mul_add,
    MyNat.add_mul,
    MyNat.mul_zero,
    MyNat.zero_mul,
    MyNat.mul_one,
    MyNat.one_mul
  ]
  try ac_rfl -- try を付け加える
)

-- エラーで落ちなくなった！
example (m n : MyNat) : m * n + n * n = (m + n) * n := by
  distrib

-- 5.2.7 練習問題
example (n : MyNat) : ∃ s t : MyNat, s * t = n * n + 8 * n + 16 := by
  exists n + 4
  exists n + 4
  distrib
