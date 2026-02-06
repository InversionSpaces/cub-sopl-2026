import Mathlib.Tactic.Basic


namespace Section3

inductive Lang
| zero
| True
| False
| succ (exp : Lang)
| pred (exp : Lang)
| iszero (exp : Lang)
| If (cond exp₁ exp₂ : Lang)

def size : Lang → Nat
| .zero => 1
| .True => 1
| .False => 1
| .succ exp => 1 + size exp
| .pred exp => 1 + size exp
| .iszero exp => 1 + size exp
| .If cond exp₁ exp₂ => 1 + size cond + size exp₁ + size exp₂


def depth : Lang → Nat
| .zero => 1
| .True => 1
| .False => 1
| .succ exp => 1 + depth exp
| .pred exp => 1 + depth exp
| .iszero exp => 1 + depth exp
| .If cond exp₁ exp₂ => 1 + max (max (depth cond) (depth exp₁)) (depth exp₂)

lemma induction_size_specified (P : Lang → Prop) :
  ∀ gen_sz, (∀ (s : Lang), (∀ r, size r < size s → P r) → P s) → ∀ s, size s < gen_sz  → P s := by
    intro gen_sz ind s hlt
    induction gen_sz generalizing s
    { simp [*] at hlt }
    rename_i n hn
    by_cases size s = n
    { grind }
    grind

theorem induction_size (P : Lang → Prop) :
  (∀ (s : Lang), (∀ r, size r < size s → P r) → P s) → ∀ s, P s := by
    intro ind s
    exact induction_size_specified P (size s + 1) ind s (by simp)


lemma induction_depth_specified (P : Lang → Prop) :
  ∀ gen_sz, (∀ (s : Lang), (∀ r, depth r < depth s → P r) → P s) →
  ∀ s, depth s < gen_sz  → P s := by
    intro gen_sz ind s hlt
    induction gen_sz generalizing s
    { simp [*] at hlt }
    rename_i n hn
    by_cases depth s = n
    { grind }
    grind

theorem induction_depth (P : Lang → Prop) :
  (∀ (s : Lang), (∀ r, depth r < depth s → P r) → P s) → ∀ s, P s := by
    intro ind s
    exact induction_depth_specified P (depth s + 1) ind s (by simp)

#check Lang.recOn

end Section3
