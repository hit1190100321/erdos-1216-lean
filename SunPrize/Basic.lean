import Std

namespace SunPrize

/-- 对按编号递增的三个顶点，判断是否构成有向三角形。 -/
def cycleBits (a b c : Bool) : Prop :=
  (a = true ∧ b = true ∧ c = false) ∨
  (a = false ∧ b = false ∧ c = true)

def cyclic (g : Nat → Nat → Bool) (a b c : Nat) : Prop :=
  cycleBits (g a b) (g b c) (g a c)

/-- 每个四点子集都含有有向三角形。 -/
def Obstruction4 (n : Nat) (g : Nat → Nat → Bool) : Prop :=
  ∀ a b c d : Nat, a < b → b < c → c < d → d < n →
    cyclic g a b c ∨ cyclic g a b d ∨ cyclic g a c d ∨ cyclic g b c d ∨ False

/-- 每个五点子集都含有有向三角形，因而没有五点传递子图。 -/
def Obstruction5 (n : Nat) (g : Nat → Nat → Bool) : Prop :=
  ∀ a b c d e : Nat, a < b → b < c → c < d → d < e → e < n →
    cyclic g a b c ∨ cyclic g a b d ∨ cyclic g a b e ∨
    cyclic g a c d ∨ cyclic g a c e ∨ cyclic g a d e ∨
    cyclic g b c d ∨ cyclic g b c e ∨ cyclic g b d e ∨
    cyclic g c d e ∨ False

theorem cycleClause0 : ∀ a b c : Bool, (a = true) ∨ (b = true) ∨ (c = true) ∨ ¬ (cycleBits a b c) ∨ False := by intro a b c; cases a <;> cases b <;> cases c <;> simp [cycleBits]

theorem cycleClause1 : ∀ a b c : Bool, (a = true) ∨ (b = true) ∨ ¬ (c = true) ∨ (cycleBits a b c) ∨ False := by intro a b c; cases a <;> cases b <;> cases c <;> simp [cycleBits]

theorem cycleClause2 : ∀ a b c : Bool, (a = true) ∨ ¬ (b = true) ∨ (c = true) ∨ ¬ (cycleBits a b c) ∨ False := by intro a b c; cases a <;> cases b <;> cases c <;> simp [cycleBits]

theorem cycleClause3 : ∀ a b c : Bool, (a = true) ∨ ¬ (b = true) ∨ ¬ (c = true) ∨ ¬ (cycleBits a b c) ∨ False := by intro a b c; cases a <;> cases b <;> cases c <;> simp [cycleBits]

theorem cycleClause4 : ∀ a b c : Bool, ¬ (a = true) ∨ (b = true) ∨ (c = true) ∨ ¬ (cycleBits a b c) ∨ False := by intro a b c; cases a <;> cases b <;> cases c <;> simp [cycleBits]

theorem cycleClause5 : ∀ a b c : Bool, ¬ (a = true) ∨ (b = true) ∨ ¬ (c = true) ∨ ¬ (cycleBits a b c) ∨ False := by intro a b c; cases a <;> cases b <;> cases c <;> simp [cycleBits]

theorem cycleClause6 : ∀ a b c : Bool, ¬ (a = true) ∨ ¬ (b = true) ∨ (c = true) ∨ (cycleBits a b c) ∨ False := by intro a b c; cases a <;> cases b <;> cases c <;> simp [cycleBits]

theorem cycleClause7 : ∀ a b c : Bool, ¬ (a = true) ∨ ¬ (b = true) ∨ ¬ (c = true) ∨ ¬ (cycleBits a b c) ∨ False := by intro a b c; cases a <;> cases b <;> cases c <;> simp [cycleBits]

end SunPrize
