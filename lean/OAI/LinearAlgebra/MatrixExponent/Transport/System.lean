import OAI.LinearAlgebra.MatrixExponent.Coloring.Pad
import OAI.LinearAlgebra.MatrixExponent.Install.Weight

/-!
# Local realization of a permutation

An input-dependent controller reads a permutation and an outer
selector. At each site it chooses a local kernel and a configuration
of the incident core slots. Every enabled slot names its opposite end.
A kernel also receives the incoming and outgoing exterior records.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Transport

open Coloring

abbrev Site (h : ℕ) := B (h + 1)
abbrev Port (h p : ℕ) := Site h × B p
abbrev Data (W z : ℕ) := Fin W × Fin z → Bool
abbrev Channels (p z : ℕ) := B p × Fin z → Bool

/-- Enable flag, orientation bit, remote site and remote slot. -/
abbrev Command (h p : ℕ) := Format.pair .bit (.pair .bit (.pair (.addr (h + 1)) (.addr p)))
abbrev Controls (h p : ℕ) (A : Format) := Format.vec (h + 1) (.pair A (.vec p (Command h p)))
abbrev Orders (h p : ℕ) := Port h p → (Command h p).obj

variable {h p W z : ℕ}

def commands {A : Format} (c : (Controls h p A).obj) : Orders h p := fun i => (c i.1).2 i.2

def Enabled (a : Orders h p) : Finset (Port h p) := Finset.univ.filter (fun i => (a i).1)

def Valid (group : Port h p → ℕ) (a : Orders h p) : Prop :=
  ∀ i ∈ Enabled a, let j := (a i).2.2
    j ∈ Enabled a ∧ (a j).2.2 = i ∧ (a j).2.1 = !(a i).2.1 ∧ group j = group i

def Joins (a : Orders h p) (c : Site h → Channels p z) : Prop :=
  ∀ i ∈ Enabled a, let j := (a i).2.2
    ∀ t, c i.1 (i.2, t) = c j.1 (j.2, t)

abbrev KernelPins (A : Format) (p W z : ℕ) :=
  A.pins ⊕ (Fin W × Fin z) ⊕ (Fin W × Fin z) ⊕ (B p × Fin z)

structure System (F : Type) (h p W z : ℕ) where
  selector : Format
  config : Format
  dispatch : ((Perm h).pair selector).obj → (Controls h p config).obj
  group : Port h p → ℕ
  kernel : config.obj → Data W z → Data W z → Channels p z → F

namespace System

variable {F : Type} [Field F] (S : System F h p W z)

def localWeight (x : KernelPins S.config p W z → Bool) : F :=
  S.kernel (S.config.code.symm (x ∘ Sum.inl)) (fun i => x (.inr (.inl i)))
    (fun i => x (.inr (.inr (.inl i)))) (fun i => x (.inr (.inr (.inr i))))

def value (v : (Controls h p S.config).obj) (x y : Site h → Data W z)
    (c : Site h → Channels p z) : F :=
  ∏ i, S.kernel (v i).1 (x i) (y i) (c i)

open Classical in
def Correct (C : ℕ) : Prop :=
  ∀ (σ : Equiv.Perm (B h)) (x y : Site h → Data W z),
    (∀ t c, let v := S.dispatch (σ, t)
      S.value v x y c ≠ 0 → Valid S.group (commands v) ∧ (Enabled (commands v)).card ≤ C * W * 2 ^ h) ∧
    (if ∀ i, x i = y (Routing.inflate h σ i) then (1 : F) else 0) =
      ∑ t : S.selector.pins → Bool, ∑ c : Site h → Channels p z,
        let v := S.dispatch (σ, S.selector.code.symm t)
        S.value v x y c * (if Joins (commands v) c then 1 else 0)

end System

/-- Uniform bound on transported width; all control and local kernel
costs may depend on the chosen height ratio. -/
def LocalProtocol (F : Type) [Field F] : Prop :=
  ∃ C : ℕ, ∀ τ : ℝ, 0 < τ → ∃ p W D : ℕ, 4 ≤ W ∧ ∀ᶠ h : ℕ in Filter.atTop,
    ∃ b : ℕ, p + 22 ≤ b ∧ b ≤ h ∧ (b : ℝ) ≤ τ * h ∧ ∀ j : ℕ, j ≤ h →
      ∃ S : System F h p W (2 ^ j), S.Correct C ∧
        (∀ i, (Finset.univ.filter (fun k => S.group k = i)).card ≤ 2 ^ (b - 1)) ∧
        Cheap F (h + 1) (h + 1) ((Perm h).pair S.selector) (Controls h p S.config) S.dispatch D ∧
        Install.Weight F S.localWeight (2 ^ j * (100 + j) ^ D)

end OAI.LinearAlgebra.MatrixExponent.Transport
