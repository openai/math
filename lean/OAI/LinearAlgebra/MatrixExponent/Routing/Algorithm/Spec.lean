import OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm.Code


/-!
# Observable interface of the protocol with charged advice

The tags have h bits. The other input word at each site selects a
local summand. Outputs are a bounded configuration word and a fixed
list of enable, orientation, address and slot fields.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm
open Coloring Transport
open scoped Classical

variable {F : Type} [Field F]

abbrev Input (h q : ℕ) := Format.pair (Perm h) (.vec (h + 1) (.addr q))
abbrev Program (h p q l : ℕ) := Code (3 * (h + 1) + 10) (Input h q).obj (Controls h p (.addr l)).obj
abbrev Kernel (F : Type) (p l w n : ℕ) :=
  B l → (Fin w → Bool) → (Fin w → Bool) → Channels p n → F

abbrev network {h p q l w n : ℕ} (code : Program h p q l) (group : Port h p → ℕ)
    (f : Kernel F p l w n) : PaddedSystem F h p w n :=
  ⟨.vec (h + 1) (.addr q), .addr l, code.eval, group, f⟩

/-- One bank holds the n original labels. The other bank receives
identical padding at the two interfaces. -/
def padded {A : Type} {h : ℕ} (a : A) (x : B h → A) (i : Site h) :=
  if hi : i.val < 2 ^ h then x ⟨i.val, hi⟩ else a

variable {h p w u : ℕ} (S : PaddedSystem F h p w u) (σ : Equiv.Perm (B h))

/-- Selectors for which the commands describe a matching of bounded cost. -/
def legal (C : ℕ) :=
  Finset.univ.filter fun z : S.selector.pins → Bool =>
    let a := commands (S.dispatch (σ, S.selector.code.symm z))
    Valid S.group a ∧ (Enabled a).card * u ≤ C * 2 ^ h * w

end OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm
