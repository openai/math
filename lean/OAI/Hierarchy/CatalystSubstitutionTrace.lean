import OAI.Hierarchy.CatalystSubstitutionHost
import OAI.Hierarchy.CatalystSubstitution

namespace OAI
/-! # Iterated replacement at counted physical oracle occurrences -/

noncomputable section
namespace Hierarchy.CatalystSubstitution
open Catalyst LinearAlgebra.SpectralBooks
open scoped Classical BigOperators

variable {k p : ℕ} {F : Type*} [Field F]

theorem Agrees.gap {A B : Approximation F k p} (h : Agrees A B) {g : (Fin p → Bool) → F}
    {D : ℝ} (hg : A.Gap g D) : B.Gap g D := by
  obtain ⟨a,an⟩ := A
  obtain ⟨b,bn⟩ := B
  obtain ⟨hw,e⟩ := h
  change a = b at hw
  cases hw
  have eq : (⟨a,an⟩ : Approximation F k p).coeff = (⟨a,bn⟩ : Approximation F k p).coeff := funext e
  let test (v : (Port p a → Bool) → F) :=
    ∀ P : SpectralPlacementPrices F (EuclideanSpace ℝ (Fin k)),
      v-ideal a g = 0 ∨ P.price (bitTensor (v-ideal a g)) (sites a) ≤ 2*(∑ j, (a j : ℝ))-D
  exact (congrArg test eq).mp hg

/-- A trace records actual opened contractions and the replacements physically
plugged into them. The coefficient check on a cut mentions only the exact call.
Each call may have a different arity, table, and directional width. -/
inductive Trace (A : Approximation F k p) (G : ℝ) : ℕ → Approximation F k p → Prop
  | nil : Trace A G 0 A
  | snoc {m q : ℕ} {B : Approximation F k p} (prev : Trace A G m B)
      (C : Context F k p q) (X : Approximation F k q) (f : (Fin q → Bool) → F)
      (cut : Agrees B (exactPlug C f)) (replacement : X.Gap f G) : Trace A G (m+1) (approxPlug C X)

/-- Taking `G` to be the minimum of the original and replacement gaps gives
the finite occurrence bound, including the empty trace. -/
theorem Trace.gap {A Y : Approximation F k p} {m : ℕ} {G : ℝ}
    (t : Trace A G m Y) {g : (Fin p → Bool) → F} (old : A.Gap g G) :
    Y.Gap g (G - 2*(k:ℝ)*(m:ℝ)) := by
  induction t with
  | nil => simpa using old
  | @snoc m q B prev C X f cut replacement ih =>
    have h := approxPlug_gap C X (cut.gap ih) replacement
    apply Approximation.Gap.mono _ h
    have nonneg : 0 ≤ 2*(k:ℝ)*(m:ℝ) := by positivity
    rw [min_eq_left (by linarith : G-2*(k:ℝ)*(m:ℝ) ≤ G)]
    push_cast
    linarith

end Hierarchy.CatalystSubstitution

end
end OAI
