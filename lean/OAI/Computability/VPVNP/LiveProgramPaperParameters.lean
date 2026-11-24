import OAI.Computability.VPVNP.DiagonalClock
import OAI.Computability.VPVNP.LiveProgramAdviceCapacity
import OAI.Computability.VPVNP.LiveOutsideBudget
import OAI.Computability.VPVNP.LiveWorkspaceCapacity

/-!
# Joint parameter choices for the live evaluator and the diagonal budget

Choose the chain power, raw-prefix and advice exponents, tape radius and cut
width before choosing the address multiplier. The bound on that multiplier
depends on these fixed exponents. Only then take the eventual threshold in
the input length.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram

open Filter CursorBounds LiveEvaluatorEncoding

private def labelCount (C motif n : ℕ) := PrimedStackRAM.labelCount n n (n^(C+5)) + motif

private theorem polynomial_labels (C motif : ℕ) : PolynomiallyBounded (labelCount C motif) := by
  let id := PolynomiallyBounded.id
  let state := id.pow (C+5)
  have pair := (id.mul id).of_le (fun n => show n*(n-1)/2 ≤ n*n from
    (Nat.div_le_self ..).trans (Nat.mul_le_mul_left n (Nat.sub_le ..)))
  change PolynomiallyBounded (fun n => PrimedStackRAM.labelCount n n (n^(C+5)) + motif)
  simpa [PrimedStackRAM.labelCount, Nat.choose_two_right] using
    (((state.mul id).mul (.const 2)).add (((pair.mul state).mul state).mul state)).add (.const motif)

/-- One choice of the constants gives simultaneous clock, cut, advice and
outside-budget bounds, as well as sufficient physical word space. -/
theorem paper_parameters (C motif : ℕ) {P rawLength H : ℕ → ℕ} (radius : ℕ → ℕ → ℕ)
    (hP : PolynomiallyBounded P) (hraw : PolynomiallyBounded rawLength) (hH : PolynomiallyBounded H)
    (hr : ∀ a, PolynomiallyBounded (fun n => radius n (2*n^a))) (E : UniversalMachine.Program) :
    ∃ a dA d₁ d₂ r B₀ : ℕ, 2 ≤ a ∧ 1 ≤ B₀ ∧ ∀ k B : ℕ, B₀ ≤ B → ∀ᶠ n : ℕ in atTop,
      let c : Constants := ⟨C, a, d₁, d₂, r, dA, motif⟩
      let g := paperGeometry B H n
      let t := c.labels.eval g
      let Z := 2*n^a
      2^(P n) * (Z+1)^k ≤ 2^(n^a-1) ∧ radius n Z ≤ n^r ∧ rawLength n ≤ n^dA ∧
      g.w + n^dA + t * Nat.clog 2 t ≤ n^d₁ ∧ 1 + t*Z ≤ n^d₂ ∧
      LiveEvaluatorTail.Layout E.extra (n^r) g.w (n^d₂) ∧
      OutsideBudget.majorant c n < processorCount B n ∧ g.w ≤ n ∧
      (Layout.pairWorkspace c).eval g + (processorCount B n)^2 < 2^g.w ∧
      (Layout.shadow c).eval g < 2^g.w ∧ (Layout.oldState c).eval g < 2^g.w ∧
      Layout.stageTag.eval g < 2^g.w := by
  let t := labelCount C motif
  have ht : PolynomiallyBounded t := polynomial_labels C motif
  obtain ⟨a, _, _, ha, hclock⟩ := DiagonalClock.parameters radius hP hraw ht hr E
  obtain ⟨r, hrad⟩ := Advice.eventually_power (hr a)
  obtain ⟨dA, d₁, had⟩ := Advice.capacity_exponents hraw ht
  have hfields : PolynomiallyBounded fun n => fieldWords (n^r) :=
    (((PolynomiallyBounded.const 1).add (((PolynomiallyBounded.const 2).mul
      (PolynomiallyBounded.id.pow r)).add (.const 1))).add (((PolynomiallyBounded.const 2).mul
      (PolynomiallyBounded.id.pow r)).add (.const 1)))
  have hz := (PolynomiallyBounded.const 2).mul (PolynomiallyBounded.id.pow a)
  obtain ⟨d₂, hcut⟩ := Advice.eventually_power (((PolynomiallyBounded.const 1).add (ht.mul hz)).add
    ((PolynomiallyBounded.const 1).add (hfields.mul PolynomiallyBounded.id)))
  let c : Constants := ⟨C, a, d₁, d₂, r, dA, motif⟩
  obtain ⟨B', hbudget⟩ := OutsideBudget.eventually_budget c
  refine ⟨a, dA, d₁, d₂, r, max 1 B', ha, le_max_left .., fun k B hB => ?_⟩
  have hB' := (le_max_left 1 B').trans hB
  filter_upwards [hclock k B hB', hrad, had B, hcut, hbudget B ((le_max_right ..).trans hB),
    eventually_workspace c hB' hH] with n time rad adv cut budget work
  have he : c.labels.eval (paperGeometry B H n) = t n := by rw [Constants.labels, eval_add, Constants.grammarLabels_eq]; rfl
  change 1+t n*(2*n^a) + (1+fieldWords (n^r)*n) ≤ n^d₂ at cut
  have hwidth := Nat.mul_le_mul_left (fieldWords (n^r)) budget.2
  dsimp only
  change _ ∧ _ ∧ _ ∧ _ + _ + c.labels.eval _ * _ ≤ _ ∧ 1 + c.labels.eval _ * _ ≤ _ ∧ _
  rw [he]
  exact ⟨time.1, rad, adv.1, adv.2, by omega, ⟨time.2.2.2.symbolWidth, time.2.2.2.stateWidth,
    by change 1 + fieldWords (n^r) * wordBits B n ≤ n^d₂; omega⟩, budget.1, budget.2, work⟩

end LiveProgram

end VPVNP
end Computability
end OAI
