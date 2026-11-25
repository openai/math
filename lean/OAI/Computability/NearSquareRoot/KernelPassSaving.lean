import OAI.Computability.NearSquareRoot.KernelGeneratedRepair
import OAI.Computability.NearSquareRoot.KernelPassSearch
import OAI.LinearAlgebra.FiniteFourier.PrimeStrictSaving
import OAI.LinearAlgebra.FiniteFourier.PrimeRectangleSystem

/-! # Strict recursive saving of the generated binary repair

One label runs the full pencil on all coefficient components. Across labels
the two incidence lists and the charged rectangles bound a stage. Full
spectral conversions apply only to the two check banks. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPassSaving

open OAI.LinearAlgebra.FiniteFourier PencilSearch
open scoped CyclotomicCode

abbrev labels (L b : ℕ) := (2^b)^L
abbrev expandedWidth (m : ℕ) := batchWidth m * 2^(batchExponent m)
abbrev expandedChecks (m : ℕ) := batchChecks m * 2^(batchExponent m)
abbrev axes (m D : ℕ) := 2*(m+D-1)

def stageBound (L b m D : ℕ) : ℕ :=
  2*D*expandedWidth m * (2*labels L b*(1+b)^L + m*(2^L*(2^b)^(L/2)))

def callBound (L b m D stage : ℕ) : ℕ :=
  4*clockPeriod m*stage + 4*labels L b*expandedChecks m*axes m D

/-- The identified row degree factors out of the entire call count,
including both conversions of the two check banks. -/
theorem calls_le_budget {L b m D stage calls : ℕ}
    (hs : stage ≤ stageBound L b m D) (hc : calls ≤ callBound L b m D stage) :
    calls ≤ 2^(batchExponent m) * primeKernelCallBudget 2 L b m D (batchWidth m) := by
  let R := batchWidth m
  let H := 2^(batchExponent m)
  let A := axes m D
  let N := labels L b
  let I := 2*N*(1+b)^L + m*(2^L*(2^b)^(L/2))
  rw [stageBound] at hs
  change stage ≤ 2*D*(R*H)*I at hs
  rw [callBound, clockPeriod_eq] at hc
  change calls ≤ 4*countPencilOrder 2 m*stage + 4*N*(R/(2*m^3)*H)*A at hc
  change calls ≤ H * (((2+2)*countPencilOrder 2 m) * (2*2*D*R)*I + 4*(R/(2*m^3))*A*N)
  have hp := Nat.mul_le_mul_left (4*countPencilOrder 2 m) hs
  have hrow : 2*D*(R*H)*I ≤ H*(2*2*D*R)*I := by
    have hh : 2*D*R*H ≤ 2*(2*D*R*H) := by omega
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using Nat.mul_le_mul_right I hh
  calc
    calls ≤ _ := hc
    _ ≤ 4*countPencilOrder 2 m*(2*D*(R*H)*I) + 4*N*(R/(2*m^3)*H)*A :=
      Nat.add_le_add_right hp _
    _ ≤ 4*countPencilOrder 2 m*(H*(2*2*D*R)*I) + 4*N*(R/(2*m^3)*H)*A := by gcongr
    _ = _ := by ring

/-- Every stage and total call count satisfying the compiled bounds meet
the strict target for this single choice of label length, alphabet, and
query count, uniformly in the allowed common-space dimension. -/
theorem exists_parameters {θ : ℝ} (hθ : 1/2 < θ) :
    ∃ L b m : ℕ, 2 ≤ L ∧ 1 ≤ b ∧ 2 ≤ m ∧ m ≡ 1 [MOD 2] ∧
      ∀ D : ℕ, 1 ≤ D → D ≤ 1+(1+L*2^b)^(2-1) →
      ∀ stage calls : ℕ, stage ≤ stageBound L b m D → calls ≤ callBound L b m D stage →
        (calls : ℝ)/(labels L b * expandedWidth m : ℕ) < (axes m D : ℝ)^θ := by
  obtain ⟨L,b,m,hL,hb,hm,hmod,h⟩ := exists_primeKernelCallBudget_lt (by decide : 2 ≤ 2) hθ
  refine ⟨L,b,m,hL,hb,hm,hmod,?_⟩
  intro D hD hDr stage calls hs hc
  have h := h D hD hDr (batchWidth m) (2^(batchExponent m))
    (by have := two_le_batchWidth hm; omega) (by positivity)
  have hrows : labels L b * expandedWidth m =
      2^batchExponent m * batchWidth m * (2^b)^L := by unfold labels expandedWidth; ring
  rw [hrows]
  exact lt_of_le_of_lt (div_le_div_of_nonneg_right (by exact_mod_cast calls_le_budget hs hc)
    (by positivity)) h

/-- Pick the actual dyadically weighted rectangle system, with the minimum
arity and number of independent rows needed by the template enumeration. -/
theorem exists_system {θ : ℝ} (hθ : 1/2 < θ) :
    ∃ L b m : ℕ, 2 ≤ L ∧ 1 ≤ b ∧ 2 ≤ m ∧ m ≡ 1 [MOD 2] ∧
      ∃ G : PrimeRectangleSystem Dyadic 2 L b,
        5 ≤ axes m G.D ∧ 2 ≤ labels L b * expandedWidth m ∧
        ∀ stage calls : ℕ, stage ≤ stageBound L b m G.D → calls ≤ callBound L b m G.D stage →
          (calls : ℝ)/(labels L b * expandedWidth m : ℕ) < (axes m G.D : ℝ)^θ := by
  obtain ⟨L,b,m,hL,hb,hm,hmod,h⟩ := exists_parameters hθ
  have htwo : IsUnit (2 : Dyadic) :=
    isUnit_iff_exists_inv'.mpr ⟨Dyadic.ofIntWithPrec 1 1, by decide⟩
  obtain ⟨G⟩ := exists_primeRectangleSystem Dyadic 2 L b htwo
  have hd := G.dimension_pos
  have hm3 : 3 ≤ m := by
    change m % 2 = 1 % 2 at hmod
    omega
  refine ⟨L,b,m,hL,hb,hm,hmod,G,by unfold axes; omega,?_,h G.D hd G.dimension_le⟩
  have he : 0 < 2 ^ batchExponent m := by positivity
  have hn : 0 < labels L b := by unfold labels; positivity
  exact (two_le_batchWidth hm).trans ((Nat.le_mul_of_pos_right _ he).trans (Nat.le_mul_of_pos_left _ hn))

/-- A correct compiled plan with the stated per-stage and total bounds
witnesses termination of the uniform finite-program search. -/
theorem exists_good_of_compiler {num den : ℕ} (hθ : 1/2 < (num : ℝ)/den)
    (build : ∀ (L b m : ℕ), 2 ≤ L → 1 ≤ b → 2 ≤ m → m ≡ 1 [MOD 2] →
      ∀ G : PrimeRectangleSystem Dyadic 2 L b,
      let W := labels L b * expandedWidth m
      ∃ p : KernelPass.Plan (axes m G.D) W W, KernelPass.Correct p ∧
        ∃ stage : ℕ, stage ≤ stageBound L b m G.D ∧ p.calls ≤ callBound L b m G.D stage) :
    ∃ t : KernelPass.Candidate, KernelPass.Candidate.Good num den t := by
  obtain ⟨L,b,m,hL,hb,hm,hmod,G,hA,hW,hcost⟩ := exists_system hθ
  obtain ⟨p,hp,stage,hs,hc⟩ := build L b m hL hb hm hmod G
  exact ⟨⟨_,_,p⟩,hA,hW,hp,hcost stage p.calls hs hc⟩

end KernelPassSaving

end NearSquareRoot
end Computability
end OAI
