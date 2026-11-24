import OAI.Computability.VPVNP.LiveVirtualPairHistograms

/-! # Equating terminal job flushes with the canonical pair histogram

The terminal interpreter may enumerate its local jobs in a different order from
the compressed witness's histograms. The accumulated counters agree in every
cell as soon as the integer increment sums agree for each motif label.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.Counters

open BurstRAM

theorem visit_eq_of_sums {A B : Type*} {g w : ℕ} (base grammar : ℕ) (f : A → Fin g → ℕ) (u : List A)
    (h : B → Fin g → ℕ) (v : List B) (m : Memory w)
    (sums : ∀ j : Fin g, (u.map (fun a => f a j)).sum = (v.map (fun b => h b j)).sum) :
    visit base grammar f u m = visit base grammar h v m := by
  funext a
  by_cases inside : base+grammar ≤ a ∧ a < base+grammar+g
  · let j : Fin g := ⟨a-(base+grammar),by omega⟩
    have addr : a = base+grammar+j.val := by dsimp [j]; omega
    rw [addr,visit_at,visit_at,sums j]
  · have outside : a < base+grammar ∨ base+grammar+g ≤ a := by omega
    rw [visit_outside _ _ _ _ _ _ outside, visit_outside _ _ _ _ _ _ outside]

end PairSimulation.Counters

namespace FixedProgramDiagonal.Program

open Compression CursorNetwork BurstRAM LabelEvaluator ExponentTrace PairSimulation

universe v
variable {D : FixedProgramDiagonal.Program} {n C : ℕ} {K : Type v} [Field K] {S : BlockSchedule K}
    {B : S.Templates} {hn : 2 ≤ n} {p : Nat.Primes}
    {M : Model p (B.compressorDegree n) (B.compressorEquations hn C)}
    (data : D.ScalarData B hn M)
    (processorFit : ProcessorInput.Fits D.literal n (D.geometry n).d (D.geometry n).H (D.geometry n).w)
    {u : PairExponents B.growthConstant} (V : D.VirtualPairs B u hn C)
    (ξ : Exterior (D.chainHeight n) (n^D.constants.deltaPower)) (i : D.groupIndices n) (μ : D.pairNom n C)
    (q : (V.pairData data processorFit).Path ξ i μ)

/-- The ordered final-site histograms sum to the exponent of this very occurrence. -/
theorem VirtualPairs.histograms_sum (l : B.Entry) :
    ((V.histograms data processorFit ξ i μ q).map (fun h => h l)).sum =
      (V.pairData data processorFit).ν ξ i μ q l := by
  exact Counters.vertexHistograms_sum _ _ _ _ _ q l

/-- A terminal visit in any physical site order flushes precisely the canonical
counter memory when its local job increments sum to the witness exponents. -/
theorem VirtualPairs.siteFlushes_eq {Site : Type*} [Fintype Site] {N g w : ℕ}
    (sites : Fin N ≃ Site) (counts : Site → B.Entry → ℕ)
    (powers : ∀ l, (∑ v, counts v l) = (V.pairData data processorFit).ν ξ i μ q l)
    (base grammar : ℕ) (order : Fin g → B.Entry) (m : Memory w) :
    Counters.visit base grammar (fun site j => counts site (order j)) (List.ofFn sites) m =
      Counters.visit base grammar (fun (h : B.Entry → ℕ) j => h (order j))
        (V.histograms data processorFit ξ i μ q) m := by
  apply Counters.visit_eq_of_sums
  intro j
  rw [V.histograms_sum data processorFit ξ i μ q, ← powers]
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply]
  exact sites.sum_comp (fun v => counts v (order j))

end FixedProgramDiagonal.Program

end VPVNP
end Computability
end OAI
