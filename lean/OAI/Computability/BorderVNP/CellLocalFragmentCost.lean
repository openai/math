import OAI.Computability.BorderVNP.CellLocalBlockCost
import OAI.Computability.BorderVNP.CellLocalFactorLength

/-! # Native per-box factor-template costs on the actual local packet

Local computation pays a polynomial in binary metadata widths. Repeated box copies are
represented by a single binary loop bound. The cost for assembling the factor list is a
ninth-degree polynomial in the size of the actual one-copy block, times its factor count.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Emit.Local

open ExactQuantumFactoring.BitStackProgram

/-- The local input passed to the factor at its original one-copy ordinal. -/
abbrev factorAt (b : BlockArg) (i : Fin b.2.2.factors.length) : Input :=
  ((prepare b).1,i.val,b.2.2.factors[i])

/-- Complete actual cost of preparing and printing a block. The bound on child calls is
separate from the encoded size, so directory traversal is never substituted into the clock
of a per-factor table printer. -/
theorem fragment_meter (mode : Pass) : ∃ K : ℕ, ∀ (b : BlockArg) (P : ℕ),
    (∀ i, (printer mode).meter (factorAt b i) ≤ P) →
    (fragment mode).meter b ≤ K*(b.2.2.factors.length+1)*((blockArgCode b).length+1)^9*(P+1)^2 := by
  obtain ⟨K₁,prep⟩ := prepareBlock_measured
  obtain ⟨K₂,print⟩ := blockPrinter_meter mode
  refine ⟨6*(K₁+K₂*8^9),fun b P child => ?_⟩
  let n := b.2.2.factors.length+1
  let S := (blockArgCode b).length+1
  let F := P+1
  have hc := print (prepare b) P child
  have hp := prep b
  change prepareBlock.meter b ≤ K₁*S^4 at hp
  change (blockPrinter mode).meter (prepare b) ≤ K₂*n*((blockDataCode (prepare b)).length+1)^9*F^2 at hc
  have hl := Nat.pow_le_pow_left (prepare_length b) 9
  change ((blockDataCode (prepare b)).length+1)^9 ≤ (8*S)^9 at hl
  have hs : S^4 ≤ S^9 := Nat.pow_le_pow_right (by dsimp [S]; omega) (by decide)
  have hpad : S^9 ≤ n*S^9*F^2 := by
    have hn : 1 ≤ n := by dsimp [n]; omega
    have hF : 1 ≤ F^2 := Nat.one_le_pow _ _ (by dsimp [F]; omega)
    simpa only [Nat.one_mul,Nat.mul_one] using (Nat.mul_le_mul (Nat.mul_le_mul_right (S^9) hn) hF)
  have a : prepareBlock.meter b ≤ K₁*(n*S^9*F^2) :=
    hp.trans (Nat.mul_le_mul_left _ (hs.trans hpad))
  have c : (blockPrinter mode).meter (prepare b) ≤ (K₂*8^9)*(n*S^9*F^2) := by
    apply hc.trans
    calc K₂*n*((blockDataCode (prepare b)).length+1)^9*F^2 ≤ K₂*n*(8*S)^9*F^2 := by gcongr
         _ = _ := by ring
  unfold fragment
  rw [Procedure.meter_congrFun]
  apply (Procedure.meter_comp _ _ b).trans
  calc 6*(prepareBlock.meter b+(blockPrinter mode).meter (prepare b)) ≤
        6*(K₁*(n*S^9*F^2)+(K₂*8^9)*(n*S^9*F^2)) := Nat.mul_le_mul_left _ (Nat.add_le_add a c)
       _ = _ := by dsimp [n,S,F]; ring

private theorem fragment_power (mode : Pass) (H j : ℕ) : ∃ K : ℕ, ∀ (W : ℕ) (b : BlockArg),
    (∀ i, (printer mode).meter (factorAt b i) ≤ H*(W+1)^j) →
    (fragment mode).meter b ≤ K*(b.2.2.factors.length+1)*((blockArgCode b).length+1)^9*(W+1)^(2*j) := by
  obtain ⟨K,frag⟩ := fragment_meter mode
  refine ⟨K*(H+1)^2,fun W b child => ?_⟩
  let P := H*(W+1)^j
  have hp : P+1 ≤ (H+1)*(W+1)^j := by
    have hpow : 1 ≤ (W+1)^j := Nat.one_le_pow _ _ (by omega)
    dsimp [P]
    rw [Nat.add_mul,Nat.one_mul]
    omega
  apply (frag b P child).trans
  calc K*(b.2.2.factors.length+1)*((blockArgCode b).length+1)^9*(P+1)^2 ≤
        K*(b.2.2.factors.length+1)*((blockArgCode b).length+1)^9*((H+1)*(W+1)^j)^2 := by gcongr
       _ = _ := by rw [Nat.mul_pow,← pow_mul,Nat.mul_comm j 2]; ring

/-- The bound in the binary field width accommodates global identifiers of arbitrary
magnitude. Only the actual lengths of their transported words enter the local printer. -/
theorem fragment_meter_fields_width (mode : Pass) (A : ℕ) : ∃ C j : ℕ, ∀ (U : ℕ) (b : BlockArg),
    (∀ i, ScalarFields (factorAt b i) U) →
    (∀ f ∈ b.2.2.factors, FactorFields f U ∧ f.TableBound A) →
    (fragment mode).meter b ≤ C*(b.2.2.factors.length+1)*((blockArgCode b).length+1)^9*(U.size+1)^j := by
  obtain ⟨H,j,perSite⟩ := printer_meter_fields_width mode A
  obtain ⟨C,bound⟩ := fragment_power mode H j
  refine ⟨C,2*j,fun U b hs hf => bound U.size b ?_⟩
  intro i
  have h := hf b.2.2.factors[i] (List.getElem_mem ..)
  exact perSite (factorAt b i) U (hs i) h.1 h.2

/-- At each fixed table arity and row bound, polynomially bounded binary scalars give a
polylogarithmic factor in the input order. The exponent in the block's own encoded size is
uniform over the three passes. -/
theorem fragment_meter_polynomial_fields (mode : Pass) (A B k : ℕ) : ∃ C j : ℕ, ∀ (n U : ℕ) (b : BlockArg),
    U ≤ B*(n+2)^k →
    (∀ i, ScalarFields (factorAt b i) U) →
    (∀ f ∈ b.2.2.factors, FactorFields f U ∧ f.TableBound A) →
    (fragment mode).meter b ≤ C*(b.2.2.factors.length+1)*((blockArgCode b).length+1)^9*(n.size+1)^j := by
  obtain ⟨H,j,perSite⟩ := printer_meter_polynomial_fields mode A B k
  obtain ⟨C,bound⟩ := fragment_power mode H j
  refine ⟨C,2*j,fun n U b hu hs hf => bound n.size b ?_⟩
  intro i
  have h := hf b.2.2.factors[i] (List.getElem_mem ..)
  exact perSite n U _ hu (hs i) h.1 h.2

end CellSparse.Packet.Emit.Local

end BorderVNP
end Computability
end OAI
