import OAI.Computability.VPVNP.PrimedInputRAMCapacity
import OAI.Computability.VPVNP.PrimedInputRAMOpcodeExecutionResult

/-!
# The input passes at the paper's live and virtual parameters

For one fixed choice of the address multiplier, all sufficiently large
lengths support every primed pair. Its actual fixed opcode table respects
the auxiliary per-call work and probe caps, and the `R′K′` total budget.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedInputRAM

open BurstRAM CursorBounds Compression Opcodes Filter

/-- Six elementary word operations per instruction include dispatch and
operand handling. The complete private fuel is eventually below the
auxiliary machine's `n^10` work cap, independently of the pair. -/
theorem eventually_nativeInputWork (B : ℕ) :
    ∀ᶠ n : ℕ in atTop, 6 * nativeFuel (addressWidth B n) ≤ n^10 := by
  filter_upwards [eventually_ge_atTop (6*(3*B+165)), eventually_ge_atTop 1] with n hn hp
  have hclog : Nat.clog 2 n ≤ n := (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr Nat.lt_two_pow_self.le
  have hr : addressWidth B n ≤ B*n := Nat.mul_le_mul_left _ hclog
  have hadd : 165 ≤ 165*n := Nat.le_mul_of_pos_right _ hp
  calc
    6*nativeFuel (addressWidth B n) ≤ 6*((3*B+165)*n) := by
      rw [Nat.add_mul, Nat.mul_assoc]
      unfold nativeFuel
      omega
    _ = (6*(3*B+165))*n := (Nat.mul_assoc ..).symm
    _ ≤ n^2 := by simpa [pow_two] using Nat.mul_le_mul_right n hn
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide : 2 ≤ 10)

/-- Simultaneous layout, private word fit and exact auxiliary budgets for the
physical assembler, uniformly for all group pairs and histogram lengths. -/
theorem eventually_physicalLayouts (p : UniversalMachine.Program) (a d₁ d₂ C B : ℕ)
    (hB : max (max (a+1) (a+d₂)) (max d₁ C) + 2 ≤ B) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1) :
    ∀ᶠ n : ℕ in atTop, ∀ i : Fin (2^(n^a-1)), ∀ t ≤ n^C,
      let L := PairedChain.lengths (n^a-1) (n^d₂) (n^d₁) i
      let r := addressWidth B n
      let S := 2^(virtualBits B n)
      let K := 2^(roundedUp 1 4 n)
      ∃ Q : Layout L n r (liveBucket δ n) (CursorBounds.wordBits B n),
        Q.program = p ∧ Q.scratchBase = S ∧ Header.count L+t ≤ S ∧ ParameterFit Q ∧
        6 ≤ K ∧ 11 * positions n r + 1 ≤ S*K ∧ 6*nativeFuel r ≤ n^10 := by
  have hpos : 1 ≤ B := by omega
  filter_upwards [eventually_pairedLayouts p a d₁ d₂ C B hB hδ hδ',
    eventually_parameterFit p hpos, eventually_virtualBucket_ge 6, eventually_pairExternalBudget B 22,
    eventually_nativeInputWork B] with n hQ hF hK htotal hwork
  intro i t ht
  obtain ⟨Q,hp,hs,hh⟩ := hQ i t ht
  have hx := htotal 0 (Nat.zero_le _)
  have he : 11 * positions n (addressWidth B n) = 22 * (processorCount B n*n) := by
    unfold positions processorCount addressBits
    ring
  refine ⟨Q,hp,hs,hs ▸ hh,hF _ _ Q hp,hK,?_,hwork⟩
  rw [he]
  omega

end PrimedInputRAM

end VPVNP
end Computability
end OAI
