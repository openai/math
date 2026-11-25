import OAI.Computability.BorderVNP.CellLocalSweepMeter
import OAI.Computability.BorderVNP.CellLocalFragmentCost

/-! # Charging a whole native sweep by its actual factor-printer invocations -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Emit.Local

open ExactQuantumFactoring.BitStackProgram

set_option maxHeartbeats 3600000
set_option maxRecDepth 30000

/-- The uniform native clock for the complete compact sweep requires only a bound on
its individual fixed site-printer calls. No field or copied occurrence is expanded by
the compiler's directory traversal. -/
theorem sweepPrinter_rows_meter (mode : Pass) :
    ∃ K : ℕ, ∀ (x : SweepInput) (P : ℕ),
      (∀ (i : Fin x.2.blocks.length) (k : Fin x.2.blocks[i].factors.length),
        (printer mode).meter (factorAt (visit x i x.2.blocks[i]) k) ≤ P) →
      (sweepPrinter mode).meter x ≤ K*(P+1)^4*(sweepSpan x+1)^31 := by
  obtain ⟨F,frag⟩ := fragment_meter mode
  obtain ⟨S,sweep⟩ := sweepPrinter_meter mode
  let V := F*5^9
  refine ⟨S*(V+1)^2,fun x P hp => ?_⟩
  let t := sweepSpan x+1
  let H := V*(P+1)^2
  have ht : 1 ≤ t := Nat.succ_le_succ (Nat.zero_le _)
  have child (i : Fin x.2.blocks.length) :
      (fragment mode).meter (visit x i x.2.blocks[i]) ≤ H*t^14 := by
    let b := x.2.blocks[i]
    have hb : b ∈ x.2.blocks := List.getElem_mem ..
    have hi := list_length_le_code Typed.factor b.factors
    have hw := code_le_of_mem blockCode hb
    have hn : b.factors.length+1 ≤ t := by
      dsimp only [t,sweepSpan,blockSpan]
      simp only [blockCode,prodCode,pairBits_length] at hw
      omega
    have ha := visit_arg_size x i b hb
    have hc := frag (visit x i b) P (hp i)
    change (fragment mode).meter (visit x i b) ≤
      F*(b.factors.length+1)*((blockArgCode (visit x i b)).length+1)^9*(P+1)^2 at hc
    calc (fragment mode).meter (visit x i b) ≤ _ := hc
      _ ≤ F*t*(5*t)^9*(P+1)^2 := Nat.mul_le_mul_right _ (Nat.mul_le_mul
        (Nat.mul_le_mul_left F hn) (Nat.pow_le_pow_left ha 9))
      _ = H*t^10 := by dsimp only [H,V]; ring
      _ ≤ H*t^14 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right ht (by decide))
  have hb := sweep x H child
  have hz : 1 ≤ (P+1)^2 := Nat.one_le_pow _ _ (by omega)
  have hbig : H+1 ≤ (V+1)*(P+1)^2 := by
    rw [Nat.add_mul,Nat.one_mul]
    dsimp only [H]
    omega
  have hm := Nat.mul_le_mul_right (t^31) (Nat.mul_le_mul_left S (Nat.pow_le_pow_left hbig 2))
  calc (sweepPrinter mode).meter x ≤ S*(H+1)^2*t^31 := hb
    _ ≤ S*((V+1)*(P+1)^2)^2*t^31 := hm
    _ = _ := by simp only [Nat.mul_pow,← pow_mul,Nat.mul_assoc,t]

end CellSparse.Packet.Emit.Local

end BorderVNP
end Computability
end OAI
