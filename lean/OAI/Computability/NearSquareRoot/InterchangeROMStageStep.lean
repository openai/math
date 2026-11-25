import OAI.Computability.NearSquareRoot.InterchangeROMStageLedger
import OAI.Computability.NearSquareRoot.InterchangeROMStageVolumeNative

/-! # The exact open-recursion contract of the generated rectangle stage -/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section
namespace InterchangeROMStage
open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip IntegerMultiplication.Loom
  Space InterchangeSpace Frame.Realization InterchangeROMStageVolume InterchangeROMStageTable
  InterchangeROMSequence

variable {Q A Y : Type} (c : Parameters) (r : Frame.Realization c.1) [Fact c.2.1.Prime]
  (addr : Series A) (payload : Series Y) (π : r.NativeMove → Equiv.Perm (A × Y))
  (data : Fin (Frame.labels c.1) → A × Y → Fin c.2.2.1 → ZMod c.2.1)

/-- Total number of scalar field words, including identity words. Identity
words contribute no entries to the separate recursive request list. -/
def fieldCount (g : Frame) (d : ℕ) := ∑ k : Fin 6, ((g.bank (routePos k+1)).length*d)

open private primrec_finite_sum from OAI.Computability.NearSquareRoot.InterchangeROMStageVolumeCoefficient

theorem primrec_fieldCount : Primrec₂ fieldCount := by
  apply primrec_finite_sum Finset.univ
  intro k _
  exact Primrec.nat_mul.comp (Primrec.list_length.comp (Frame.primrec_bank Primrec.fst (routePos k+1)))
    Primrec.snd

theorem step (job : Job Q) (charts : List Opcode.Word) (wordCmd : Opcode.Word → Cmd) (header : Tree)
    (requests : (k : Fin 6) → r.Field c.2.2.1 k → List Q) (W S D : ℕ)
    (active : ∀ k : Fin 5, 0 < (c.1.bank (inputBoundary k)).length*c.2.2.1)
    (movement : ∀ k z d, Step job (wordCmd (lookup charts (r.operand (r.moveAt k z)))) header
      (runRow c r addr payload π data (routePos k) (r.srcAt k z) d)
      (runRow c r addr payload π data (routePos k+1) z d) (requests k (z,d)) W S D) :
    let m := mass header addr.count payload.count
    Step job (rawStage c.1 c.2.1 c.2.2.1 (gateMatrix c) charts wordCmd) header
      (r.Tape 0 c.2.2.1 (runRow c r addr payload π data 0))
      (runState c r addr payload π data header 11)
      (r.ledger c.2.2.1 requests) (stageFactor c*m+fieldCount c.1 c.2.2.1*W)
      (localFactor c*m+S) (localFactor c*m+D+1) := by
  dsimp only
  intro parent env price size depth children deck base live
  let qs := r.ledger c.2.2.1 requests
  let time := fun k (z : r.Field c.2.2.1 k) => W+costSum price (requests k z)
  let acc := childPeak size qs
  let stack := childPeak depth qs
  have member {k : Fin 6} {z : r.Field c.2.2.1 k} {q : Q} (hq : q ∈ requests k z) : q ∈ qs :=
    (r.mem_ledger _).mpr ⟨k,z,hq⟩
  have localRun (k : Fin 6) (z : r.Boundary (routePos k+1)) (d : Fin c.2.2.1)
      (rest : Deck) (b : ℕ) (hrest : DeckCap b rest) :
      BoundedFits (parent::env) (wordCmd (lookup charts (r.operand (r.moveAt k z))))
        (pile 0 (.fork header (runRow c r addr payload π data (routePos k) (r.srcAt k z) d)) rest)
        (pile 0 (runRow c r addr payload π data (routePos k+1) z d) rest)
        (time k (z,d)) (b+(S+acc)) (D+stack) := by
    have h := movement k z d parent env price size depth
      (fun q hq => children q (member hq)) rest b hrest
    have u := childPeak_le size (requests k (z,d)) acc (fun q hq => le_childPeak size (member hq))
    have v := childPeak_le depth (requests k (z,d)) stack (fun q hq => le_childPeak depth (member hq))
    exact h.mono le_rfl (by omega) (by omega)
  have run := native c r addr payload π data header (S+acc) (D+stack) charts wordCmd
    (parent::env) time active localRun deck base live
  have total := r.aggregate c.2.2.1 requests price W
  rw [← Finset.sum_mul] at total
  change (∑ k : Fin 6, costSum (time k) (r.cells (routePos k+1) c.2.2.1)) =
    fieldCount c.1 c.2.2.1*W+costSum price qs at total
  dsimp only at run
  rw [total] at run
  simpa only [costSum,runState,Nat.add_assoc,Nat.add_right_comm _ stack 1,acc,stack,qs] using run

end InterchangeROMStage

end

end NearSquareRoot
end Computability
end OAI
