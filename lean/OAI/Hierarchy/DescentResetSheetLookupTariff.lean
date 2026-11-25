import OAI.Hierarchy.DescentPhysicalResetCandidateReturn
import OAI.Hierarchy.DescentResetRankedInvoice
import OAI.Hierarchy.DescentPackedMatchedAll
import OAI.Hierarchy.DescentPackedColumnHardware

namespace OAI
/-! Word and instruction costs of the authentic two candidate sheets, signed rank return, and node archive. -/
namespace Hierarchy.DescentResetCandidatePair
open DescentSIMDLookup DescentResetFieldAssembler DescentPackedColony DescentStaticWordColumn
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section

def scanBill (J rows work : ℕ) :=4+J*(4+rows*(2*work+4))+7*(15+J*(11+4*work))

theorem scan_bill (base rows pitch J w work : ℕ) (read : ℕ→Expr)
    (small : ∀i<J,(read i).work≤work) :
    clock (DescentPackedFlowBatch.passes base rows pitch read 0 J)+
      7*names (ProtocolRAM.program w (DescentPackedFlowBatch.passes base rows pitch read 0 J))
        ≤ scanBill J rows work:=by
  exact Nat.add_le_add (DescentPackedFlowBatch.tariff base rows pitch J read work small)
    (Nat.mul_le_mul_left 7 (DescentOperandVectorArena.names_passes base rows pitch w work read 0 J
      (fun j _ hj=>small j (by simpa using hj))))

theorem pair_bill {X s c p : ℕ} (base bits H G M w headerWork rawWork : ℕ)
    (header raw : Inputs X s c p) (hs : ∀x j,(header x j).work≤headerWork)
    (rs : ∀x j,(raw x j).work≤rawWork) :
    let J:=X*CandidateSheet.size s c p
    time base bits H G M header raw+7*names (program base bits H G M w header raw)≤
      scanBill J (H*chunks G M) headerWork+scanBill J (H*chunks G M) rawWork:=by
  intro J
  have small (src : Inputs X s c p) (L : ℕ) (fit : ∀x j,(src x j).work≤L) (i : ℕ) (hi:i<J) :
      (CandidateSheet.terms src i).work≤L:=by rw [CandidateSheet.terms,dite_eq_left hi];exact fit _ _
  have one:=scan_bill base (H*chunks G M) (2^bits) J w headerWork _ (small header _ hs)
  have two:=scan_bill (originalBase base X (CandidateSheet.size s c p) bits) (H*chunks G M) (2^bits) J w rawWork _
    (small raw _ rs)
  unfold time program prices
  rw [names_seq]
  dsimp only [J] at one two ⊢
  omega

end
end Hierarchy.DescentResetCandidatePair

namespace Hierarchy.DescentResetNodeBooks
open DescentSIMDLookup DescentPacking.PackedMatch.Local DescentOrdinaryAtomFieldRAM DescentStaticWordColumn
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
def invoice (names N H G s M : ℕ) :=
  4+10*volume N s M+7*(15*(volume N s M+1))+
    DescentResetCandidatePair.scanBill names (rows H G M) (1+N*18)

theorem billed (floor old count N H G s M w : ℕ) :
    ticks floor old count N H G s M+7*names (program floor old count N H G s M w)≤ invoice count N H G s M:=by
  have key (p : ℕ) : (term floor old N H G s M p).work≤1+N*18:=by
    simpa only [term,Gather.assembly,List.length_finRange] using
      (Gather.collect_work (tabs floor s N M) (fun n=>.lookup (scalar old N H G M p n) .row)
        (List.finRange N) 7 (fun _=>by change 7≤7; exact Nat.le_refl _))
  have sweep:=DescentResetCandidatePair.scan_bill (output floor count N H G s M) (rows H G M)
    (rows H G M) count w (1+N*18) _ (fun i _=>key i)
  unfold ticks program invoice passes ROM.mount
  rw [names_seq,names_mount]
  change (4+10*volume N s M+_)+7*(15*(volume N s M+1)+_)≤_
  omega

end
end Hierarchy.DescentResetNodeBooks

end OAI
