import OAI.Hierarchy.DescentPackedMinimum
import OAI.Hierarchy.DescentColonySearchHardware
import OAI.Hierarchy.ProtocolRAMSumScoresCheap

namespace OAI
/-! # Instruction and storage cost of the packed score accumulator and candidate search -/

namespace Hierarchy.DescentPackedMinimum
open DescentSIMDLookup DescentPackedScore ProtocolRAM DescentColonies.CandidateRAM
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
variable {q : ℕ}

theorem accumulator_hardware (src dict : Bank) (out bound H r M w : ℕ) :
    Bounded (raw src dict out bound H r M w) (4+(H*chunks r M+1)*66) := by
  refine ⟨PruneFlag.cheap w out (H*chunks r M) bound (read src dict),?_⟩
  simp only [storage,raw,SumScores.procedure,PhysicalInputPhases.writing,Term.labels_eq,SumScores.step_binds,
    DescentPackedScore.read,Expr.work]
  omega

theorem issue_hardware (L : Layout q) (w H r M : ℕ) (xs : List (Fin q)) :
    Bounded (program L w H r M xs) (4+xs.length*cost L.work (H*chunks r M)) := by
  induction xs with
  | nil=>
    refine ⟨@scan_cheap _ _ _ _,?_⟩
    obtain ⟨labels,regs,slots⟩ := scan_size w L.work 0 (.lit 0)
    simp only [program,List.length_nil,Nat.zero_mul,Nat.add_zero,storage,labels,regs,slots,Expr.work]; decide
  | cons i is ih=>
    have collect:=accumulator_hardware (L.source i) (L.dictionary i) L.work 0 H r M w
    have copyBound:=scan_bound w (L.ledger.base+i.val) 1 (fetch L.work (H*chunks r M)) (by decide)
    convert seq_bound (seq_bound ih collect) copyBound using 1 <;> simp [program,copy,cost,List.length_cons]; ring

theorem search_hardware (L : Layout q) (w H r M : ℕ) :
    Bounded (search L w H r M) ((4+q*cost L.work (H*chunks r M))+
      DescentFirstMinimumRAM.ticks L.result L.ledger (List.range q)) := by
  simpa [search] using seq_bound (issue_hardware L w H r M (List.finRange q))
    (DescentFirstMinimumRAM.code_bound w L.result L.ledger (List.range q))

end Hierarchy.DescentPackedMinimum

end OAI
