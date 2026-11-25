import OAI.Computability.BorderVNP.FragmentTaskPublishedRanks
import OAI.Computability.BorderVNP.CellPacketGeometryPublishedCell
import OAI.Computability.BorderVNP.DiagonalNativeReportBindingReadback

/-! # The published original cell packet at each actual signed report return -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.History.Native

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator DiagonalTallyAllocation DiagonalTallyCellReports
open CellPacket CellSparse CellSparse.Packet CellSparse.Packet.Source

variable {w description : ℕ} {l : ReportLayout} {cs : List (ReportCell l)} {q : ReportCursor}
    {pub : Arg → Word w} {m : Memory w} {mac : TeamOpcode.Macros w 8} {s : RoutingISA.Bank w}
    {pre : BeforeTasks} {post : AfterTasks} {banks : CellBanks.Layout}

/-- A public packet occupies the same addresses in any later RAM that
preserves its ordinary and reserved descriptor interval. -/
theorem CellMemory.at_checkpoint {O : Type} {cell : Placed O} {geometry last lo hi : ℕ}
    {old newMem : ℕ → ℕ} (memory : CellMemory cell geometry last old)
    (descriptors : lo≤cell.descriptorBase ∧ last≤hi)
    (words : lo≤cell.publicBase ∧ cell.publicBase+((Supplement.prefixParts cell).flatMap Part.publicBuffer).length≤hi)
    (geom : lo≤geometry ∧ geometry+(fieldList record cell.rows++fieldList vector cell.reports).length≤hi)
    (keep : ∀ addr, lo≤addr → addr<hi → newMem addr=old addr) :
    CellMemory cell geometry last newMem := by
  have retain (a : ℕ) (xs : List ℕ) (h₁ : lo≤a) (h₂ : a+xs.length≤hi) (stored : WordsAt old a xs) :
      WordsAt newMem a xs := by
    intro i
    exact (keep (a+i.val) (h₁.trans (Nat.le_add_right ..)) ((Nat.add_lt_add_left i.isLt a).trans_le h₂)).trans (stored i)
  have limits := memory.endAddress
  refine ⟨retain _ _ descriptors.1 (by have := descriptors.2; omega) memory.prefixDescriptors,
    retain _ _ words.1 words.2 memory.prefixWords,retain _ _ geom.1 geom.2 memory.geometry,?_,?_,limits⟩
  · apply (keep _ geom.1 ?_).trans memory.count
    have endAt := geom.2
    simp only [List.length_append,fieldList,List.length_cons] at endAt
    omega
  · apply retain _ _ (descriptors.1.trans (Nat.le_add_right ..)) _ memory.tail
    change cell.descriptorBase+(CellPacket.descriptors (Supplement.prefixChunks cell)).length+12≤hi
    exact limits ▸ descriptors.2


/-- Reading the original published packet through the count/use guesser gives
the same descriptor, public payload, geometry count and four reserved triples.
The proof applies to every native report return, including arbitrary count guesses. -/
theorem CellMemory.report_return {O : Type} {cell : Placed O} {geometry last lo hi : ℕ}
    (memory : CellMemory cell geometry last (readings m))
    (allocation : ReportAllocation pre post banks l cs q) (seed : PreparedReportInput pub m cs q description)
    (r : Returns prepareCellReports pub mac s m)
    (envelope : l.frame+35<lo ∧ hi≤banks.bankStart)
    (descriptors : lo≤cell.descriptorBase ∧ last≤hi)
    (words : lo≤cell.publicBase ∧ cell.publicBase+((Supplement.prefixParts cell).flatMap Part.publicBuffer).length≤hi)
    (geom : lo≤geometry ∧ geometry+(fieldList record cell.rows++fieldList vector cell.reports).length≤hi) :
    CellMemory cell geometry last (readings r.val.2.2) := by
  let equiv := reportReturnEquiv seed mac s
  let tape := equiv.symm r
  have image := (reportReturnEquiv_spec seed mac s tape).2.2
  rw [show reportReturnEquiv seed mac s tape=r from equiv.apply_symm_apply r,prepareWrites_image] at image
  have keep (addr : ℕ) (lower : lo≤addr) (upper : addr<hi) : readings r.val.2.2 addr=readings m addr := by
    rw [image]
    exact (allocation.tape _ _).prepare_geometry_word _ addr (upper.trans_le envelope.2) (by have := envelope.1; omega)
  exact memory.at_checkpoint descriptors words geom keep

end CellPacketGeometry.History.Native

end BorderVNP
end Computability
end OAI
