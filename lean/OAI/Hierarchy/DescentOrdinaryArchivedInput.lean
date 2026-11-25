import OAI.Hierarchy.DescentOrdinarySelectedInputs
import OAI.Hierarchy.DescentArchiveCellReads

namespace OAI
/-! The physically acquired old header and range fields come from the complete previous packed register. -/
namespace Hierarchy.DescentRetainedRangeDigits
open DescentDatedPriorOperand DescentOperandStateBanks DescentSIMDLookup DescentDatedAddressBook
open Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section

def previousPageCell {w : ℕ} (a : PriorResetArchive) (l : Layout) (field : ℕ) (m : Memory w)
    (pos : 0 < l.lanes) (j : ℕ) (f : Fin 7) (b : Fin l.blocks) (h : Fin l.hosts)
    (g : Fin l.groups) : Cell (field*l.nodes) :=
  if live : j < l.operands then archivedCell a l field m pos (DescentOperandStateBanks.page f ⟨j,live⟩) b h g else 0

theorem previous_page_range {w : ℕ} (a : PriorResetArchive) (l : Layout) (field : ℕ) (m : Memory w)
    (pos : 0 < l.lanes) (j : ℕ) (f : Fin 3) (b : Fin l.blocks) (h : Fin l.hosts) (g : Fin l.groups) :
    previousPageCell a l field m pos j (page f) b h g = previousRangeCell a l field m pos j f b h g := rfl

end
end Hierarchy.DescentRetainedRangeDigits

namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary.ArgumentEntry
open DescentDatedPriorOperand DescentOperandStateBanks DescentSIMDLookup DescentDatedAddressBook DescentRetainedRangeDigits
open Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (A : ArgumentEntry v)
    (S : A.InputShape v) (floor : ℕ) («matching» : A.Match v floor)
    {w : ℕ} (a : PriorResetArchive) (m : Memory w) (pos : 0 < A.previous.lanes)
local notation "old₀" => (fun p b => archivedCell a A.previous (A.previous.size+2) m pos p b)

theorem old_archived_input (f : Fin 7) (j : Fin v.vector.operands) (b : Fin (2^v.reference.k))
    (h : Fin A.clip.venue.hosts) (g : Fin A.clip.venue.groups) (actual : h.val < A.previous.hosts) :
    (A.oldInput v S floor «matching» old₀ (DescentOperandStateBanks.page f j) b h g).val =
    (previousPageCell a A.previous (A.previous.size+2) m pos j.val f
      (b.cast «matching».oldBlocks.symm) ⟨h.val,actual⟩ (g.cast S.prevGroups)).val := by
  by_cases active : j.val < A.previous.operands
  · simp [oldInput,oldField,rowsAt,DescentOperandStateBanks.page,Equiv.symm_apply_apply,
      DescentOrdinaryPriorPad.extend,DescentOrdinaryHostPad.extend,previousPageCell,active,actual]
    rfl
  · simp [oldInput,rowsAt,DescentOperandStateBanks.page,Equiv.symm_apply_apply,previousPageCell,active]

theorem old_archived_range (f : Fin 3) (j : Fin v.vector.operands) (b : Fin (2^v.reference.k))
    (h : Fin A.clip.venue.hosts) (g : Fin A.clip.venue.groups) (actual : h.val < A.previous.hosts) :
    (A.oldInput v S floor «matching» old₀
      (DescentOperandStateBanks.page (DescentRetainedRangeDigits.page f) j) b h g).val =
    (previousRangeCell a A.previous (A.previous.size+2) m pos j.val f
      (b.cast «matching».oldBlocks.symm) ⟨h.val,actual⟩ (g.cast S.prevGroups)).val :=
  A.old_archived_input v S floor «matching» a m pos _ j b h g actual

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary.ArgumentEntry

end OAI
