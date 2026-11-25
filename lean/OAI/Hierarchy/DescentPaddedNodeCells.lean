import OAI.Hierarchy.DescentOriginalPaddedNodes
import OAI.Hierarchy.DescentReachedNodeCells
import OAI.Hierarchy.DescentPaidResidentCensus

namespace OAI
/-! A dated output rectangle may be wider or narrower than the host calendar. Both
enumerations use the same actual sorted Reached.vertex ordinal. -/
namespace Hierarchy.DescentSixParty.Reached.NodeCells
open DescentKernelHistory DescentLocalArchiveOrder DescentColonies DescentCompiler
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
  {q ε : ℝ} {S : AtomSchedule} {k age grain degree wire hist : ℕ}
  (cap : Reached W G q ε S k age grain degree wire hist) (B : BitDescription W) (ord : Local B)
  {H N : ℕ} (x : Block k) (j : Fin N) (h : Fin H) (g : Fin (S.groupCount age))

theorem atPhysical_live (name : cap.V↪Fin H) (faithful : ∀u,(name u).val=(cap.vertex u).val) :
    (∃z,atPhysical cap B ord x j h g=some z) ↔
      ∃v,DescentPaidResidentCount.occupies cap.placement (Equiv.refl _) name h g x v ∧
        j.val<Fintype.card (B.recipe v).Node:=by
  constructor
  · rintro ⟨⟨v,s⟩,found⟩
    obtain ⟨host,group,block,rank⟩:=(atPhysical_some cap B ord x j h g v s).mp found
    exact ⟨v,⟨Fin.ext ((faithful _).trans host),group,block⟩,by rw [rank];exact (ord v s).isLt⟩
  · rintro ⟨v,⟨host,group,block⟩,room⟩
    let s:=(ord v).symm ⟨j.val,room⟩
    refine ⟨⟨v,s⟩,(atPhysical_some cap B ord x j h g v s).mpr ⟨(faithful _).symm.trans (congrArg Fin.val host),group,block,?_⟩⟩
    simp only [s,Equiv.apply_symm_apply]

end
end Hierarchy.DescentSixParty.Reached.NodeCells

end OAI
