import OAI.Hierarchy.DescentIssuedRootRoom

namespace OAI
/-! # The root catalogue preserves the matrix operands used by the sender -/
namespace Hierarchy.DescentFallbackPeriod.Projected.Receiver
open DescentSIMDLookup DescentPackedZip DescentSixParty.Chronology
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable {D cap N n r c H G K R M h l t field Ht w : ℕ}
    (a : Receiver D cap N n r c H G K R M h l t field Ht w) (b : RootBook n r D (2^r) cap field)
local notation "groups" => 2^c

theorem before_header (space : a.PreparedFits b) (mem : Memory w) (x : ℕ) (earlier : x<a.headerEnd b) :
    a.preparedImage b space mem x=a.preparedMid b space mem x :=
  ((a.rootedTemplates b).run (a.headerEnd b) space.rows (a.preparedMid b space mem)).2.2 x (.inl earlier)

/-- The sender source uses the same measured coordinates and comparison words at the end
of the root jobs. The chart supplying the input-width proof is the one that assembled the book. -/
theorem final_matrix_rows (space : a.PreparedFits b) (mem : Memory w)
    (src : RootSources D (2^r) cap)
    (room : src.OperandRoom H groups M w (a.headerEnd b))
    (values : Fin H→Fin groups→Fin (DescentRotorWindowArchive.count D (2^r) cap)→Cell field)
    (rows : ∀j,Source (src.matrixRow H j) (fun v hi=>values v hi j) M (a.preparedMid b space mem)) :
    ∀j,Source (src.matrixRow H j) (fun v hi=>values v hi j) M (a.preparedImage b space mem) := by
  intro j p
  exact (eval_below _ _ (a.preparedMid b space mem) (a.preparedImage b space mem)
    (src.matrix_fit room j) (a.before_header b space mem)).trans (rows j p)

end
end Hierarchy.DescentFallbackPeriod.Projected.Receiver

end OAI
