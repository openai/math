import OAI.Hierarchy.TaggedWideBranchRoleMap
import OAI.Hierarchy.TaggedWideCalendarFirst

namespace OAI
/-! # Endpoint transports of a funded role map -/
noncomputable section
namespace Hierarchy.WireTelescope.NamedAperture
open LinearAlgebra.SpectralBooks ChordGraph CalendarTape

theorem transport_path {K : ℕ} {A B C : Widths K} {V : Type}
    (ab:A=B) (bc:B=C) (ac:A=C) (f:(Σs,SiteBit A s)↪V) :
    (transport ac).symm.toEmbedding.trans f =
      (transport bc.symm).toEmbedding.trans ((transport ab.symm).toEmbedding.trans f) := by
  subst B
  subst C
  rfl

end Hierarchy.WireTelescope.NamedAperture

namespace Hierarchy.WireTelescope.CalendarTape.Prefix
open ProtocolRAM.Calendar
theorem boundaryIndex_zero {X:Type} {slot:Event→Slot X} {es : List Event} {start:X} (j:Path slot es start) :
    boundaryIndex j 0=atCursor (Prefix.start : Prefix slot es start es start) := by
  cases es <;> rfl
end Hierarchy.WireTelescope.CalendarTape.Prefix

namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.BranchRoles
open LinearAlgebra.SpectralBooks ChordGraph
open AdaptiveProbe ReportSockets ProtocolRAM.Calendar WireTelescope CalendarTape
open scoped Classical
variable {X:Type} {slot:Event→Slot X} {es:List Event} {x:X}
variable {h W k jobs depth : ℕ} {S : PurchaseSampler} {π : Equiv.Perm (Fin (2^h))}
variable {cap : Public S h W k jobs → ℕ}
    {wire : Prefix.Cursor slot es x → Widths (siteLast h (2^W) k + 1)}
    (possible : ∀ c : Prefix.Cursor slot es x, Nonempty (Path slot c.todo c.mem))
    (R : ∀ j : Path slot es x, BranchRoles S π depth cap wire j) (j : Path slot es x)

/-- Re-express any reached boundary in a second, mathematically equal named
quantity family. This applies to the matching at time zero and the settled
output matrix after the final feed. -/
theorem endpoint_mapping (t:Fin (es.length+1)) (s : Prefix.Cursor slot es x) (located:Prefix.boundaryIndex j t=s)
    (qty:Fin (R j).count→ℕ) (data:(R j).bits t=qty) (width:Widths (siteLast h (2^W) k + 1))
    (bridge:installedWidths (sorted S π depth (R j).mark ∘ (R j).order) qty=width)
    (head:width=wire s)
    (room:∀e side,qty e≤cap (named S π depth (R j).mark (R j).exclusive (R j).order (e,side))) :
    cells possible R j s = (NamedAperture.transport head.symm).toEmbedding.trans
      ((NamedAperture.transport bridge.symm).toEmbedding.trans
        (statePlace S π depth (R j).mark (R j).exclusive (R j).order qty cap room)) := by
  subst s
  subst qty
  exact (cells_at possible R j t).trans
    (NamedAperture.transport_path bridge head ((R j).atWidth t)
      (statePlace S π depth (R j).mark (R j).exclusive (R j).order ((R j).bits t) cap room))

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.BranchRoles
end

end OAI
