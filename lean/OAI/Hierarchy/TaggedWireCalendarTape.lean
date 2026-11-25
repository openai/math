import OAI.Hierarchy.TaggedWireTapeAdmission
import OAI.Hierarchy.TaggedWireCalendarHistory

namespace OAI
/-! # The exact private tape of a calendar with different histogram extents at each event -/

noncomputable section
namespace Hierarchy.WireTelescope.CalendarTape
open ProtocolRAM ProtocolRAM.Calendar Tagged
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph
open scoped Classical

variable {X : Type} {W q d S : ℕ} {F : Type*} [Field F]

variable (slot : Event→Slot X)

def expansion (wire : X→Widths S) (stage : ∀ e x,Expansion (raw F (wire x)) ((slot e).choice x)
    (fun c=>wire ((slot e).next x c))) : (es : List Event) → (x : X) →
    Expansion (raw F (wire x)) (Path slot es x) (fun p=>wire (terminal slot es x p))
  | [],x=>Expansion.transport (wire x) (restrict_refl _)
  | e::es,x=>(stage e x).bind (fun c=>expansion wire stage es ((slot e).next x c))

end Hierarchy.WireTelescope.CalendarTape

end
end OAI
