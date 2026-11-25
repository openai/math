import OAI.Hierarchy.TaggedWirePathCore
import OAI.Hierarchy.TaggedWireShelf
import OAI.Hierarchy.ProtocolRAMCalendarRun

namespace OAI
/-! # The menu-dependent finite choices at each native calendar event -/

noncomputable section
namespace Hierarchy.WireTelescope.CalendarTape
open ProtocolRAM ProtocolRAM.Calendar ProtocolRAM.PurchaseStage Tagged
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM
open scoped Classical

variable {X : Type} {W q d : ℕ}

structure HistogramFormat (C : Chart W q d) (X : Type) where
  bank : Attempt→Bank
  fields : ∀a j,(C.raw a).batch.field j=HistogramShelf.field (bank a) j
  fits : ∀a,(C.layout a).candidates*q≤(bank a).size
  room : ∀a,(C.layout a).candidates*q≤2^W
  letters : (a : Attempt)→X→Fin (C.layout a).candidates→ℕ
  copies : (a : Attempt)→X→Fin (C.layout a).candidates→ℕ
  width : ∀a x i,letters a x i≤q
  count : ∀a x i,copies a x i<2^W
  commit : ∀a x,BallChoices (letters a x) (copies a x)→X
  boundary : Boundary→X→X

namespace HistogramFormat
variable {C : Chart W q d} (F : HistogramFormat C X)

def slot : Event→Slot X
  | .attempt a=>
    { bits := ((C.layout a).candidates*q)*W
      choice := fun x=>BallChoices (F.letters a x) (F.copies a x)
      finite := fun _=>inferInstance
      word := fun x=>selectorTable _ _ (F.width a x) (F.count a x)
      next := F.commit a }
  | .feed b=>feed (F.boundary b)

end HistogramFormat
end Hierarchy.WireTelescope.CalendarTape
end

end OAI
