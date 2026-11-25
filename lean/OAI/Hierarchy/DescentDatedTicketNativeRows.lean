import OAI.Hierarchy.DescentDatedOperandTicketValue
import OAI.Hierarchy.DescentDatedTicketDigit

namespace OAI
/-! # Reading the unique native selector heads at a single packed row -/
namespace Hierarchy.DescentDatedOperandReadPipeline
open DescentDatedOperandCoordinates DescentSIMDLookup Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable (g : Geometry) (v : Data g) (j : Fin g.jobs) (h : Fin g.hosts) (k : Fin g.groups)

def rawKey := rawLaw g.paths (g.blocks*(g.cap*11)) g.digitBits 0 (fun i=>rawInputs g v j i h k)

def anchorChoice := anchorLaw g.paths g.blocks g.cap g.digitBits 0 (fun i=>anchorInputs g v j i h k)

def pathChoice := pathLaw g.paths g.degree g.digitBits 0 (fun i=>pathInputs g v j i h k)

theorem pathV_at (i : Fin (g.paths*(g.degree+1))) (selected : (pathChoice g v j h k).val=i.val+1) :
    pathV g v j 0 h k=v.path i h k :=
  DescentResetStemMux.pick_actor (pathChoice g v j h k) (fun t=>v.path t h k) i selected

theorem anchorV_at (a : Fin (g.paths*(g.blocks*(g.cap*3))))
    (selected : (anchorChoice g v j h k).val=a.val+1) (f : Fin 5) :
    anchorV g v j f h k=v.anchor j f a h k :=
  DescentResetStemMux.pick_actor (anchorChoice g v j h k) (fun i=>v.anchor j f i h k) a selected

theorem rawV_at (i : Fin (g.paths*(g.blocks*(g.cap*11))))
    (selected : (rawKey g v j h k).val=i.val+1) (f : Fin 8) :
    rawV g v j f h k=v.raw j f i h k :=
  DescentResetStemMux.pick_actor (rawKey g v j h k) (fun t=>v.raw j f t h k) i selected

/-- The selected head is the actual digit at the source expression on the input memory. -/
theorem raw_source_digit (src : Sources g) {w floor : ℕ} (m : Memory w)
    (stored : Recorded g src v floor m) (lanes : 0<g.lanes) (bits : g.digitBits*g.lanes≤w)
    (i : Fin (g.paths*(g.blocks*(g.cap*11)))) (chosen : (rawKey g v j h k).val=i.val+1) (f : Fin 8) :
    Ticket.socketDigit g.digitBits g.lanes (src.raw j f i) m h k=(rawV g v j f h k).val :=
  (Ticket.socket_digit (src.raw j f i) m (v.raw j f i) (stored.raw j f i).read lanes bits h k).trans
    (congrArg Fin.val (rawV_at g v j h k i chosen f)).symm

/-- A kind-one cable ticket leaves the private rank selector at its blank value. -/
theorem rankV_at_cable (kind : (v.prior j 0 h k).val=1) : rankV g v j 0 h k=0 := by
  simp [rankV,picked,localLaw,rankInputs,kind,DescentResetStemMux.pick]

/-- The five selected matcher columns and eight selected raw columns supply all visible
ticket fields. This equality refers to the two original tables at their actual indices. -/
theorem ticketAt_read_rows
    (a : Fin (g.paths*(g.blocks*(g.cap*3)))) (anchorHit : (anchorChoice g v j h k).val=a.val+1)
    (i : Fin (g.paths*(g.blocks*(g.cap*11)))) (rawHit : (rawKey g v j h k).val=i.val+1) :
    ticketAt g v j h k=Ticket.fields g.blocks (v.origin j 0 h k).val (v.prior j 0 h k).val
      (rankV g v j 0 h k).val (v.origin j 2 h k).val (rawKey g v j h k).val
      (v.raw j 6 i h k).val (v.raw j 7 i h k).val (v.mouth j 1 h k).val
      (fun f=>(v.anchor j f a h k).val) (fun f=>(v.raw j (f.castLE (by decide : 6≤8)) i h k).val) := by
  unfold ticketAt
  simp only [anchorV_at g v j h k a anchorHit,rawV_at g v j h k i rawHit,rawKey]

end
end Hierarchy.DescentDatedOperandReadPipeline

end OAI
