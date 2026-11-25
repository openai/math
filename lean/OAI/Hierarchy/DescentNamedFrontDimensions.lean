import OAI.Hierarchy.DescentNamedFrontWords
import OAI.Hierarchy.DescentDatedScheduleSpace

namespace OAI
/-! # Public scalar counts of the original reset peer, ticket, and stem directories -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentCompiler DescentCompiler.TerminalScale DescentSixParty Filter
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)
variable (D f g C packet : ℕ) {ι : ℕ→Type*} (J : ℕ→ℕ) (z : ∀h,ι h→Sample)
set_option quotPrecheck false in
local notation "v" => fun h i=>(z h i).output G board D f g C packet
local notation "Ht" => GroupStage.depthBound D n f g

theorem front_counts (r : CalendarInputs G board D f g C packet J z)
    (height : ∀ᶠ h:ℕ in atTop,J h≤h)
    (oldH : Bounded (fun h i=>let a:=z h i;a.sched.hostSize a.age))
    (newH : Bounded (fun h i=>let a:=z h i;a.sched.hostSize (a.age+1)))
    (oldG : Bounded (fun h i=>let a:=z h i;2^a.sched.groupWidth a.k a.tail a.age))
    (newG : Bounded (fun h i=>let a:=z h i;a.sched.groupCount (a.age+1)))
    (M : Bounded (fun h i=>(z h i).lanes)) :
    PeerDimensions v ∧ Bounded (fun h i=>(v h i).privateShape.keys) :=by
  let const (a:ℕ):=Bounded.const (ι:=ι) a
  have L:=r.sheets.block.bounded height
  have prev:=r.previousCap.bounded height
  have old:=r.sheets.old
  have hits:=r.sheets.contact.bounded height
  have wire:=r.sheets.private_.bounded height
  have signed:= (const 2).mul (L.mul ((const 2).mul prev))
  have live:=signed.add ((const 1).add ((hits.mul signed).add wire))
  have k : Bounded (fun h i=>(z h i).k):=L.of_le fun h i=>Nat.lt_two_pow_self.le
  have tickets:=(const 2).mul (((k.add (const 1)).mul L).mul (const (2^n+1)))
  refine ⟨⟨oldH,r.sheets.shapes.bounded height,const D,live,newG,M,oldG,signed,
    const (DescentResetCableSlots.cableCap board Ht),tickets,newH,signed.mul (const (D+2)),L,signed⟩,wire⟩

end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
