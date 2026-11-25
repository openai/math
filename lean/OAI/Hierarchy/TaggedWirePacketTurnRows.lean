import OAI.Hierarchy.TaggedWireShortWalkWords
import OAI.Hierarchy.TaggedWireStripSeats
import OAI.Hierarchy.TaggedWireTurnData
import OAI.Hierarchy.TaggedWireChronologicalMatrix
import OAI.Hierarchy.ProtocolRAMTurnShelf

namespace OAI
/-! # Native item, role, prefix and boundary fields of each short packet installation -/

noncomputable section
namespace Hierarchy.WireTelescope.PacketTurns
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph AdaptiveProbe
open TurnShelf
open scoped Classical

variable {S n m t count : ℕ} (old : Fin n→Chord S) (edge : Fin m→Chord S)
  (route : Fin n→List (Fin m)) (bits : Fin n→ℕ) (rank : Fin t≃Σi,Fin (route i).length)
  (before : Fin n→Bool→ℕ) (after : Fin m→Bool→ℕ) (short : ∀i,(route i).length≤2)
  (order : Fin count≃Positions route)

def vertex (q : Positions route) := ShortWalk.site (rowGraph edge) (old q.1).1.1 (old q.1).1.2 (route q.1) q.2.val

def side (q : Positions route) (right : Bool) : TurnRef :=
  let v := vertex old edge route q
  if right then ShortWalk.right (rowGraph edge) v (route q.1) q.2.val
  else ShortWalk.left (rowGraph edge) v (route q.1) q.2.val

/-- The two cuts of a single-hop selector/ordinary/inventory route use one
actual row ID. A catalyst can additionally use its actual mate at the
middle boundary. Prefixes include every earlier occurrence of that ID. -/
def fields (i : Fin count) : Fin 7→ℕ :=
  let q := order i
  let role := fun b=>refRole route before after q.1 (side old edge route q b)
  let off := fun b=>refStart route bits rank q.1 (side old edge route q b)
  ![role false,role true,off false,off true,bits q.1,(vertex old edge route q).val,
    (StripPaths.positionSeat route short q).val]

local notation "col" => fields old edge route bits rank before after short order

def put : ProtocolRAMTurnShelf.Live col ↪ Fin S×Fin (n*3) where
  toFun u := (vertex old edge route (order u.val),StripPaths.positionSeat route short (order u.val))
  inj' _ _ eq := Subtype.ext (order.injective ((StripPaths.positionSeat route short).injective (congrArg Prod.snd eq)))

variable (sp : ∀i,Spine (rowGraph edge) (old i).1.1 (route i) (old i).1.2)

include short in
theorem visit (q : Positions route) : vertex old edge route q=(sp q.1).visit q.2 :=
  ShortWalk.site_eq _ (sp q.1) (short q.1) q.2

include short in
theorem side_ref (q : Positions route) (b : Bool) :
    side old edge route q b=refAt old edge route sp q b := by
  have loc := visit old edge route short sp q
  have pair := ShortWalk.sides_eq (rowGraph edge) (sp q.1) (fun j=>(edge j).property.ne) q.2
  cases b
  · exact (congrArg (fun v=>ShortWalk.left (rowGraph edge) v (route q.1) q.2.val) loc).trans (congrArg Prod.fst pair)
  · exact (congrArg (fun v=>ShortWalk.right (rowGraph edge) v (route q.1) q.2.val) loc).trans (congrArg Prod.snd pair)

theorem role_read (i : Fin count) (b : Bool) :
    col i (if b then 1 else 0)=refRole route before after (order i).1 (refAt old edge route sp (order i) b) := by
  cases b <;> exact congrArg (refRole route before after (order i).1) (side_ref old edge route short sp (order i) _)

theorem start_read (i : Fin count) (b : Bool) :
    col i (if b then 3 else 2)=refStart route bits rank (order i).1 (refAt old edge route sp (order i) b) := by
  cases b <;> exact congrArg (refStart route bits rank (order i).1) (side_ref old edge route short sp (order i) _)

theorem width_read (i : Fin count) : col i 4=bits (order i).1 := rfl

theorem field_site (u : ProtocolRAMTurnShelf.Live col) :
    (put old edge route bits rank before after short order u).1=(sp (order u.val).1).visit (order u.val).2 :=
  visit old edge route short sp _

end Hierarchy.WireTelescope.PacketTurns

end
end OAI
