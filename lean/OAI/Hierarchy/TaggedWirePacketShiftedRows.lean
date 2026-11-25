import OAI.Hierarchy.TaggedWirePacketPortBits
import OAI.Hierarchy.TaggedWirePacketTurnRows

namespace OAI
/-! # The same two-barrel router reading shifted lanes of a gathered physical chord -/
noncomputable section
namespace Hierarchy.WireTelescope.PacketTurns
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph AdaptiveProbe
open TurnShelf
open scoped Classical

variable {S n m t count : ℕ} (old : Fin n→Chord S) (edge : Fin m→Chord S)
  (route : Fin n→List (Fin m)) (bits : Fin n→ℕ) (rank : Fin t≃Σi,Fin (route i).length)
local notation "mass" => routeLoad route bits
local notation "alloc" => NativeSlot.allocation route bits rank

def shiftedStart (base : Fin m→ℕ) (i : Fin n) : TurnRef→ℕ
  | .inl _=>0
  | .inr (j,_)=>if h:j<(route i).length then base ((route i).get ⟨j,h⟩)+NativeSlot.start route bits rank i ⟨j,h⟩ else 0

theorem shifted_read (base : Fin m→ℕ) (i : Fin n) (j : Fin (bits i)) (s : Fin S) (ref : TurnRef)
    (valid : ValidRef old edge route i s ref) (x : BitState (bitGraph (rowGraph old) bits) s)
    (y : BitState (bitGraph (rowGraph edge) mass) s) (before : Fin n→Bool→ℕ) (after : Fin m→Bool→ℕ)
    (plane : ℕ→ℕ→Bool)
    (prior : ∀b (h:(rowGraph old).vertex i b=s),plane (before i b) j.val=x (priorPort old bits i j b h))
    (paid : ∀q : Fin (route i).length,∀b (h:(rowGraph edge).vertex ((route i).get q) b=s),
      plane (after ((route i).get q) b) (base ((route i).get q)+NativeSlot.start route bits rank i q+j.val)=
        y (paidPort edge route bits rank i j q b h)) :
    plane (refRole route before after i ref) (shiftedStart route bits rank base i ref+j.val)=
      readTurn (rowGraph edge) (rowGraph old) route bits alloc ⟨i,j⟩ s (x,y) ref := by
  rcases ref with b|⟨u,b⟩
  · rw [turn_start_bit old edge route bits rank i j b s valid,refRole,shiftedStart,Nat.zero_add]
    exact prior b valid
  · obtain ⟨ht,here⟩:=valid
    let q : Fin (route i).length:=⟨u,ht⟩
    let key := alloc ⟨⟨i,j⟩,q⟩
    have hit : key.1=(route i).get q := NativeSlot.allocation_edge route bits rank _
    have room : u<(placedRoute route bits alloc ⟨i,j⟩).length := by simpa [placedRoute] using ht
    have actual : (placedRoute route bits alloc ⟨i,j⟩).get ⟨u,room⟩=key := by simp [placedRoute,key,q]
    have endAt : (bitGraph (rowGraph edge) mass).vertex key b=s := by
      cases b <;> simpa [bitGraph,PortGraph.vertex,hit,q] using here
    simp only [readTurn,dite_eq_left room,actual,dite_eq_left endAt,refRole,shiftedStart,dite_eq_left ht]
    refine (paid q b here).trans (congrArg y ?_)
    first | rfl | exact Subtype.ext (Prod.ext actual.symm rfl)

variable (base : Fin m→ℕ) (before : Fin n→Bool→ℕ) (after : Fin m→Bool→ℕ)
    (short : ∀i,(route i).length≤2) (order : Fin count≃Positions route)

def shiftedFields (r : Fin count) : Fin 7→ℕ :=
  let z:=order r
  let role := fun b=>refRole route before after z.1 (side old edge route z b)
  let off := fun b=>shiftedStart route bits rank base z.1 (side old edge route z b)
  ![role false,role true,off false,off true,bits z.1,(vertex old edge route z).val,
    (StripPaths.positionSeat route short z).val]

variable (sp : ∀i,Spine (rowGraph edge) (old i).1.1 (route i) (old i).1.2)

theorem shifted_role_read (r : Fin count) (b : Bool) :
    shiftedFields old edge route bits rank base before after short order r (if b then 1 else 0)=
      refRole route before after (order r).1 (refAt old edge route sp (order r) b) := by
  cases b <;> exact congrArg (refRole route before after (order r).1) (side_ref old edge route short sp (order r) _)

theorem shifted_start_read (r : Fin count) (b : Bool) :
    shiftedFields old edge route bits rank base before after short order r (if b then 3 else 2)=
      shiftedStart route bits rank base (order r).1 (refAt old edge route sp (order r) b) := by
  cases b <;> exact congrArg (shiftedStart route bits rank base (order r).1) (side_ref old edge route short sp _ _)

end Hierarchy.WireTelescope.PacketTurns

end
end OAI
