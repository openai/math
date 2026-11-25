import OAI.Hierarchy.TaggedWirePacketPriorPort
import OAI.Hierarchy.TaggedWireTurnData

namespace OAI
/-! # The two local packet port bits for arbitrary intermediate and outgoing states -/

noncomputable section
namespace Hierarchy.WireTelescope.PacketTurns
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph AdaptiveProbe
open scoped Classical

variable {S n m t : ℕ} (old : Fin n→Chord S) (edge : Fin m→Chord S)
  (route : Fin n→List (Fin m)) (bits : Fin n→ℕ) (rank : Fin t≃Σi,Fin (route i).length)
local notation "mass" => routeLoad route bits
local notation "alloc" => NativeSlot.allocation route bits rank

def paidPort (i : Fin n) (j : Fin (bits i)) (q : Fin (route i).length) (b : Bool) {s : Fin S}
    (atSite : (rowGraph edge).vertex ((route i).get q) b=s) : (bitGraph (rowGraph edge) mass).Port s := by
  let key := alloc ⟨⟨i,j⟩,q⟩
  have same : key.1=(route i).get q := NativeSlot.allocation_edge route bits rank _
  exact ⟨(key,b),by cases b <;> simpa only [bitGraph,PortGraph.vertex,same] using atSite⟩

theorem local_read (i : Fin n) (j : Fin (bits i)) (s : Fin S) (ref : TurnRef)
    (valid : ValidRef old edge route i s ref) (x : BitState (bitGraph (rowGraph old) bits) s)
    (y : BitState (bitGraph (rowGraph edge) mass) s) (before : Fin n→Bool→ℕ) (after : Fin m→Bool→ℕ)
    (plane : ℕ→ℕ→Bool)
    (prior : ∀b (h:(rowGraph old).vertex i b=s),plane (before i b) j.val=x (priorPort old bits i j b h))
    (paid : ∀q : Fin (route i).length,∀b (h:(rowGraph edge).vertex ((route i).get q) b=s),
      plane (after ((route i).get q) b) (NativeSlot.start route bits rank i q+j.val)=
        y (paidPort edge route bits rank i j q b h)) :
    plane (refRole route before after i ref) (refStart route bits rank i ref+j.val)=
      readTurn (rowGraph edge) (rowGraph old) route bits alloc ⟨i,j⟩ s (x,y) ref := by
  rcases ref with b|⟨u,b⟩
  · rw [turn_start_bit old edge route bits rank i j b s valid,refRole,refStart,Nat.zero_add]
    exact prior b valid
  · obtain ⟨ht,here⟩:=valid
    let q : Fin (route i).length:=⟨u,ht⟩
    let key := alloc ⟨⟨i,j⟩,q⟩
    have hit : key.1=(route i).get q := NativeSlot.allocation_edge route bits rank _
    have room : u<(placedRoute route bits alloc ⟨i,j⟩).length := by simpa [placedRoute] using ht
    have actual : (placedRoute route bits alloc ⟨i,j⟩).get ⟨u,room⟩=key := by simp [placedRoute,key,q]
    have endAt : (bitGraph (rowGraph edge) mass).vertex key b=s := by
      cases b <;> simpa [bitGraph,PortGraph.vertex,hit,q] using here
    simp only [readTurn,dite_eq_left room,actual,dite_eq_left endAt,refRole,refStart,dite_eq_left ht]
    refine (paid q b here).trans (congrArg y ?_)
    first | rfl | exact Subtype.ext (Prod.ext actual.symm rfl)

end Hierarchy.WireTelescope.PacketTurns

end
end OAI
