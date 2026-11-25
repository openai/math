import OAI.Computability.BorderVNP.DiagonalExternalFreeCell
import OAI.Computability.BorderVNP.CubeRouteNativePlacement

/-! # A real free lane reads its own emitting directory's receiver -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew

open Crossing Packing RoutingISA RoutingISA.Evaluator RoutingISA.Transmission BorderVNP.Cube VPVNP.BurstRAM

variable {D R r K link V g m n C w entries desc : ℕ} (N : Network D (FreeBlock R V) (fun _ => g))
    (cell : N.Site → Fin C) (edgeID : N.Edge ↪ Fin m) (portID : FreeBlock R V ↪ Fin n)
    (hg : 0<g) (room : r*(2*K+R*link)≤V*g) (pp lp : ℕ → ℕ × ℕ)
local notation3 (prettyPrint := false) "dir" => freeDirectory R r K link V g entries desc

private theorem free_source_row (z : FreePort R r K) :
    let a := freeLane hg room z
    ∃ i : Fin ((dir).directory pp lp).length, ((dir).directory pp lp)[i.val].cell=
      (lp (a.1.1.val*V+a.1.2.val)).1 := by
  have row (u : Fin (R+1)) (p : Fin r) (f : Fin 2) (j : Fin K) :
      let a := freeLane hg room (fromField u p f j)
      ∃ i : Fin ((dir).directory pp lp).length, ((dir).directory pp lp)[i.val].cell=
        (lp (a.1.1.val*V+a.1.2.val)).1 := by
    obtain ⟨r,mem,_,_,_,_,_,_,same,_⟩ := freeLane_delivered hg room entries desc pp lp u p f j
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp mem
    exact ⟨i,by simpa only [List.get_eq_getElem] using (congrArg Directory.Row.cell hi).trans same⟩
  rcases z with ⟨u,p,j|j⟩
  · exact row u p 0 j
  · exact row u p 1 j

/-- The physical descriptor writer's actual owner word agrees with its routing destination
at every live literal or private input lane, including cells that have just one such lane. -/
theorem free_owner_on_writer {ar : CubeArena.Layout} {pub : Arg → Word w} {mem : Memory w} {owner : ℕ → Fin (R+1)}
    (demand : DemandInput ar dir pp lp owner pub mem) (placement : LivePlacement N cell edgeID portID lp)
    (z : FreePort R r K) :
    let c := cell (N.attach (freeLane hg room z).1)
    readings mem ((DataWriter.layout (readings pub) (readings mem)).owners+2*c.val)=(owner c.val).val := by
  intro c
  obtain ⟨i,h⟩ := free_source_row hg room pp lp z (entries:=entries) (desc:=desc)
  have atCell : ((dir).directory pp lp)[i.val].cell=c.val :=
    h.trans (congrArg Prod.fst (placement (freeLane hg room z).1))
  simpa only [atCell,Nat.mul_comm 2] using (demand.cells i).1

end Diagonal.ExternalSew

end BorderVNP
end Computability
end OAI
