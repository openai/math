import OAI.Hierarchy.DescentPackedCanvasValues
import OAI.Hierarchy.DescentPaddedProfile
import OAI.Hierarchy.DescentIssuedResidentReset

namespace OAI
/-! # Padded measured graph and the actual sorted physical port tape -/
namespace Hierarchy.DescentSixParty.PackedFlow.Canvas
open DescentGL DescentColonies DescentSIMDLookup DescentPackedExchange DescentMeasuredWeights DescentMeasuredHeader
open DescentBaseProfile DescentPackedWalsh DescentWalshPhysical DescentPackedRectangle.Canvas
open DescentPackedSingletonDepth.Canvas
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {d k H HP D u l : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {q ε : ℝ}
  (A : GroupStage W G q ε J V k) (name : V≃Fin H) (digits : Block (u+l)≃J×Block k)
  (hosts : H≤HP)
local notation "m" => u+l
local notation "header" => A.mixerHeader digits name
local notation "nxt" => extendedPort (D:=D) hosts (neighborSlot (degree:=A.degree) name A.mutual)
local notation "real" => GroupStage.MixerHeader.neighbors (A.mixerHeader digits name)
local notation "ns" => peers hosts real

theorem roster_eq (v:Fin HP) (j:Fin D) : Padded.roster A name hosts v j=nxt (v,j) := by
  by_cases site:v.val<H <;> by_cases port:j.val<A.degree <;>
    simp [Padded.roster,DescentPackedFlowPair.Padded.next,DescentPackedFlowPair.Padded.project,
      extendedPort,site,port,next_numbered]

theorem roster_row (v:Fin HP) (j:Fin D) : nxt (v,j)=(ns[v.val])[j.val]? := by
  by_cases site:v.val<H
  · let x:Fin H:=⟨_,site⟩
    have same:x.castLE hosts=v:=Fin.ext rfl
    rw [←same]
    erw [peers_real hosts real x,List.getElem?_map]
    by_cases port:j.val<A.degree
    · let slot:Fin A.degree:=⟨_,port⟩
      simp [extendedPort,x.isLt,port,A.slot_matches digits name (x,slot),slot]
      rfl
    · have limit:(real[x.val]).length≤j.val:=((header).degree x).trans (by omega)
      simp [extendedPort,port]
      exact limit
  · simp [extendedPort,peers,extend,site]

theorem old_weight (v:Fin HP) (t:Block m) : ((DescentPackedSingletonDepth.Canvas.weights hosts (header).loads)[v.val])[t.val]=
    Padded.load A name digits v t := by
  by_cases hv:v.val<H <;> simp [DescentPackedSingletonDepth.Canvas.weights,extend,Padded.load,DescentPackedFlowPair.Padded.project,hv,GroupStage.mixerHeader]

theorem original_depth (f : ℕ) (v:Fin H) :
    measuredDepth ns (DescentPackedSingletonDepth.Canvas.weights hosts (header).loads) A.degree k f (A.wire*(A.z*G.b)*A.cap) (v.castLE hosts)=
      (header).depth A f (name.symm v) := by
  erw [depth_real hosts real (header).loads A.degree k f (A.wire*(A.z*G.b)*A.cap) v]
  simp only [GroupStage.MixerHeader.depth,GroupStage.mixerHeader]
  erw [name.apply_symm_apply]

end
end Hierarchy.DescentSixParty.PackedFlow.Canvas

end OAI
