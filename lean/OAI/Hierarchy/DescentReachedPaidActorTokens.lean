import OAI.Hierarchy.DescentMaterialActorPadding

namespace OAI
/-! # The actual matched donor panel names the original actors and suppresses padded hosts -/
namespace Hierarchy.DescentScalarVenueMask.Stage
open DescentSIMDLookup DescentPacking.PackedMatch.Local DescentPacking.PackedMatch.Local.Stage DescentSixParty DescentStageEdgeReceipt
open DescentGroupPeerOrder DescentSharedCableNames DescentPackedColony DescentHaloWalkRAM DescentRawCablePanel
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
    {d k i short a H K Z M w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule)
    (ready : A.StateBounds S i) (group : J≃Fin Z) (hosts : V↪Fin H) (wide : H≤K) (win : J×V→Fin (2^k)→Cell a)
    (hm : 0<M) (profile dest : ℕ) (m : Memory w) (hub : V→Bool) (lay : Bool) (bytes slots : ℕ)
local notation "grp" => group.toEmbedding
local notation "rank" => groupRank (group.toEmbedding.trans Fin.valEmbedding) (hosts.trans Fin.valEmbedding)
local notation "up" => Fin.castLEEmb wide
local notation "large" => hosts.trans up
local notation "near" => hostRotor large (hostRoster A (Function.Embedding.trans large Fin.valEmbedding))
local notation "fmt" => shapeOf (short:=short) A bytes
local notation "state" => nativeParts (short:=short) A native S ready rank win group large hm profile dest m near hub lay bytes
local notation "t" => tokens (short:=short) A native S ready rank win profile lay grp hosts
local notation "printed" => fun x j (h : Fin K) g=>
  DepotRAM.ActorInputs.token fmt profile slots (2^(k+1)*slots) (state h g)
    (Prepare.actors A grp large h g) (x,j)

/-- The incoming donor panel can have a different lane pitch from the later clipped
    field bank.  These statements identify the lane contents before repacking. -/
theorem received_tokens :
    (∀x j h g,printed x j (up h) g=t slots x j h g) ∧
    (∀x j (h : Fin K) g,H≤h.val→printed x j h g=none) ∧
    ∀h,Census.hub A large (up h)=Census.hub A hosts h :=by
  have rankEq : (Function.Embedding.trans large Fin.valEmbedding)=hosts.trans Fin.valEmbedding :=by
    ext v
    rfl
  have read (x : Fin (2^k)) (j : Fin (1+A.cap*6)) (h : Fin K) (g : Fin Z) :
      printed x j h g=tokens (short:=short) A native S ready rank win profile lay grp large slots x j h g :=by
    have issued:=retained_actor (short:=short) A native S ready group large win hm profile dest
      m hub lay bytes slots x j h g
    simpa only [rankEq] using issued
  refine ⟨?_,?_,fun h=>hub_padded hosts up A h⟩
  · intro x j h g
    exact (read x j _ g).trans
      (tokens_padded (short:=short) grp hosts up A native S ready rank win profile lay slots x j h g)
  · intro x j h g absent
    apply (read x j h g).trans
    apply tokens_absent (short:=short) grp hosts up A native S ready rank win profile lay slots x j h g
    intro v impossible
    have equal:=congrArg Fin.val impossible
    change v.val=h.val at equal
    have bound:=v.isLt
    omega

end
end Hierarchy.DescentScalarVenueMask.Stage

end OAI
