import OAI.Hierarchy.DescentOrdinaryPinMap
import OAI.Hierarchy.DescentScheduledBitHistory
import OAI.Hierarchy.DescentGroupStageNames

namespace OAI
/-! # The exact surviving grouped pins of the chosen ordinary branch -/
namespace Hierarchy.DescentSixParty.GroupStage
open DescentColonies DescentGL DescentHostDegree DescentHostDirectory DescentKernelHistory
open scoped Classical
noncomputable section
variable {F P J J₁ V V₁ : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype J₁] [DecidableEq J₁]
  [Fintype V] [DecidableEq V] [Fintype V₁] [DecidableEq V₁]
  {d k n : ℕ} {bits : P→ℕ} {G : PoweredGadget F} {W Y : MarkedWorld F d P bits} {price ε : ℝ}
  (A : GroupStage W G price ε J V k) (he : 0≤ε) (digits : J≃J₁×Block n)
  (fresh : GroupStage Y G price ε J₁ V₁ n) (chart : V₁↪Key V)

/-- Both group fields come from the actual next radix digit. The new hub
records the previous host and the high part of the chosen linear image. -/
def HubRows : Prop := ∀pin, A.hub (A.pos (W.graph.attach pin)).2=true →
  let u:=W.graph.attach pin
  let v:=Y.graph.attach pin
  let gain:=gainExponent 20 A.degree
  let image:=rearrange (multiplier A.fieldBits (BitDescription.scannedRows he A.stage).μ) (A.block u)
  ((fresh.pos v).1,fresh.block v)=digits (A.pos u).1 ∧
    chart (fresh.pos v).2=((A.pos u).2,(k-gain,group (k-gain) image),0)

theorem HubRows.rename (receipt : HubRows A he digits fresh chart)
    (s : Equiv.Perm Y.graph.Site) (e : Equiv.Perm Y.graph.Edge) :
    HubRows A he digits (fresh.names s e) chart := by
  intro pin flag
  change ((fresh.pos (s.symm (s (Y.graph.attach pin)))).1,
      fresh.block (s.symm (s (Y.graph.attach pin)))) = _ ∧
    chart (fresh.pos (s.symm (s (Y.graph.attach pin)))).2 = _
  rw [s.symm_apply_apply]
  exact receipt pin flag

theorem HubRows.cast_names (receipt : HubRows A he digits fresh chart)
    (s : Equiv.Perm Y.graph.Site) (e : Equiv.Perm Y.graph.Edge)
    {Y' : MarkedWorld F d P bits} (eqn : Y'=PhysicalRename.world Y s e) :
    HubRows A he digits (eqn.symm ▸ fresh.names s e) chart := by
  subst Y'
  exact HubRows.rename A he digits fresh chart receipt s e

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
