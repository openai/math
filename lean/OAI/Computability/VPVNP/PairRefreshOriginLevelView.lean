import OAI.Computability.VPVNP.PairRefreshSelectedPackets
import OAI.Computability.VPVNP.PairRefreshTraversalOriginBits

/-! # Reindexing a selected refresh kernel at its physical port

The selected level keeps the output site of its term. The native reader
undoes the promotion of that site. Both views have the same placed half,
the same local occurrence, and the same singleton child packet.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RefreshHook.SelectedRows

open BurstRAM Compression Compression.DegreeRefresh Compression.Refresh CompressorRecords
open CompressorRecords.PortRefresh NodeArguments NodeArguments.ChildScan LocalHistory
open TreeDecode NetworkKernel
open TraversalRows TraversalRoles
set_option quotPrecheck false

variable {k K : Type} [_root_.Field k] [CommRing K] {S : BlockSchedule k} {B : S.Templates}
  {f : B.Entry → K} {hf : B.IsSolution f}
  (v : SelectedLevel B f hf) (u : (v.pass.step.term v.term).output.Site)
  (h : tagLevel B f hf v = .refresh)

local notation "t₀" => StatePass.step v.pass |>.term v.term
local notation "o₀" => occurrence v u h
local notation "x₀" => Occurrence.state (o₀)
local notation "port₀" => Occurrence.port (o₀)
local notation "u₀" => promotedSites (port₀)
local notation "r₀" => originReader B f hf v.origin v.term
local notation "r₁" => originReader B f hf (PassOrigin.refresh (x₀)) (Occurrence.choice (o₀))
local notation "source₀" => Placed (Term.place (t₀)) v.input.network.Half u
local notation "source₁" =>
  Placed (TraversalPlan.place (x₀)) (Network.Half (State.network (x₀))) (u₀)

/-- Placed arguments of the selected term and of its native port. -/
noncomputable def placedEquiv : source₀ ≃ source₁ := by
  rcases v with ⟨a, g, a', g', X, p, origin, term, tape⟩
  cases origin with
  | shrink => cases h
  | refresh X =>
    rcases u with ⟨⟨base, port⟩, lane⟩
    exact Equiv.refl _

variable (z : (v.pass.step.term v.term).output.Half u)
local notation "new₀" => halfEquiv v u h z

/-- This equivalence includes the actual local occurrence, also at a zero
coefficient in the specialization. -/
noncomputable def choiceEquiv :
    ((a : source₀) × ((r₀).witness u a z).Choice) ≃
    ((a : source₁) × ((r₁).witness (u₀) a (new₀)).Choice) := by
  rcases v with ⟨a, g, a', g', X, p, origin, term, tape⟩
  cases origin with
  | shrink => cases h
  | refresh X =>
    rcases u with ⟨⟨base, port⟩, lane⟩
    exact Equiv.refl _

variable (a : Placed (v.pass.step.term v.term).place v.input.network.Half u)
  (c : ((originReader B f hf v.origin v.term).witness u a z).Choice)
local notation "native₀" => choiceEquiv v u h z ⟨a, c⟩

theorem choice_fields :
    (native₀).1 = placedEquiv v u h a ∧
      (r₀).nodeBits u a z c = (r₁).nodeBits (u₀) (native₀).1 (new₀) (native₀).2 ∧
      ((r₀).witness u a z).exponents c =
        ((r₁).witness (u₀) (native₀).1 (new₀)).exponents (native₀).2 := by
  rcases v with ⟨a, g, a', g', X, p, origin, term, tape⟩
  cases origin with
  | shrink => cases h
  | refresh X =>
    rcases u with ⟨⟨base, port⟩, lane⟩
    exact ⟨rfl, rfl, rfl⟩

/-- The site's placed fiber contains the one old site at its true
address in the previous physical layer. -/
theorem children_eq (base : ℕ) :
    children (r₀) (fun t y => ⟨(sitePointers B.recordLimit base (siteOrder v.input) t).1,
      packed v.input t y⟩) u a =
    [RefreshHook.packet (x₀) (RefreshMapOperands.oldSite (x₀) (port₀))
      (childNode (x₀) base B.recordLimit (RefreshMapOperands.oldSite (x₀) (port₀)))
      ((placedEquiv v u h a) _ (TraversalPlan.old_place (x₀) (port₀)))] := by
  rcases v with ⟨a, g, a', g', X, p, origin, term, tape⟩
  cases origin with
  | shrink => cases h
  | refresh X =>
    rcases u with ⟨⟨b, port⟩, lane⟩
    let v' := ((b, lane), port)
    let r := originReader B f hf (PassOrigin.refresh X) term
    let addr := fun t => (sitePointers B.recordLimit base (siteOrder X) t).1
    exact (TermParsers.childPackets_state X r rfl (fun _ => rfl) (fun _ => rfl) addr
      (promotedSites v') a).symm.trans (TraversalPlan.origin_childPackets B f hf X term v' a addr)

end PairSimulation.RefreshHook.SelectedRows

end VPVNP
end Computability
end OAI
