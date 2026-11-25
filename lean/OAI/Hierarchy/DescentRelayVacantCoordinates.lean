import OAI.Hierarchy.DescentOriginalRelayPadding

namespace OAI
/-! # Physical coordinates of the occupied destination of an arbitrary original trunk -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentCompiler ClosedReset.Window DescentPaidResidentCount DescentSharedCableNames
open DescentKernelHistory DescentBundleHistory
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
    {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (B : ClosedReset input ctl)
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "coarse" => (Z).orderedReentry T (DescentOrderedReset.grains W B.count B.order)
local notation:max "realRelay" t:arg => B.reblock.destination (((Z).resetNames T).symm (.inl (true,t)))
local notation:max "target" t:arg => (blocks B).dst (trunkParent B t)

theorem relay_vacant_coordinates (ports : DatePorts)
    (groupsAt : ports.venue.groups=S.groupCount (i+1)) (radixAt : ports.venue.k=k)
    (x : Fin (2^ports.venue.k)) (rh : Fin ports.operandHosts) (rg : Fin ports.venue.groups)
    (inside : rh.val<Fintype.card B.next.V) (t : (Z).Fallback)
    (here : occupies B.next.placement (Equiv.refl _) B.next.vertex ⟨rh.val,inside⟩
      (rg.cast groupsAt) (x.cast (congrArg (2^·) radixAt)) (realRelay t)) :
    ((denseOrder B) (target t).1.2).val=rh.val ∧ (target t).1.1.val=rg.val ∧ (target t).2.val=x.val :=by
  have atDst : (coarse).graph.dst (trunkParent B t)=((Z).resetNames T).symm (.inl (true,t)):=by
    apply ((Z).resetNames T).injective
    rw [Equiv.apply_symm_apply]
    exact (trunk_nodes B t).2
  have physical : target t=Stage.home B.next.placement (realRelay t):=by
    change Stage.home B.next.placement (B.reblock.destination ((coarse).graph.dst (trunkParent B t)))=_
    rw [atDst]
  rw [physical]
  exact ⟨congrArg Fin.val here.1,congrArg Fin.val here.2.1,congrArg Fin.val here.2.2⟩

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
