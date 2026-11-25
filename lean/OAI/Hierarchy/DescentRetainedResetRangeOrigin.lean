import OAI.Hierarchy.DescentArchiveSliceLayout
import OAI.Hierarchy.DescentRetainedRangeDigits

namespace OAI
/-! # Range words at the actual old, relay and fresh origins of an installed reset -/
namespace Hierarchy.DescentRetainedRangeDigits
open DescentBundleHistory DescentKernelHistory DescentSixParty DescentSixParty.Chronology DescentCompiler
open DescentPrimitivePalette DescentTerminalSliceRuns DescentTerminalCombinedRole DescentOrderedReset
open DescentResetAttachments DescentRouterBank DescentNamedContact DescentResetTrunks DescentRotor
open DescentEpochTagKeys Computability.BorderVNP.Crossing
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d p R : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
variable {B : BitDescription W}
section Install
variable {H Q Y : Type} [Fintype H] [Fintype Q] {L d' : ℕ} (sh : WorldShape p R B) (hp : 0<p) (one : 1≤R)
    (home : W.graph.Site→H) (grp : Bool→W.graph.Edge→Q) (hub : H→Bool)
    {w : W.graph.Edge→ℕ} (same : w=W.graph.width) (board : Network d' (Bool×Q) (publicWidth grp w))
    (legacy sorted : board.Tables F) (ids : W.graph.Edge↪Fin L)
    (scalar : Y→List (List Bool)→F) (prog : SiteBits (U:=Y) board) (valid : ReadsBits board scalar prog sorted)
    (device : ∀v,Shape p (prog v)) (bound : ∀v u j g,((device v).chunk u j g).stride≤R)
    (widths : ∀e,p∣board.width e)
local notation "names_" => NodeOrder.installedNames B home grp hub same board legacy sorted ids scalar prog valid
local notation "installed_" => installedWorldShape sh hp one home grp hub same board legacy sorted ids scalar prog valid device bound widths
omit [Fintype Q] in
theorem installed_range_origin (x : NodeOrder.All (B.installed home grp hub same board legacy sorted ids scalar prog valid)) :
    (installed_).nodeFields x=Sum.elim sh.nodeFields
      (Sum.elim (fun e=>relayFields p (W.graph.width e)) (fun v : NodeOrder.Global prog=>(device v.1).sliceFields v.2))
      (names_ x) := by
  subst w
  rcases x with ⟨(⟨b,h⟩|v),u⟩
  · cases b
    · rcases u with ⟨⟨v,rfl⟩,u⟩
      exact retained_fields W.graph home grp board ids sh.edges hp B.recipe prog sh.sites device v u
    · exact relay_fields W.graph home grp board ids sh.edges hp B.recipe prog sh.sites device h u
  · exact device_fields W.graph home grp board ids sh.edges hp B.recipe prog sh.sites device v u
end Install
variable {q ε : ℝ} {S : AtomSchedule} {k i z D wire hist n h C f g cut tail : ℕ} {G : PoweredGadget F}
    {cap : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
variable (b : ClosedReset cap ctl) (hp : 0<p) (whole : p∣b.reset.unit) (a : Archive W)
local notation "key" => DescentOrderedReset.grains W b.count b.order
local notation "fit" => (Nat.div_mul_cancel whole).symm
local notation "plan" => b.reset.laneProgram key (b.reset.unit/p) p hp fit
local notation "prog" => b.reset.laneRecipe key (b.reset.unit/p) p hp fit
local notation "device" => fun v=>ofProgram (fun e=>boundaryWidth b.reset.bank v e/p)
  (b.reset.laneWidth_eq (b.reset.unit/p) p fit v) hp (plan v)
local notation "origin" => resetOrigin b hp whole a

theorem reset_range_origin (sh : WorldShape p R a.bit) (one : 1≤R) (pos : 0<b.reset.unit)
    (wide : max 1 (max b.reset.width (C*b.reset.width))≤R)
    (x : NodeOrder.All (resetArchive b p hp whole a).bit) :
    let split:=sh.granular b.count (z*G.b) b.fit hp (b.unit ▸ pos) (b.unit ▸ whole)
    let post:=WorldShape.follow hp pos whole b.reblock b.cuts
      (reentryWorldShape split b.reset b.terminals key (b.reset.unit/p) hp fit (resetMenu b) one wide)
    post.nodeFields x=Sum.elim sh.nodeFields
      (Sum.elim (fun e=>relayFields p ((W.granular b.count (z*G.b) b.fit).graph.width e))
        (fun v : NodeOrder.Global prog=>(device v.1).sliceFields v.2)) (origin x) := by
  intro split post
  refine (WorldShape.follow_fields hp pos whole b.reblock b.cuts
    (reentryWorldShape split b.reset b.terminals key (b.reset.unit/p) hp fit (resetMenu b) one wide) x).trans ?_
  unfold reentryWorldShape
  exact installed_range_origin split hp one b.terminals.home b.reset.placement.input b.terminals.hub
    (funext fun e=>(b.reset.allWidths e).symm) b.reset.bank b.reset.tables (b.reset.orderedBank key) key
    _ prog (b.reset.lane_valid key (b.reset.unit/p) p hp fit (resetMenu b)) device
    (fun v u j g=>(b.reset.lane_stride key (b.reset.unit/p) p hp fit v u j).trans wide)
    (fun e=>b.reset.lane_dvd (b.reset.unit/p) p fit (b.reset.bank.src e) (.inl ⟨e,Or.inl rfl⟩))
    (NodeOrder.followNames b.reblock _ x)

end
end Hierarchy.DescentRetainedRangeDigits

end OAI
