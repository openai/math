import OAI.Hierarchy.DescentMountedGoodNode
import OAI.Hierarchy.DescentLanePortKeys

namespace OAI
namespace Hierarchy.DescentChosenRouter
open Computability.BorderVNP.Crossing DescentKernelHistory DescentResetGates DescentRotor DescentMixedRouter
open DescentRouterSlots DescentBatchedBank DescentBundleHistory DescentBatchedNodeOrder
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1600000
open private transportCircuit from OAI.Hierarchy.DescentInstalledNames
variable {V I H A K : Type} [Fintype V] [DecidableEq V] [Fintype I] [Fintype H] [Fintype A] [Field K]
    {k n h C₀ bits u N : ℕ} (P : Placement V I H A k (2^n)) (G : NonlinearExpanders.Graph n h)
    (hw : 0<bits) (pay : ℝ) (hardware : Hardware (K:=K) (C₀:=C₀) (u:=u) P G hw pay)
    (key : I↪Fin N) (D m p : ℕ) (hp : 0<p) (fit : u=m*p)
local notation "sel" => selected P G hw pay hardware
local notation "bank" => DescentMixedRouter.network G hw u P.contact P.input P.site P.owner P.align sel D
local notation "prg" => sizedProgram G hw u m p hp fit P.contact P.input P.site P.owner P.align key D sel
variable (s : Bool) (g : P.Good)
local notation "r" => (⟨s,.inl g⟩ : Bool×P.Site)
local notation "sizedHardware" => (fit ▸ hardware : Hardware (K:=K) (C₀:=C₀) (u:=m*p) P G hw pay)
local notation "sizedChoice" => selected P G hw pay sizedHardware s (.inl g)
local notation "trueDevice" => DescentMixedRouter.device G hw (m*p) P.contact P.input P.site P.owner P.align
  (D:=D) sizedChoice
local notation "installedSite" => DescentCommonPalette.rotorSiteEquiv G D
  (selectedRotorLayers P G hw pay hardware s g) C₀ bits u
local notation "sizedSite" => DescentCommonPalette.rotorSiteEquiv G D
  (selectedRotorLayers P G hw pay sizedHardware s g) C₀ bits (m*p)
local notation "prog" v => (DescentBatchedBank.deviceProgram G hw m p hp P.contact P.input P.site P.owner
  P.align key D sizedChoice (sizedSite v))
local notation "widthAt" v => (boundaryWidth trueDevice (sizedSite v))
local notation "venue" v => (⟨r,installedSite v⟩ : (bank).Site)
variable (v : (DescentCommonPalette.rotor G).Site)
local notation "μ" => (fun i => (widthAt v) i / p)

open DescentLaneGates
-- These are the actual rack and its selected devices once the unit is substituted.
local notation "rack" => DescentRouterBank.network D P.contact P.input P.site P.owner (fun _ : I=>m*p)
local notation "fixedCell" c => (DescentCommonPalette.rotorSiteEquiv G D
  (selectedRotorLayers P G hw pay c s g) C₀ bits (m*p) v)
local notation "fixedPorts" c => (portMap rack (fun a : (rack).Site =>
  DescentMixedRouter.device G hw (m*p) P.contact P.input P.site P.owner P.align (D:=D)
    (selected P G hw pay c a.1 a.2)) r (fixedCell c))
local notation "fixedProgram" c => (DescentBatchedBank.deviceProgram G hw m p hp P.contact P.input P.site
  P.owner P.align key D (selected P G hw pay c s (.inl g)) (fixedCell c))

def mountedGoodPorts : PortMap (widthAt v) (boundaryWidth bank (venue v)) :=by
  revert hardware
  subst u
  intro mounted
  exact fixedPorts mounted

/-- Installing a chosen good circuit applies the original rack port map to a
local operand and keeps its p-word and gate ordinal. -/
theorem mountedGoodKey (target : ∀i,boundaryWidth bank (venue v) i=boundaryWidth bank (venue v) i/p*p)
    (source : ∀i,(widthAt v) i=μ i*p) (node : (prg (venue v)).Node) (slot : ℕ)
    (ref : BlockRef p (widthAt v)) (hit : ((ofProgram μ source hp (prog v)).keys
      (mountedGoodNode P G hw pay hardware key D m p hp fit s g v node))[slot]?=some (.inl ref)) :
    ((ofProgram (fun i=>boundaryWidth bank (venue v) i/p) target hp (prg (venue v))).keys node)[slot]?=
      some (.inl ((mountedGoodPorts P G hw pay hardware D m p fit s g v).wordBlock ref)) :=by
  revert hardware target source node slot ref hit
  subst u
  intro mounted target source node slot ref hit
  exact (fixedPorts mounted).transported_key source target hp (fixedProgram mounted) node slot ref hit

theorem mountedGoodWords (target : ∀i,boundaryWidth bank (venue v) i=boundaryWidth bank (venue v) i/p*p)
    (source : ∀i,(widthAt v) i=μ i*p) (node : (prg (venue v)).Node) :
    ((ofProgram (fun i=>boundaryWidth bank (venue v) i/p) target hp (prg (venue v))).keys node).length=
      ((ofProgram μ source hp (prog v)).keys (mountedGoodNode P G hw pay hardware key D m p hp fit s g v node)).length :=by
  revert hardware target source node
  subst u
  intro mounted target source node
  exact (congrArg List.length
    ((fixedPorts mounted).transported_keys source target hp (fixedProgram mounted) node)).trans
    (List.length_map _)

theorem mountedGoodIssued (target : ∀i,boundaryWidth bank (venue v) i=boundaryWidth bank (venue v) i/p*p)
    (source : ∀i,(widthAt v) i=μ i*p) (localNode : (prog v).Node) (slot : ℕ)
    (ref : BlockRef p (widthAt v))
    (hit : ((ofProgram μ source hp (prog v)).keys localNode)[slot]?=some (.inl ref)) :
    let node:=(mountedGoodNode P G hw pay hardware key D m p hp fit s g v).symm localNode
    ((ofProgram (fun i=>boundaryWidth bank (venue v) i/p) target hp (prg (venue v))).keys node)[slot]?=
      some (.inl ((mountedGoodPorts P G hw pay hardware D m p fit s g v).wordBlock ref)) :=by
  intro node
  apply mountedGoodKey P G hw pay hardware key D m p hp fit s g v target source node slot ref
  simpa only [node,Equiv.apply_symm_apply] using hit

-- The local tap instructions use the same finite enumeration as the good arm of selected.
local notation "itemEnum" => @Subtype.fintype I (fun a => P.owner s (P.contact a) = Sum.inl g)
  (fun _ => Classical.propDecidable _) inferInstance
local notation "chip" => (transportCircuit (b:=itemEnum) (G:=G) (hw:=hw) (pay:=pay) (sizedHardware s g))
local notation "tapLeg" => DescentResetGates.tapLegLane D (m*p) P.contact P.input P.site P.owner P.align s
  (.inl g) G (head P s g) (tail P s g) chip key (m:=m) (p:=p) rfl hp
local notation "backLane" => DescentBatchedRotor.tapLane D m p hp P.contact P.input P.site P.owner P.align s
  (.inl g) G (head P s g) (tail P s g) chip
variable (vertex : Fin (2^n))
variable (i : Fin (DescentPhysicalSplit.count (Physical.host G.arcs D
  (selectedRotorLayers P G hw pay (fit ▸ hardware : Hardware (K:=K) (C₀:=C₀) (u:=m*p) P G hw pay) s g)
  C₀ bits (m*p)) vertex))
local notation "tapSite" => (sizedSite).symm ⟨vertex,.inr i⟩
local notation "tapWidth" => widthAt tapSite
local notation "tapUnits" => (fun e=>tapWidth e/p)
local notation "gate" t => (mountedGoodNode P G hw pay hardware key D m p hp fit s g tapSite).symm (.inr t)

private theorem equal_wire_args {J : Type} {w : J → ℕ} {Y p : ℕ} (a b : Lane p w) :
    List.ofFn (DescentLaneGates.equalOp (Y:=Y) (.wire a) (.wire b)).arg = [a,b] := by
  simp [DescentLaneGates.equalOp, List.ofFn_succ]

private theorem key_after_one_lane {J : Type} {w : J → ℕ} {Y p : ℕ}
    (units : J → ℕ) (whole : ∀a, w a = units a*p) (positive : 0<p)
    (q : DescentLaneGates.Program Y p w) (node : q.Node) (back l : Lane p w)
    (args : List.ofFn (q.op node).arg = [back,l]) (within : Fin (l.count units)) :
    ((ofProgram units whole positive q).keys node)[back.count units + within.val]? =
      some (.inl (laneBlock units whole positive l within)) := by
  simpa only [List.map_cons, List.map_nil, List.sum_singleton] using
    program_key_on units whole positive q node [back] [] l args within

/-- A true live public selector appends its named lane after the back-spine
words. The native bank port is obtained by the original selected hardware
installation, even when the two lanes have different extents. -/
theorem installedKnownTap
    (t : DescentLaneGates.Block (selectedRotorLayers P G hw pay sizedHardware s g) m
      (@DescentResetGates.tapBits (Cells P s g) K itemEnum _ D (m*p) n h bits C₀ G hw pay _ _ chip vertex i))
    (target : ∀e,boundaryWidth bank (venue tapSite) e=boundaryWidth bank (venue tapSite) e/p*p)
    (source : ∀e,tapWidth e=tapUnits e*p) (l : Lane p tapWidth)
    (live : tapLeg vertex i t.1 t.2.1 t.2.2=.wire l) (within : Fin (l.count tapUnits)) :
    let back:=backLane vertex i true ⟨i,t⟩
    ((ofProgram (fun e=>boundaryWidth bank (venue tapSite) e/p) target hp (prg (venue tapSite))).keys (gate t))[back.count tapUnits+within.val]? =
      some (.inl ((mountedGoodPorts P G hw pay hardware D m p fit s g tapSite).wordBlock
        (laneBlock tapUnits source hp l within))) :=by
  intro back
  apply mountedGoodIssued P G hw pay hardware key D m p hp fit s g tapSite target source (.inr t)
    (back.count tapUnits + within.val) (laneBlock tapUnits source hp l within)
  have args : List.ofFn (((prog tapSite).op (.inr t)).arg)=[back,l]:=by
    change List.ofFn ((DescentLaneGates.equalOp (Y:=2^n) (.wire back) (tapLeg vertex i t.1 t.2.1 t.2.2)).arg)=[back,l]
    rw [live]
    exact equal_wire_args back l
  exact key_after_one_lane tapUnits source hp (prog tapSite) (.inr t) back l args within

end
end Hierarchy.DescentChosenRouter

end OAI
