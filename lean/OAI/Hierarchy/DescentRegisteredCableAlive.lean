import OAI.Hierarchy.DescentReachedPointerCases

namespace OAI
/-! A raw cable feeding an attained public operand survives both ordinary contractions. -/
namespace Hierarchy.DescentLocalArchiveOrder
open Computability.BorderVNP.Crossing DescentSixParty DescentSixParty.Chronology DescentStageEdgeReceipt
open DescentCompiler DescentKernelHistory DescentBundleHistory DescentHostDirectory DescentHostDegree
open DescentPackedOperand DescentNetworkPartition
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d p R : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
variable {u q ε : ℝ} {S : AtomSchedule} {k i z D z' D' wire hist : ℕ}
    {cap : Reached W G q ε S k i z D wire hist}
    {he : 0≤ε} {T : StageInput W G u ε} {c : (T.result he).Choice}
    {n : Normalize ((T.result he).state c)} {target : Reached n.result G q ε S k (i+1) z' D' wire hist}
    (ticket : OrdinaryLink cap he T c n target) (arch : Archive W)
    (hp : 0<p) (one : 1≤R) (pin : ∀x,p∣bits x) (sh : WorldShape p R arch.bit) (unit : p∣T.z)
set_option quotPrecheck false
set_option backward.isDefEq.lazyProjDelta false
set_option backward.isDefEq.lazyWhnfCore false
attribute [local irreducible] BitDescription.scannedRows
local notation "r" => BitDescription.scannedRows he T
local notation "uni" => fun _ : (r).pairs=>T.z
local notation "pos" => fun _ : (r).pairs=>T.unitPos
local notation "room" => fun _ : (r).pairs=>le_refl T.z
local notation "whole" => fun _ : (r).pairs=>unit
local notation "prof" => (r).profile c
local notation "sel" => scanWorld he T c
local notation "after" => afterOrdinary hp one pin ticket arch sh unit
local notation "b" => privateChart ticket arch hp one pin sh unit
local notation "addr" => MarkedWorld.address sel ((b).key he T c) (b).hub T.k (gainExponent 20 T.Δ)
local notation "group" => GadgetNetwork.newSite W.graph (r).pick (bestLayout (branchWidth G uni prof)) (r).pack
local notation "loc" => addr ∘ group
local notation "M" => rawGraph he T c
local notation "baseShape" => physicalShape W arch.bit G (r).pick uni room prof hp sh.sites sh.edges pin whole
local notation "next" => (ticket.advance arch).bit
local notation "source" => operandSource ticket arch

local notation:max "srcArg" x:arg j:arg => ((baseShape (source x).1).recipe hp).operand (source x).2
  (sourceIndex ticket arch hp one pin sh unit x j)
local notation:max "sourceSite" x:arg => (source x).1
local notation:max "wireAt" x:arg => Incident (M) (sourceSite x)
local notation:max "equalHome" e:arg => loc ((M).src (e).val)=loc ((M).dst (e).val)

theorem uncaptured_source (x:NodeOrder.All next) (j:Fin ((((after).sites x.1).recipe hp).arity x.2))
    {b₀:BlockRef p (boundaryWidth n.result.graph x.1)}
    (hit:(((after).sites x.1).recipe hp).operand x.2 j=.inl b₀) (e:wireAt x)
    (piece:ℕ) (len:(piece+1)*p≤(M).width e.val)
    (read:srcArg x j=.inl ⟨.inl e,piece,len⟩) : ¬equalHome e:=by
  intro merged
  apply selectedSource_public_cases arch.bit G (r).pick uni pos (r).fit room (r).pack prof hp one pin sh whole
    ((b).key he T c) (b).hub T.k (gainExponent 20 T.Δ) (source x)
    (sourceIndex ticket arch hp one pin sh unit x j) (public_source ticket arch hp one pin sh unit x j hit)
  · intro edge chunk fit different original
    have eqEdge : edge = e := Sum.inl.inj (congrArg BlockRef.port (Sum.inl.inj (original.symm.trans read)))
    cases eqEdge
    exact different merged
  · intro pinRef chunk fit original
    have impossible := congrArg BlockRef.port (Sum.inl.inj (original.symm.trans read))
    cases impossible

end
end Hierarchy.DescentLocalArchiveOrder

end OAI
