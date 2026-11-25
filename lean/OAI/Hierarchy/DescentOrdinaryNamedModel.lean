import OAI.Hierarchy.DescentOrdinarySignedGeometry
import OAI.Hierarchy.DescentIssuedChartAgreement
import OAI.Hierarchy.DescentIssuedChronology

namespace OAI
/-! The original geometric presentation of an issued ordinary successor, including the physical permutations. -/
namespace Hierarchy.DescentStageEdgeReceipt
open DescentSixParty DescentSixParty.StarKeys DescentHostDirectory DescentHostDegree DescentKernelHistory DescentPacking
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P H : Type} [Field F] [Fintype H] [DecidableEq H] {d : ℕ} {bits : P→ℕ}
variable {W:MarkedWorld F d P bits} {G:PoweredGadget F} {u ε:ℝ}
variable (he:0≤ε) (T:StageInput W G u ε) (c:(T.result he).Choice)
local notation "rr" => BitDescription.scannedRows he T
local notation "layout" => bestLayout (branchWidth G (fun _ : (rr).pairs=>T.z) ((rr).profile c))
local notation "actor" => GadgetNetwork.newSite W.graph (rr).pick layout (rr).pack
local notation "gain" => gainExponent 20 T.Δ
local notation "number" => PairRAM.globalNumberBy W.graph W.core (scanHomeAt he T) (scanColorAt he T) T.cap
  (originalId (ScanColonies he T))
variable (oldID:W.graph.Edge↪Fin (Fintype.card W.graph.Edge))
structure OrdinaryModel (H:Type) [Fintype H] [DecidableEq H] where
  chart : IssuedDonorChart he T H
  old : ∀e∈W.core,T.z∣W.graph.width e
  used : ∀j,(rr).pick j∈W.core
  site : (MarkedWorld.subroundNormalize W G (rr).pick (fun _ => T.z) (fun _ => T.unitPos)
    (rr).fit (rr).pack ((rr).profile c) (chart.key he T c) chart.hub T.k gain T.z old used (fun _=>dvd_refl T.z)).result.graph.Site↪ℕ

namespace OrdinaryModel
variable (B:OrdinaryModel he T c H)
abbrev normalized:=MarkedWorld.subroundNormalize W G (rr).pick (fun _ => T.z) (fun _ => T.unitPos)
  (rr).fit (rr).pack ((rr).profile c) (B.chart.key he T c) B.chart.hub T.k gain T.z B.old B.used (fun _=>dvd_refl T.z)
abbrev tape:=ordinary W G oldID number (rr).pick (fun _=>T.z) (fun _=>T.unitPos) (rr).fit (rr).pack ((rr).profile c)
  (B.chart.key he T c) B.chart.hub T.k gain T.z B.old B.used (fun _=>dvd_refl T.z)
abbrev siteMap:=DescentPhysicalOrder.rename B.site
abbrev edgeMap:=DescentPhysicalOrder.rename ((B.tape he T c oldID).sourceKey (B.normalized he T c).result.graph.src
  B.site (B.normalized he T c).result.graph.width)
abbrev named:=(B.normalized he T c).appendNames (B.siteMap he T c) (B.edgeMap he T c oldID)
abbrev namedTape:=Tape.afterNames (B.normalized he T c) (B.tape he T c oldID) (B.siteMap he T c) (B.edgeMap he T c oldID)
end OrdinaryModel

variable {root:H↪ℕ} {Y:MarkedWorld F d P bits} {n:Normalize Y} {t:Tape n.result.graph.Edge} {pair:ScanNumbers he T}

/-- A genuine named trajectory step determines a single old chart, normalized edge decomposition, and site order. -/
theorem IssuedRows.named_model (issued:IssuedRows he T c oldID root Y n t pair) (only:n.nameCount=1)
    (quantum:n.CutsEqual T.z) :
    ∃B:OrdinaryModel he T c H,HEq n (B.named he T c oldID) ∧ HEq t (B.namedTape he T c oldID) ∧ pair=number :=by
  let Q:SignedClaim he T:=fun _ n t pair=>n.CutsEqual T.z→
    ∃B:OrdinaryModel he T c H,HEq n (B.named he T c oldID) ∧ HEq t (B.namedTape he T c oldID) ∧ pair=number
  apply issued.signedCases only (Q:=Q) _ quantum
  intro col same hub k g q legal source old used cut profile key pairs norm tape site siteRename edgeRename grain
  obtain ⟨_,hk,hg,_,hc,codes,olds⟩:=source
  subst k
  subst g
  have prev:=(Normalize.cutsEqual_appendNames _ _ _ _).mp grain
  have eqn:q=T.z:=prev.1
  subst q
  let b:IssuedDonorChart he T H:=⟨col,same,hub,hc,codes,olds⟩
  exact ⟨⟨b,old,used,site⟩,HEq.rfl,HEq.rfl,rfl⟩

namespace OrdinaryModel
variable (B:OrdinaryModel he T c H)
local notation "key" => B.chart.key he T c
local notation "last" => MarkedWorld.address (W.selected G (rr).pick (fun _=>T.z) (fun _=>T.unitPos) (rr).fit (rr).pack ((rr).profile c))
  key B.chart.hub T.k gain
abbrev rawSite (x:(rawGraph he T c).Site) := B.siteMap he T c (last (actor x))

/-- Transport the actual reached world once. Every raw vertex then has its original
common-host coordinate after the very same site permutation, including empty vertices. -/
theorem locations (input:Y=scanWorld he T c) (same:HEq n (B.named he T c oldID)) :
    ∃eqn : n.result=(B.named he T c oldID).result,∀x:(rawGraph he T c).Site,
      cast (congrArg (fun world:MarkedWorld F d P bits=>world.graph.Site) eqn)
        (n.destination (rawInput he T c input x))=B.rawSite he T c x :=by
  subst Y
  obtain rfl:=eq_of_heq same
  exact ⟨rfl,fun _=>rfl⟩

omit [Field F] in
private theorem transported_order (left right : MarkedWorld F d P bits) (worldEq : left = right)
    (rank : right.graph.Site ↪ ℕ) (a b : left.graph.Site) (x y : right.graph.Site)
    (hx : cast (congrArg (fun w : MarkedWorld F d P bits => w.graph.Site) worldEq) a =
      DescentPhysicalOrder.rename rank x)
    (hy : cast (congrArg (fun w : MarkedWorld F d P bits => w.graph.Site) worldEq) b =
      DescentPhysicalOrder.rename rank y) :
    originalId left.graph.Site a < originalId left.graph.Site b ↔ rank x < rank y := by
  cases worldEq
  change a = DescentPhysicalOrder.rename rank x at hx
  change b = DescentPhysicalOrder.rename rank y at hy
  subst a
  subst b
  change (Fintype.equivFin _ (DescentPhysicalOrder.rename rank x)).val <
    (Fintype.equivFin _ (DescentPhysicalOrder.rename rank y)).val ↔ _
  rw [DescentPhysicalOrder.code_rename, DescentPhysicalOrder.code_rename]
  exact DescentPhysicalOrder.physical_lt_iff rank x y

set_option maxHeartbeats 1200000 in
theorem old_rank (input:Y=scanWorld he T c) (eqn:n.result=(B.named he T c oldID).result)
    (placed : ∀x:(rawGraph he T c).Site,cast (congrArg (fun p:MarkedWorld F d P bits=>p.graph.Site) eqn)
      (n.destination (rawInput he T c input x))=B.rawSite he T c x) (x y:(rawGraph he T c).Site) :
    (originalId n.result.graph.Site) (n.destination (rawInput he T c input x)) <
      (originalId n.result.graph.Site) (n.destination (rawInput he T c input y)) ↔
      B.site (last (actor x))<B.site (last (actor y)) :=by
  exact transported_order n.result (B.named he T c oldID).result eqn B.site
    (n.destination (rawInput he T c input x)) (n.destination (rawInput he T c input y))
    (last (actor x)) (last (actor y)) (placed x) (placed y)

end OrdinaryModel

end
end Hierarchy.DescentStageEdgeReceipt

end OAI
