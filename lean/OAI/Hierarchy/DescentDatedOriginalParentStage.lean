import OAI.Hierarchy.DescentDatedOriginalParentModel
import OAI.Hierarchy.DescentOrdinaryOriginalRoster
import OAI.Hierarchy.DescentOrdinaryNamedModel

namespace OAI
/-! Original normalized presentation and incoming route banks on one actual ordinary date. -/
namespace Hierarchy.DescentSixParty.Chronology.OrdinaryLink
open DescentCableDonorNames DescentRawCablePanel DescentStageEdgeReceipt DescentSIMDLookup DescentOrdinaryAtomFieldRAM DescentHaloWalkRAM
open DescentHostDegree DescentHostDirectory StarKeys DescentPacking DescentPacking.PackedMatch.Local
open DescentPacking.PackedMatch.Local.Stage DescentKernelHistory
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
variable {S : DescentCompiler.AtomSchedule} {q ε : ℝ} {k i z D wire hist w short a : ℕ}
variable {W : MarkedWorld F d P bits} {prior : Reached W G q ε S k i z D wire hist}
set_option quotPrecheck false
attribute [local irreducible] StarKeys.nativeKey
local notation "A" => prior.placement
local notation "J" => Fin (S.groupCount i)
local notation "V" => prior.V
local notation "native" => prior.order.trans Fin.valEmbedding
local notation "rank" => groupRank Fin.valEmbedding (prior.vertex.trans Fin.valEmbedding)
variable {he : 0≤ε} {choice : (prior.placement.stage.result he).Choice}
    {n : Normalize ((prior.placement.stage.result he).state choice)}
variable {z' D' : ℕ} {next : Reached n.result G q ε S k (i+1) z' D' wire hist}
variable (ticket : OrdinaryLink prior he prior.placement.stage choice n next) (port : MeterPort prior)
local notation "H" => port.hosts
local notation "T" => (A).stage
local notation "home" => scanHomeAt he T
local notation "color" => scanColorAt he T
local notation "addr" => nativeAddress he T
local notation "r" => 2^k
local notation "rr" => BitDescription.scannedRows he T
local notation "lay" => bestLayout (branchWidth G (fun _ : (rr).pairs=>(T).z) ((rr).profile choice))
local notation "bytes" => donorNameBits (T).k (T).Δ
local notation "slots" => 2^(packExponent 20 (T).Δ)+2
local notation "gain" => gainExponent 20 (T).Δ
local notation "peers" => rotor A rank
local notation "grp" => Equiv.refl J
local notation "hosts" => port.vertex
variable (win : Fin (S.groupCount i)×prior.V→Fin (2^k)→Cell a) (hm : 0<port.groupsPerWord)
variable (named : prior.placement.SiteNamed (groupRank Fin.valEmbedding (prior.vertex.trans Fin.valEmbedding)))
    (fit : ∀u,(win (prior.placement.pos u) (prior.placement.block u)).val<2^short)
    (winner : ∀u,(win (prior.placement.pos u) (prior.placement.block u)).val=
      1+2*heap (nativeAddress he prior.placement.stage (scanHomeAt he prior.placement.stage u)).2+
        (scanColorAt he prior.placement.stage u).toNat)
    (df : prior.placement.degree<2^short)
    (order : ∀e f,(prior.order e).val<(prior.order f).val ↔ originalId W.graph.Edge e<originalId W.graph.Edge f)
variable (profile : ℕ)
local notation "positiveRows" => DescentRawCablePanel.Live A (rr).pick
local notation "model" => OrdinaryModel he T choice (J×V)
local notation "net" => rawGraph he T choice
local notation "place" => newSite W.graph (rr).pick lay (rr).pack
local notation:max "center" B:arg x:arg => mergeHub (B).chart.hub (T).k (gainExponent 20 (T).Δ) ((B).chart.key he T choice (place x))
local notation:max "current" x:arg => n.destination (rawInput he T choice ((rr).state choice) x)
local notation:max "oldRow" e:arg => (A).pos (W.graph.src (anchor (rr).pick (e).val))
local notation "caps" => 2^(packExponent 20 (T).Δ)+2
open DescentSixParty.MarkedWorld
variable (age:i<S.length) (radix:S.radix=2^k)

variable (B : OrdinaryModel he prior.placement.stage choice (Fin (S.groupCount i) × prior.V))
local notation "world" => (B.named he T choice prior.order).result
local notation "act" => B.rawSite he T choice
variable (coh : n.result=(B.named he prior.placement.stage choice prior.order).result)
variable (places : ∀x:(rawGraph he prior.placement.stage choice).Site,
    cast (congrArg (fun u:MarkedWorld F d P bits=>u.graph.Site) coh)
      (n.destination (rawInput he prior.placement.stage choice
        ((BitDescription.scannedRows he prior.placement.stage).state choice) x)) =
      B.rawSite he prior.placement.stage choice x)

def modelStage : GroupStage world G q ε (Fin (S.groupCount (i+1))) next.V k :=
  cast (congrArg (fun U:MarkedWorld F d P bits=>GroupStage U G q ε (Fin (S.groupCount (i+1))) next.V k) coh) next.placement

local notation "A₁" => modelStage («next»:=next) B coh

private theorem cast_bounds {U U':MarkedWorld F d P bits} (p:U=U')
    {j v:Type} [Fintype j] [DecidableEq j] [Fintype v] [DecidableEq v]
    (a:GroupStage U G q ε j v k) (s:DescentCompiler.AtomSchedule) (t:ℕ) (bound:a.StateBounds s t) :
    (cast (congrArg (fun u=>GroupStage u G q ε j v k) p) a).StateBounds s t:=by subst U';exact bound

private theorem cast_unit {U U':MarkedWorld F d P bits} (p:U=U')
    {j v : Type} [Fintype j] [DecidableEq j] [Fintype v] [DecidableEq v]
    (a:GroupStage U G q ε j v k) :
    (cast (congrArg (fun u=>GroupStage u G q ε j v k) p) a).z=a.z:=by subst U';rfl

private theorem cast_shape {U U':MarkedWorld F d P bits} (eqn:U=U')
    {j v:Type} [Fintype j] [DecidableEq j] [Fintype v] [DecidableEq v]
    (a:GroupStage U G q ε j v k) :
    let b:=cast (congrArg (fun u=>GroupStage u G q ε j v k) eqn) a
    b.cap=a.cap ∧ b.degree=a.degree ∧ b.z=a.z ∧ b.near=a.near :=by
  subst U'
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem model_shape : (A₁).cap=next.placement.cap ∧ (A₁).degree=next.placement.degree ∧
    (A₁).z=next.placement.z ∧ (A₁).near=next.placement.near :=cast_shape coh next.placement

theorem model_bounds : (A₁).StateBounds S (i+1) :=by
  exact cast_bounds coh next.placement S (i+1) next.valid

include ticket in
theorem model_grain : (A₁).z*G.b=(T).z :=by
  exact (congrArg (fun z₀ : ℕ => z₀*G.b) ((cast_unit coh next.placement).trans next.grain)).trans
    (ticket.grainStep.symm.trans (prior.grain.symm.trans ticket.quantum.symm))

private theorem transported_site {U U':MarkedWorld F d P bits} (p:U=U')
    {j v : Type} [Fintype j] [DecidableEq j] [Fintype v] [DecidableEq v]
    (a:GroupStage U G q ε j v k) (x:U.graph.Site) :
    let a':=cast (congrArg (fun u=>GroupStage u G q ε j v k) p) a
    let x':=cast (congrArg (fun u:MarkedWorld F d P bits=>u.graph.Site) p) x
    a'.pos x'=a.pos x ∧ a'.block x'=a.block x :=by subst U';exact ⟨rfl,rfl⟩

include places in
theorem model_placement (x:(net).Site) :
    (A₁).pos (act x)=next.placement.pos (current x) ∧ (A₁).block (act x)=next.placement.block (current x) :=by
  have atOld := transported_site coh next.placement (current x)
  exact ⟨(congrArg (A₁).pos (places x).symm).trans atOld.1,
    (congrArg (A₁).block (places x).symm).trans atOld.2⟩

include places in
theorem model_sites (x:(net).Site) :
    let key:=splitKey (center B x)
    let here:=act x
    (((A₁).pos here).1,(A₁).block here)=S.groupDigits age radix key.1 ∧
      (ticket.parentVenue port.enough ((A₁).pos here).2).1=hosts key.2.1 ∧
      (ticket.parentVenue port.enough ((A₁).pos here).2).2.val=SiteDecode.localNumber (T).k caps key.2 :=by
  dsimp only
  have p:=model_placement (next:=next) B coh places x
  have eq := B.chart.same_address he T choice ticket.donorChart (T).k (gainExponent 20 (T).Δ) (place x)
  change center B x=mergeHub ticket.donorHub (T).k (gainExponent 20 (T).Δ) (ticket.donorKey (place x)) at eq
  have keyEq := (ticket.rawParentKey_donor x).trans (congrArg (fun key₀ : Key (J × V) => splitKey key₀) eq.symm)
  let location (pos : (Fin (S.groupCount (i+1)) × next.V) × Fin (2^k)) (key₀ : J × Key V) :=
    (pos.1.1,pos.2)=S.groupDigits age radix key₀.1 ∧
      (ticket.parentVenue port.enough pos.1.2).1=hosts key₀.2.1 ∧
      (ticket.parentVenue port.enough pos.1.2).2.val=SiteDecode.localNumber (T).k caps key₀.2
  have read : location (next.placement.pos (current x),next.placement.block (current x)) (ticket.rawParentKey x) :=
    ticket.parentVenue_raw_location port.enough age radix x
  have pairEq : (next.placement.pos (current x),next.placement.block (current x)) =
      ((A₁).pos (act x),(A₁).block (act x)) := Prod.ext p.1.symm p.2.symm
  exact Eq.mp (congrArg₂ location pairEq keyEq) read

end
end Hierarchy.DescentSixParty.Chronology.OrdinaryLink

end OAI
