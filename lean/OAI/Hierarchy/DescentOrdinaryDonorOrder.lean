import OAI.Hierarchy.DescentOrdinaryDonorHalo
import OAI.Hierarchy.DescentSharedCableNames
import OAI.Hierarchy.DescentSiteNameRead

namespace OAI
/-! # Positive normalized cable comparisons are read from four short fields -/
namespace Hierarchy.DescentOrdinaryDonorOrder
open Computability.BorderVNP.Crossing DescentSixParty DescentSixParty.StarKeys DescentSixParty.MarkedWorld
open DescentHostDirectory DescentColonies DescentPacking DescentStageEdgeReceipt DescentCableDonorNames
open DescentSharedCableNames
open scoped Classical BigOperators
noncomputable section
variable {F P I C H : Type} [Field F] [Fintype I] [DecidableEq H] {d : ℕ} {bits : P→ℕ}
variable (W : MarkedWorld F d P bits) (G : PoweredGadget F)
variable (edge : W.graph.Edge↪Fin (Fintype.card W.graph.Edge)) (pair : I≃Fin (Fintype.card I))
variable (pick : I×Fin 2↪W.graph.Edge) (z : I→ℕ) (hz : ∀i,0<z i)
variable (fit : ∀i s,W.graph.width (pick (i,s))=z i*G.b) (pack : W.graph.Site→C) (p : I→Profile G.C)
variable (key : (W.selected G pick z hz fit pack p).graph.Site↪Key H) (flag : H→Bool) (k g q : ℕ)
variable (old : ∀e∈W.core,q∣W.graph.width e) (picked : ∀j,pick j∈W.core) (affected : ∀i,q∣z i)
set_option quotPrecheck false
local notation "coarse" => coalesced (W.selected G pick z hz fit pack p) key flag k g
local notation "copies" => repetitions W G pick z hz fit pack p key flag k g q
local notation "childNet" => DescentCableUnbundling.network (coarse).graph (coarse).core copies q
local notation "childEdge" => DescentCableUnbundling.Edge (coarse).graph (coarse).core copies
local notation "childSite" => (coarse).graph.Site
local notation "originUnit" => DescentCableUnbundling.pieceUnit (coarse).graph (coarse).core copies q
local notation "childTape" => ordinary W G edge pair pick z hz fit pack p key flag k g q old picked affected
local notation "ancestry" => ancestryTicket W G edge pick z hz fit pack p key flag k g q old picked affected
local notation "rawOrigin" e => ((originUnit) e).1.val.val
local notation "parentEdge" e:arg => DescentCableDonorNames.anchor pick (rawOrigin e)
set_option quotPrecheck true
variable {J V : Type} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V] {age phase : ℕ} {price ε : ℝ}
variable (A : GroupStage W G price ε J V age) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S phase)
variable {D C' : ℕ}
  (roster : Halo (coalesced (W.selected G pick z hz fit pack p) key flag k g).graph.Site W.graph.Site D)

private abbrev donorMember {U T : Type} {slots : ℕ} (r : Halo U T slots) (v : U) (t : T) : Prop :=
  t ∈ r.member v

set_option maxHeartbeats 4000000 in
/-- The only earlier source pointer is its short outgoing slot at the
previous real source. The numeric donor field is the old canonical site ID
restricted to the actual bounded neighborhood of the new source. -/
def short (e : childEdge) (member : donorMember roster ((childNet).src e) (W.graph.src (parentEdge e)))
    (positive : 0<A.grainCount (parentEdge e)) (off : (childTape).offset e<C') : Ticket D A.cap C' :=
  by
    let parent : W.graph.Edge := parentEdge e
    let previousSite : W.graph.Site := W.graph.src parent
    let localSite : childSite := (childNet).src e
    let home : ↥(roster.member localSite) := ⟨previousSite, member⟩
    let oldCable : Stage.Positive A := ⟨parent, positive⟩
    let oldSlot : Fin A.cap := Stage.outgoing A (edge.trans Fin.valEmbedding) S ready oldCable
    let piece : Fin C' := ⟨(childTape).offset e, off⟩
    exact Ticket.mk (roster.slot localSite home) oldSlot (role (rawOrigin e)) piece


set_option quotPrecheck false in
local notation "compact" => Hierarchy.DescentOrdinaryDonorOrder.short W G edge pair pick z hz fit pack p key flag k g q old picked affected A S ready roster

set_option maxHeartbeats 4000000 in
theorem compare (ordered : ∀h (a b : ↥(roster.member h)),roster.slot h a<roster.slot h b ↔ originalId W.graph.Site a.val < originalId W.graph.Site b.val)
    (site : childSite↪ℕ) (a b : childEdge)
    (ap : 0<(childNet).width a) (bp : 0<(childNet).width b) (same : (childNet).src a=(childNet).src b)
    (am : donorMember roster ((childNet).src a) (W.graph.src (parentEdge a))) (bm : donorMember roster ((childNet).src b) (W.graph.src (parentEdge b)))
    (av : 0<A.grainCount (parentEdge a)) (bv : 0<A.grainCount (parentEdge b)) (ao : (childTape).offset a<C') (bo : (childTape).offset b<C') :
    (childTape).sourceKey (childNet).src site (childNet).width a<(childTape).sourceKey (childNet).src site (childNet).width b ↔
      code (compact a am av ao)<code (compact b bm bv bo) := by
  rw [(childTape).sourceKey_lt (childNet).src site (childNet).width a b ap bp same]
  change code (ancestry a)<code (ancestry b) ↔ _
  symm
  let x:=compact a am av ao
  let y:=compact b bm bv bo
  let u : ↥(roster.member ((childNet).src b)):=⟨W.graph.src (parentEdge a),same ▸ am⟩
  let v : ↥(roster.member ((childNet).src b)):=⟨W.graph.src (parentEdge b),bm⟩
  have transport {l r : childSite} (equal:l=r) (n:W.graph.Site) (m:n∈roster.member l) (m':n∈roster.member r) :
      roster.slot l ⟨n,m⟩=roster.slot r ⟨n,m'⟩ :=by subst r;rfl
  have xa : x.donor=roster.slot ((childNet).src b) u :=transport same _ _ _
  have yb : y.donor=roster.slot ((childNet).src b) v :=rfl
  have eqSite : x.donor=y.donor ↔ W.graph.src (parentEdge a)=W.graph.src (parentEdge b) := by
    rw [xa,yb,Function.Embedding.apply_eq_iff_eq,Subtype.ext_iff]
  apply rebase_lt x y (ancestry a) (ancestry b)
  · rw [xa,yb];exact ordered ((childNet).src b) u v
  · exact eqSite.trans (Fintype.equivFin W.graph.Site).apply_eq_iff_eq.symm
  · intro equal
    exact Stage.outgoing_lt A (edge.trans Fin.valEmbedding) S ready ⟨parentEdge a,av⟩ ⟨parentEdge b,bv⟩ (eqSite.mp equal)
  · intro equal;constructor
    · intro ov
      have back:=Stage.outgoing_identify A (edge.trans Fin.valEmbedding) S ready ⟨parentEdge a,av⟩ ⟨parentEdge b,bv⟩ (eqSite.mp equal) ov
      exact congrArg edge (congrArg Subtype.val back)
    · intro ov
      have deq : (parentEdge a) = (parentEdge b) := edge.injective ov
      exact congrArg (Stage.outgoing A (edge.trans Fin.valEmbedding) S ready) (Subtype.ext deq)
  · rfl
  · rfl
  · rfl
  · rfl

/-- In a genuinely named previous world, an immutable old rack/block
rectangle compares exactly as `Fintype.equivFin` of the previous sites. This
supplies `compare`'s `ordered` argument without a dynamic occupied-site sort. -/
theorem named_raster (prior : J×V↪ℕ) (named : A.SiteNamed prior) (coordinates : Function.Injective (fun u=>(A.pos u,A.block u)))
    (key' : Key (J×V)) (x y : ↥(DescentOrdinaryDonorHalo.siteSet (groupedNear A.near) A.pos key')) :
    let bound:=fun v : J×V=>(grouped_degree A.near v).le.trans (A.degreeBound v.2)
    let raster:=DescentOrdinaryDonorHalo.raster (groupedNear A.near) A.pos A.block coordinates A.degree bound prior
    raster.slot key' x<raster.slot key' y ↔ originalId W.graph.Site x.val<originalId W.graph.Site y.val := by
  intro bound raster
  let number : W.graph.Site ↪ ℕ := A.siteFrom prior coordinates
  have id (s : W.graph.Site) : originalId W.graph.Site s=(DescentPhysicalOrder.physical number s).val:=
    (named s).trans (DescentPhysicalOrder.physical_val number s).symm
  rw [id x.val, id y.val]
  exact (DescentOrdinaryDonorHalo.raster_lt (groupedNear A.near) A.pos A.block coordinates A.degree bound prior key' x y).trans
    (DescentPhysicalOrder.physical_lt_iff number x.val y.val).symm

end
end Hierarchy.DescentOrdinaryDonorOrder

end OAI
