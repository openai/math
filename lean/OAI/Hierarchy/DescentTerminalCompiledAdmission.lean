import OAI.Hierarchy.DescentTerminalCompiledPrefixRuntime
import OAI.Hierarchy.DescentTerminalRowFrames

namespace OAI
/-! # Both sticky words and the private scalar on the actual combined prefix -/
namespace Hierarchy.DescentTerminalCompiledPrefix
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open DescentExterior DescentExteriorShelf DescentTerminalEmitter
open scoped Classical Fin.CommRing
noncomputable section
variable {w:ℕ} (S:Shape) (L:Layout)
local notation "j" => S.terminal.plane.headBits
local notation "r" => S.terminal.plane.restBits
local notation "e" => S.terminal.plane.exteriors
local notation "t" => S.terminal.plane.bitLanes
local notation "origin" => L.emit.plane.exterior
local notation "flag" => flagAt («j»:=j) («r»:=r) («t»:=t) («e»:=e) origin

structure Frozen (p:ℕ) : Prop where
  memories : DescentTerminalRowPlan.Lower L.row p
  books : p<L.row.books.base
  offsets : p<L.offset.offsets.base
  sort : p<L.order.src
  pages : p<L.emit.leaf.event.base

theorem counted_preserved (m:Memory w) (ok:Room S L w) {a:ℕ} (low:Frozen L a) :
    planned S L m a=counted S L m a := by
  rw [planned,DescentTerminalChipRuntime.image_low _ _ _ _ low.pages,ordered,
    DescentTerminalExteriorPackets.sort_before _ _ _ _ _ _ ok.ordering low.sort,rowed,DescentTerminalSiteOffsets.early _ _ _ low.offsets,allocated,
    DescentTerminalRowPlan.before_publishing _ _ ok.plan low.memories low.books]

structure Protected (a:ℕ) : Prop where
  packed : a<L.count.words
  scaled : a≠L.exponent.usedBits
  dead : a≠L.exponent.deadBits
  print : Frozen L a

theorem rowed_preserved (m : Memory w) (ok : Room S L w) {a : ℕ} (p : Protected L a) :
    rowed S L m a=m a := by
  rw [rowed,DescentTerminalSiteOffsets.early _ _ _ p.print.offsets,allocated,
    DescentTerminalRowPlan.before_publishing _ _ ok.plan p.print.memories p.print.books,counted,
    DescentPackedTerminalExponent.image,DescentPrivateExponentRAM.Banks.frame _ _ _ _ _ p.scaled p.dead,
    DescentPackedPrivateSum.Layout.image,ProtocolRAMEndpointPrefix.frame _ _ _ _ _
      (.inl (by have:=ok.packed.sep;have:=p.packed;omega)),
    DescentPackedPrivateSum.Layout.scores,DescentTerminalChipRuntime.image_low _ _ _ _ p.packed]

/-- The inverse rank used by the public-field gather is present in this exact native prefix. -/
theorem ordered_port (m : Memory w) (ok : Room S L w) (home : Fin S.packets→Fin S.sites)
    (issued : ∀i,L.homes.read m (i.val:Word w)=((home i).val:Word w))
    (keep : ∀i : Fin S.packets,Protected L (L.homes.base+(i.val:Word w).val%L.homes.size))
    (i : Fin S.packets) :
    ordered S L m (L.order.sorted+i.val)=(((Computability.BorderVNP.FragmentBucket.dest home).symm i).val:Word w) := by
  refine DescentTerminalExteriorPackets.sort_id _ _ _ _ _ S.sites_pos ok.ordering home ?_ i
  intro q
  change rowed S L m _=_
  rw [rowed_preserved S L m ok (keep q)]
  exact issued q

theorem planned_preserved (m:Memory w) (ok:Room S L w) {a:ℕ} (p:Protected L a) :
    planned S L m a=m a := by
  rw [counted_preserved S L m ok p.print,counted,DescentPackedTerminalExponent.image,
    DescentPrivateExponentRAM.Banks.frame _ _ _ _ _ p.scaled p.dead,DescentPackedPrivateSum.Layout.image,
    ProtocolRAMEndpointPrefix.frame _ _ _ _ _ (.inl (by have:=ok.packed.sep;have:=p.packed;omega)),
    DescentPackedPrivateSum.Layout.scores,DescentTerminalChipRuntime.image_low _ _ _ _ p.packed]

theorem live_scalar (m:Memory w) (ok:Room S L w) (p:Frozen L L.exponent.deadBits)
    (early:BeforeKey S.terminal L.emit L.exponent.deadBits) (later:AfterFlights S.terminal L.emit L.exponent.deadBits)
    {c:ℕ} (issued:counted S L m L.exponent.deadBits=(c:Word w)) :
    result S L m L.exponent.deadBits=(c:Word w) := by
  rw [result,printed_before _ _ _ ok.emit early later,counted_preserved S L m ok p,issued]

theorem admitted {A T:Type} (m:Memory w) (ok:Room S L w) (positive:0<w) (bitsFit:2^j*t≤w)
    (seed:ℕ) (keep:Protected L seed) (early:BeforeKey S.terminal L.emit seed)
    (late:AfterFlights S.terminal L.emit seed) (tail:AfterFlights S.terminal L.emit flag)
    (x:Fin e→Plane j r→Fin t→Bool) (layout:T→Fin e→DescentGL.Layout (j+(j+r)))
    (read:(A→Bool)→Option T) (z:A⊕Hidden e j r t→Bool)
    (first:m seed=0 ↔ ∃c,read (z∘Sum.inl)=some c)
    (original:∀c,read (z∘Sum.inl)=some c→Loaded origin (layout c) x (z∘Sum.inr) m)
    (shelf:∀(b:Fin 17) (u:Fin (span j r t e)),Protected L ((bank j r t e origin b.val).base+u.val)) :
    (result S L m seed=0 ∧ result S L m flag=0) ↔ ∃c,proposed read layout x z=some c := by
  apply accepted S.terminal L.emit (planned S L m) ok.emit positive bitsFit seed early late tail x layout read z
  · rw [planned_preserved S L m ok keep];exact first
  · intro c good b u hu
    rw [planned_preserved S L m ok (shelf b ⟨u,hu⟩)]
    exact original c good b u hu

end
end Hierarchy.DescentTerminalCompiledPrefix

end OAI
