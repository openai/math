import OAI.Hierarchy.DescentRetainedCableBlock
import OAI.Hierarchy.DescentRetainedResetPinPointer
import OAI.Hierarchy.DescentRetainedOriginalLanding
import OAI.Hierarchy.DescentResetOriginRank
import OAI.Hierarchy.DescentResetEmittedFirstCable

namespace OAI
/-! # The normalized end of a retained reset cable, at the original argument ordinal -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentStageEdgeReceipt
open DescentParallelBase DescentResetSignedScan DescentNextSignedWindow DescentCableDonorNames
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
open scoped Fin.CommRing
open private emit_core emit_free from OAI.Hierarchy.DescentResetSplitUnits
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => (Z).orderedReentry T birth
local notation "cnt" => fun e=>(coarse).graph.width e/(Z).unit
local notation "world" => (Z).orderedOrdinary T birth
local notation "tape" => (Z).nativeResetEdges T vertexCode birth
local notation "index" => (tape).order.trans Fin.valEmbedding
local notation "dense" => ((Z).rawHostRank T vertexCode).trans Fin.valEmbedding
local notation "groups" => S.groupCount (i+1)
local notation "rawSite" => B.raw.siteFrom (DescentStageEdgeReceipt.groupRank (Fin.valEmbedding (n:=groups)) dense) B.valid.coordinates
local notation "hop" => DescentPhysicalOrder.rename rawSite
local notation "sparse" => DescentResetLocalOrder.allCode B.raw index S B.valid rawSite
local notation "renameEdge" => DescentPhysicalOrder.rename sparse
open DescentBundleHistory DescentKernelHistory DescentRetainedCableBlock DescentPrimitivePalette
open DescentRetainedResetPinPointer DescentResetTrunks DescentOperandPriorIncidence DescentLocalArchiveOrder
open Chronology Computability.BorderVNP.Crossing ThreeFlat.Routing
variable {p R : ℕ}
variable (hp : 0<p) (one : 1≤R) (pos : 0<B.reset.unit) (whole : p∣B.reset.unit)
    (wide : max 1 (max B.reset.width (C*B.reset.width))≤R) (a : Archive W) (sh : WorldShape p R a.bit)
local notation "split_" => sh.granular B.count (z*G.b) B.fit hp (B.unit ▸ pos) (B.unit ▸ whole)
local notation "fixed_" => ((Nat.div_mul_cancel whole).symm : (Z).unit=(Z).unit/p*p)
local notation "pre_" => reentryWorldShape split_ Z T birth _ hp fixed_ (resetMenu B) one wide
local notation "after_" => WorldShape.follow hp pos whole B.reblock B.cuts pre_
local notation "next_" => (resetArchive B p hp whole a).bit
local notation "books_" => closedBooks B hp one pos whole wide a sh
local notation "old_" => W.granular B.count (z*G.b) B.fit
local notation "per_" => (Z).unit/p
local notation "side_" v:max e:max => originFace v e
local notation "unit_" s:max e:max => carriedUnit B s e
local notation "parent_" s:max e:max => carriedParent B s e
local notation "emit_" s:max e:max => emit B (unit_ s e).val.1
local notation "cursor_" s:max e:max low:max => (unit_ s e).val.1.2.val*per_+low

include hp whole pos in
private theorem per_positive : 0<per_:= Nat.div_pos (Nat.le_of_dvd pos whole) hp

private theorem transport_cable {first last : MarkedWorld F d P bits}
    {a₀ : BitDescription first} {a₁ : BitDescription last}
    {src : WorldShape p R a₀} {dst : WorldShape p R a₁}
    (hp : 0<p) (book : SiteBooks hp dst src) (x : NodeOrder.All a₁)
    {arg cursor residue : ℕ} {fromEdge : first.graph.Edge} {toEdge : last.graph.Edge}
    (seen : AtCable src hp (book.nodeAt hp x) arg fromEdge cursor)
    (address : ∀ (inc : Incident first.graph (book.home x.1)) (full : (cursor+1)*p≤first.graph.width inc.val),
      inc.val=fromEdge → ((book.atSite x.1).publicWord ⟨.inl inc,cursor,full⟩).cableNumber last.graph x.1 =
        some (toEdge,residue)) : AtCable dst hp x arg toEdge residue := by
  obtain ⟨ordinal,inc,full,idx,parent,read⟩:=cable_read seen
  let localBook:=book.atSite x.1
  let now:=ordinal.cast (localBook.length x.2).symm
  let start : BlockRef p (boundaryWidth first.graph (book.home x.1)):=⟨.inl inc,cursor,full⟩
  refine ⟨now,localBook.publicWord start,idx,localBook.publicHit x.2 now start ?_,address inc full parent⟩
  have keep : Fin.cast (localBook.length x.2) now = ordinal := Fin.ext rfl
  rw [keep]
  exact read

private theorem named_cut_cable {A₀ : MarkedWorld F d P bits} {base : BitDescription A₀}
    (hp : 0<p) (source : WorldShape p R base) (count : A₀.graph.Edge→ℕ) (q : ℕ)
    (cut : ∀ e ∈ A₀.core, A₀.graph.width e=count e*q) (pos : 0<q) (unit : p∣q)
    (sites : Equiv.Perm A₀.graph.Site) (edges : Equiv.Perm (A₀.pieces q count cut).graph.Edge)
    (x : NodeOrder.All ((base.pieces count q cut).renamed sites edges))
    (arg : ℕ) (parent : A₀.graph.Edge) (target : (A₀.pieces q count cut).graph.Edge)
    (offset low : ℕ) (fits : low<q/p)
    (marked : ∀ (h : parent∈A₀.core) (j : Fin (count parent)), j.val=offset →
        edges (.inr ⟨⟨parent,h⟩,j⟩) = target)
    (unmarked : ∀ (h : parent∉A₀.core), edges (.inl ⟨parent,h⟩) = target) :
    let canon:=SiteBooks.trans hp (SiteBooks.rename hp (source.pieces count q cut hp pos unit) sites edges)
          (SiteBooks.split hp source count q cut pos unit)
    AtCable source hp (canon.nodeAt hp x) arg parent (offset*(q/p)+low) →
      AtCable ((source.pieces count q cut hp pos unit).renamed sites edges) hp x arg target
        (if parent∈A₀.core then low else offset*(q/p)+low) := by
  intro canon seen
  apply transport_cable hp canon x seen
  rintro ⟨wire,hw⟩ full rfl
  by_cases mark : wire∈A₀.core
  · obtain ⟨j,quotient,result⟩:=named_split_block hp source count q cut pos unit sites edges x.1
      ⟨wire,hw⟩ (offset*(q/p)+low) full mark
    have positive : 0<q/p := Nat.div_pos (Nat.le_of_dvd pos unit) hp
    have number : j.val=offset := by
      rw [quotient,Nat.mul_comm offset,Nat.mul_add_div positive,Nat.div_eq_of_lt fits,Nat.add_zero]
    have residue : (offset*(q/p)+low)%(q/p)=low := by
      rw [Nat.mul_comm offset,Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt fits]
    rw [ite_eq_left mark]
    exact result.trans (congrArg some (Prod.ext (marked mark j number) residue))
  · have result:=named_unsplit_block hp source count q cut pos unit sites edges x.1
        ⟨wire,hw⟩ (offset*(q/p)+low) full mark
    rw [ite_eq_right mark]
    exact result.trans (congrArg some (Prod.ext (unmarked mark) rfl))

/-- The true normalized primary reads the emitted child of the selected paid mother;
unmarked cables retain the full cursor in their original cable. -/
theorem named_carried (x : NodeOrder.All next_) (arg : ℕ) (s : Bool) (edge : (old_).graph.Edge)
    (low : ℕ) (fits : low<per_)
    (seen : AtCable pre_ hp ((books_).nodeAt hp x) arg (parent_ s edge) (cursor_ s edge low)) :
    AtCable after_ hp x arg (emit_ s edge).1
      (if parent_ s edge∈(coarse).core then low else cursor_ s edge low):=by
  rw [closedBooks_node B hp one pos whole wide a sh] at seen
  rw [DescentResetFreshWires.closed_shape B hp one pos whole wide a sh]
  apply named_cut_cable hp pre_ cnt (Z).unit ((Z).counts_fit T) pos whole hop renameEdge x arg
    (parent_ s edge) (emit_ s edge).1 (unit_ s edge).val.1.2.val low fits _ _ seen
  · intro mark j eqOrd
    change renameEdge (piece B ⟨parent_ s edge,mark⟩ j) = _
    change renameEdge (piece B ⟨parent_ s edge,mark⟩ j) = (emit B ⟨parent_ s edge,(unit_ s edge).val.1.2⟩).1
    have eqn:=congrArg (fun t : Stage.Grain B.next.placement => t.1)
      (emit_core B (parent_ s edge) mark (unit_ s edge).val.1.2)
    apply Eq.trans _ eqn.symm
    exact congrArg (fun t => renameEdge (piece B ⟨parent_ s edge,mark⟩ t)) (Fin.ext eqOrd)
  · intro mark
    change renameEdge (.inl ⟨parent_ s edge,mark⟩) = (emit B ⟨parent_ s edge,(unit_ s edge).val.1.2⟩).1
    exact (congrArg (fun t : Stage.Grain B.next.placement => t.1)
      (emit_free B (parent_ s edge) mark (unit_ s edge).val.1.2)).symm

/-- Left ends (including loops) enter their actual outgoing stem. Right ends enter the
joined trunk at the chronological offset of their occupied grain. -/
theorem carried_block (x : NodeOrder.All next_) (y : NodeOrder.All a.bit)
    (origin : resetOrigin B hp whole a x=.inl y)
    (arg : ℕ) (edge : Incident W.graph y.1) (chunk : ℕ) (was : AtCable sh hp y arg edge.val chunk)
    (n₀ : Fin (B.count edge.val)) (high : n₀.val=chunk/per_) :
    let grain : (old_).graph.Edge:=⟨edge.val,n₀⟩
    let s:=side_ y.1 edge
    AtCable after_ hp x arg (emit_ s grain).1
      (if parent_ s grain∈(coarse).core then chunk%per_ else cursor_ s grain (chunk%per_)):=by
  intro grain s
  obtain ⟨j,chosen,raw⟩:=granular sh hp B.count (z*G.b) B.fit (B.unit ▸ pos) (B.unit ▸ whole) y arg edge.val chunk was
  have val : j.val=n₀.val:=by rw [chosen,high,B.unit]
  cases (Fin.ext val : j=n₀)
  have room:=Nat.mod_lt chunk (per_positive B hp pos whole)
  apply named_carried B hp one pos whole wide a sh x arg s grain _ room
  let inc:=DescentRetainedCableBlock.incomingPrefix (W:=old_) (T).home birth grain
  have increment : inc/p=earlierIncoming B grain*per_:=by
    have alive:0<weight B (stemParent B (true,grain)):=by
      change 0<(blocks B).count (stemParent B (true,grain));rw [stem_one];decide
    exact (incoming_chunks B grain alive p per_ hp fixed_).trans
      (congrArg (·*per_) (incoming_sourceTicket B grain alive))
  have atBase : AtCable pre_ hp ((books_).nodeAt hp x) arg
    ((installedWireNames old_ (T).home (Z).placement.input (T).hub _ (Z).bank (Z).tables).symm
      (if s then .inr (.inl ((T).home ((old_).graph.dst grain))) else .inl (false,grain)))
    ((if s then inc/p else 0)+chunk%per_):=by
    rw [closedBooks_node B hp one pos whole wide a sh]
    unfold reentryWorldShape
    apply DescentRetainedCableBlock.installed (s:=split_) (hp:=hp) (y:=y) (origin:=origin)
      (j:=arg) (edge:=grain) (chunk:=chunk%per_)
    simpa only [B.unit] using raw
  have parent_eq : ((installedWireNames old_ (T).home (Z).placement.input (T).hub _ (Z).bank (Z).tables).symm
      (if s then .inr (.inl ((T).home ((old_).graph.dst grain))) else .inl (false,grain))) = parent_ s grain := by
    cases s <;> rfl
  have index_eq : (if s then inc/p else 0)+chunk%per_ = cursor_ s grain (chunk%per_) := by
    cases s <;>simp only [Bool.false_eq_true,ite_false,ite_true,carriedUnit,increment,Nat.zero_mul,Nat.zero_add]
  rw [parent_eq,index_eq] at atBase
  exact atBase

/-- The old primary really is the source vertex of the emitted cable at both types of old end. -/
theorem carried_at_source (x : NodeOrder.All next_) (y : NodeOrder.All a.bit)
    (origin : resetOrigin B hp whole a x=.inl y) (edge : Incident W.graph y.1) (n₀ : Fin (B.count edge.val)) :
    let grain : (old_).graph.Edge:=⟨edge.val,n₀⟩
    B.reblock.result.graph.src (emit_ (side_ y.1 edge) grain).1=x.1:=by
  intro grain
  have nodeSite:=reached_node_site B hp whole a x
  rw [origin] at nodeSite
  change hop ((Z).oldOwner T y.1)=x.1 at nodeSite
  rw [←nodeSite]
  apply B.next.valid.coordinates
  have parent:=primary_cell B (side_ y.1 edge) grain
  have term : DescentResetAttachments.ends (old_).graph (side_ y.1 edge) grain=y.1:=by
    by_cases src:W.graph.src edge.val=y.1
    · rw [show originFace y.1 edge = false by simp [originFace,src]]
      exact src
    · rw [show originFace y.1 edge = true by simp [originFace,src]]
      exact edge.property.resolve_left src
  rw [term] at parent
  let unit:=unit_ (side_ y.1 edge) grain
  have coord:=(blocks B).atSource (parent_ (side_ y.1 edge) grain) unit.val.1.2
  change Stage.home B.next.placement (B.reblock.result.graph.src
    (((Stage.stream B.next.placement (B.next.order.trans Fin.valEmbedding)).symm
      (Stage.stream B.next.placement (B.next.order.trans Fin.valEmbedding) (emit B unit.val.1))).1))=_ at coord
  rw [Equiv.symm_apply_apply] at coord
  exact coord.trans parent

local notation "names_" => DescentPacking.PackedMatch.Local.Stage.cableNames k (groupRank
  ((Function.Embedding.refl (Fin (S.groupCount (i+1)))).trans Fin.valEmbedding) (B.next.vertex.trans Fin.valEmbedding))
local notation "wing_" => DescentPackedOperand.Public.endpoint B.next.placement (B.next.order.trans Fin.valEmbedding)
  S B.next.valid names_

/-- At the original finite argument the true normalized pointer reads the source face of
the emitted cable, with a remainder on a split mother and the full cursor on a tether. -/
theorem closed_cable (rank : Local next_) (pin : P→ℕ) (args : ℕ) (x : NodeOrder.All next_) (y : NodeOrder.All a.bit)
    (origin : resetOrigin B hp whole a x=.inl y)
    (j : Fin (((sh.sites y.1).recipe hp).arity y.2)) (edge : Incident W.graph y.1) (chunk : ℕ)
    (full : (chunk+1)*p≤W.graph.width edge.val)
    (was : ((sh.sites y.1).recipe hp).operand y.2 j=.inl ⟨.inl edge,chunk,full⟩)
    (n₀ : Fin (B.count edge.val)) (high : n₀.val=chunk/per_) :
    let grain : (old_).graph.Edge:=⟨edge.val,n₀⟩
    let s:=side_ y.1 edge
    let wing:=wing_ false (emit_ s grain)
    let output:=if parent_ s grain∈(coarse).core then chunk%per_ else cursor_ s grain (chunk%per_)
    Reached.argumentPointer B.next next_ rank after_ hp pin args x j.val=
      .cable wing.neighbor.val (wing.wire.val-wing.within.val) output:=by
  intro grain s wing output
  have oldRead : AtCable sh hp y j.val edge.val chunk:=⟨j,_,rfl,was,rfl⟩
  have seen:=carried_block B hp one pos whole wide a sh x y origin j.val edge chunk oldRead n₀ high
  obtain ⟨idx,inc,ok,num,found,read⟩:=cable_read seen
  have active:=Reached.argumentPointer_cable B.next next_ rank after_ hp pin args x.1 x.2 idx inc output ok read
  rw [num] at active
  have atSrc:B.reblock.result.graph.src inc.val=x.1:=by
    rw [found];exact carried_at_source B hp whole a x y origin edge n₀
  have cable:=B.next.firstCable_emission hp (blocks B) (fun e=>e∈(coarse).core) (emission B)
    x.1 inc output ok (parent_ s grain) (unit_ s grain).val.1.2 found.symm
  apply active.trans
  simp only [atSrc,ne_eq,not_true_eq_false,decide_false] at cable
  exact cable

/-- The same argument points into the signed register published by the reset period. -/
theorem posted_cable (rank : Local next_) (pin : P→ℕ) (args : ℕ) (x : NodeOrder.All next_) (y : NodeOrder.All a.bit)
    (origin : resetOrigin B hp whole a x=.inl y)
    (j : Fin (((sh.sites y.1).recipe hp).arity y.2)) (edge : Incident W.graph y.1) (chunk : ℕ)
    (full : (chunk+1)*p≤W.graph.width edge.val)
    (was : ((sh.sites y.1).recipe hp).operand y.2 j=.inl ⟨.inl edge,chunk,full⟩)
    (n₀ : Fin (B.count edge.val)) (high : n₀.val=chunk/per_) :
    let grain : (old_).graph.Edge:=⟨edge.val,n₀⟩
    let s:=side_ y.1 edge
    let u:=unit_ s grain
    let wing:=Stage.live B.next.placement (B.next.order.trans Fin.valEmbedding) S B.next.valid (fieldNames B) _
      (GrainPorts.port B.next.placement (B.next.order.trans Fin.valEmbedding) (blocks B) _ u)
    let output:=if parent_ s grain∈(coarse).core then chunk%per_ else cursor_ s grain (chunk%per_)
    Reached.argumentPointer B.next next_ rank after_ hp pin args x j.val=
      .cable wing.neighbor.val (wing.wire.val-wing.within.val) output:=by
  intro grain s u wing output
  have oldRead : AtCable sh hp y j.val edge.val chunk:=⟨j,_,rfl,was,rfl⟩
  have seen:=carried_block B hp one pos whole wide a sh x y origin j.val edge chunk oldRead n₀ high
  obtain ⟨idx,inc,ok,num,found,read⟩:=cable_read seen
  have active:=Reached.argumentPointer_cable B.next next_ rank after_ hp pin args x.1 x.2 idx inc output ok read
  rw [num] at active
  have atSrc:B.reblock.result.graph.src inc.val=x.1:=by
    rw [found];exact carried_at_source B hp whole a x y origin edge n₀
  exact active.trans (emitted_first_cable B hp _ u x.1 inc output ok found.symm atSrc).symm

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
