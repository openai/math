import OAI.Hierarchy.DescentPostedStemInputs
import OAI.Hierarchy.DescentOriginalStemWordIssue
import OAI.Hierarchy.DescentOriginalBoardGeometry
import OAI.Hierarchy.DescentNamedStemSector
import OAI.Hierarchy.DescentCalendarRealStemAux
import OAI.Hierarchy.DescentReachedOriginalWords

namespace OAI
/-! # The original stem sector at the actual end of its dated publication -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSIMDLookup DescentPackedZip DescentDatedAddressBook
open DescentPacking DescentResetOriginalSlots DescentResetFieldAssembler DescentResetStemWord
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option hygiene false
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
variable {a : PhysicalReset} {start w : ℕ} (I : a.DateInputs start w)
local notation "v" => a.successor
local notation "s" => (v).sheets
local notation "b₀" => a.rebased start
local notation "base" => ((v).remap b₀).endAddress
local notation "stem_" => I.numbered.stemSide base
local notation "post" m:arg => (I.numbered.publicSide base).dst
  (I.numbered.prefixOutput base (I.masked.image (I.privateResult m)))
local notation "ng" => S.groupCount (i+1)
local notation "num" => stemsCount B
local notation "sector" => CandidateSheet.index num (contactCount B) (privateCount B)
local notation "oldRank" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "Z" => B.reset
local notation "T" => B.terminals

private theorem post_cast_groups {a n n' H M w : ℕ} {e : Expr} {m : Memory w} (h : n=n')
    (val : Fin H→Fin n'→Cell a) (r : Source e val M m) :
    Source e (fun rowId g=>val rowId (g.cast h)) M m:=by subst n';exact r

theorem original_stem_fn (shape : I.numbered.geometry=publicShape B)
    (deg : I.numbered.degree=input.placement.degree) (dim : I.numbered.blockBits=k) :
    (stem_).laws=stemLaws B (s).stemBits I.numbered.resultBits:=by
  change DescentResetStemWord.withHost I.numbered.degree I.numbered.blockBits I.numbered.geometry.depth
    I.numbered.geometry.ports I.numbered.geometry.span I.numbered.geometry.cap
    I.numbered.geometry.sockets I.numbered.geometry.program I.numbered.resultBits=_
  rw [shape,deg,dim]
  rfl

set_option maxHeartbeats 650000 in
/-- Publish every original stem and carry the same typed receiver, host and group through the
literal sparse bank, including rows whose old stem is absent. -/
theorem posted_original_stems (ok : I.Ready) (m : Memory w)
    (pad : Fintype.card input.V≤S.hostSize i) (bound : Fintype.card B.next.V≤(s).hosts)
    (blockAt : (s).blocks=2^k) (groupAt : (s).groups=ng) (nStem : I.numbered.stems=num)
    (shape : I.numbered.geometry=publicShape B) (deg : I.numbered.degree=input.placement.degree)
    (dim : I.numbered.blockBits=k) (sides : ∀j:Fin num,I.numbered.side (j.cast nStem.symm)=(stemTag B j).1)
    (hostRoom : input.placement.degree+1<2^(s).stemBits)
    (observed : ∃vals : Block k→Fin num→Fin (s).hosts→Fin ng→Fin 6→Cell (s).stemBits,
      (∀x j t,Source (I.stemRegisters x.val j.val t) (fun h g=>vals x j h g t) (s).lanes (post m)) ∧
      ∀x j,StemInputs B (originalTrunkRack B) x (stemTag B j).1 (stemTag B j).2 (vals x j)) :
    ∀(x : Block k) (j : Fin num),Source
      (.lookup (bank ((s).original base) (s).rows (s).candidates x.val
        (I.numbered.stemShelf (j.cast nStem.symm)).val) .row)
      (fun h gr=>(actualParentNumber B (rackOf B (((Z).denseHostRank T
        ((oldRank).trans (Fin.castLEEmb pad))).trans (Fin.castLEEmb bound)))
        x ((sector) (.inl j)) h (gr.cast groupAt):Cell I.numbered.resultBits))
      (s).lanes ((stem_).image (post m)) :=by
  obtain ⟨val,issued,holds⟩:=observed
  have law:=original_stem_fn B I shape deg dim
  have rows : (stem_).rows=(s).hosts*chunks ng (stem_).M:=by
    change (s).hosts*chunks (s).groups (s).lanes=_;rw [groupAt]; rfl
  have dead (side : Bool) : (stem_).laws side (fun _=>0)=0:=by rw [law];exact stemLaws_zero B _ _ _
  intro x j
  have got:=(stem_).issued_one ok.numbers.stem (post m) rows dead (x.cast blockAt.symm)
    (j.cast nStem.symm) (val x j) (issued x j)
  have shelf : stemShelf B j=(sector) (.inl j):=Fin.ext rfl
  have point := stem_read_number (b:=I.numbered.resultBits) B (originalTrunkRack B) x (stemTag B j).1
    (stemTag B j).2 (val x j) (holds x j) hostRoom
  have exactRow : (fun h g=>(stem_).laws ((stem_).side (j.cast nStem.symm)) (val x j h g)) =
      (fun h g=>(actualParentNumber B (originalTrunkRack B) x ((sector) (.inl j)) h g : Cell I.numbered.resultBits)) := by
    funext h g
    exact (congrFun (congrFun law _) _).trans
      ((congrArg (fun side => stemLaws B (s).stemBits I.numbered.resultBits side (val x j h g)) (sides j)).trans
      ((point h g).trans (congrArg (fun idx => (actualParentNumber B (originalTrunkRack B) x idx h g : Cell I.numbered.resultBits))
        ((stem_shelf_number B j).trans shelf))))
  let term : Expr := .lookup (bank ((s).original base) (s).rows (s).candidates x.val
    (I.numbered.stemShelf (j.cast nStem.symm)).val) .row
  let run := (stem_).image (post m)
  let read := fun values : Fin (s).hosts → Fin ng → Cell I.numbered.resultBits =>
    Source term values (s).lanes run
  have observedRow : read (fun h g => (stem_).laws ((stem_).side (j.cast nStem.symm)) (val x j h g)) := got
  have transferred := (congrArg read exactRow).mp observedRow
  let objective := fun rack' : Fin (s).hosts → Option B.next.V =>
    Source term (fun h gr => (actualParentNumber B rack' x ((sector) (.inl j)) h (gr.cast groupAt) : Cell I.numbered.resultBits))
      (s).lanes run
  have published : objective (originalTrunkRack B) :=
    post_cast_groups (a:=I.numbered.resultBits) («H»:=(s).hosts) (M:=(s).lanes) (w:=w) (e:=term) (m:=run)
      groupAt (fun h g => (actualParentNumber B (originalTrunkRack B) x ((sector) (.inl j)) h g : Cell I.numbered.resultBits)) transferred
  exact (congrArg objective (rack_of_original B pad bound)).mpr published

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
