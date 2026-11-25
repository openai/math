import OAI.Hierarchy.DescentOperandVectorArena
import OAI.Hierarchy.DescentPrivateNativePhase

namespace OAI
/-! # One fixed native ordinary suffix for all seven retained operand fields -/
namespace Hierarchy.DescentOperandVectorArena
open DescentOperandStateBanks DescentSIMDLookup DescentVectorBookReshape
open DescentOrdinaryAtomFieldRAM.ScalarOperand DescentSixParty.Chronology
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
noncomputable section
variable {D k K cap w : ℕ} {l : Layout}

/-- All coordinates and register addresses are fixed by the calendar.
The fields of this record contain addresses and dimensions, with no loads. -/
structure Wiring (l : Layout) (D k K cap : ℕ) where
  resolverSize : ℕ
  aliasBits : ℕ
  field : ℕ
  hosts : ℕ
  groups : ℕ
  lanes : ℕ
  inputs : Write.Sources l.operands
  refs : Fin l.pageCount→Fin l.lows→Refs D k K cap

namespace Wiring
variable (C : Wiring l D k K cap)
def writeCode (w start : ℕ):=Write.issue C.resolverSize C.aliasBits C.field C.hosts C.groups C.lanes start (l.norm start) w C.inputs
def writeTime (start : ℕ):=Write.work C.resolverSize C.aliasBits C.field C.hosts C.groups C.lanes start (l.norm start) C.inputs
def written (start : ℕ) (m : Memory w):=Write.imageAt C.resolverSize C.aliasBits C.field C.hosts C.groups C.lanes start (l.norm start) C.inputs m
def gatherCode (w start : ℕ):=DescentGatheredVectorReshape.program C.refs l.hosts (l.groups*l.radix) l.groups l.radix l.lanes l.bookBits (l.tables start) (l.out start) w (l.scratch start)
def gatherTime (start : ℕ):=DescentGatheredVectorReshape.ticks C.refs l.hosts (l.groups*l.radix) l.groups l.radix l.lanes l.bookBits (l.scratch start)
def program (w start : ℕ):=(C.writeCode w start).seq (C.gatherCode w start)
def ticks (start : ℕ):=C.writeTime start+C.gatherTime start
def image (start : ℕ) (m : Memory w):=DescentGatheredVectorReshape.result C.refs l.hosts (l.groups*l.radix) l.groups l.radix l.lanes l.bookBits (l.tables start) (l.out start) (l.scratch start) (C.written start m)

theorem cheap (w start : ℕ) : CheapCode (C.program w start) :=by
  apply cheap_seq
  · exact cheap_seq (DescentOrdinaryAtomFieldRAM.ROM.cheap _ _ w start) (program_cheap w _)
  · exact DescentGatheredVectorReshape.cheap C.refs l.hosts (l.groups*l.radix) l.groups
      l.radix l.lanes l.bookBits (l.tables start) (l.out start) w (l.scratch start)

def phase (w start : ℕ) : NativePhase w :=⟨C.program w start,C.ticks start,C.image start,C.cheap w start⟩

/-- The hypotheses here mention only public address ranges and field widths. -/
structure Fits (C : Wiring l D k K cap) (w start : ℕ) : Prop where
  rows : l.normalizedRows=C.hosts*chunks C.groups C.lanes
  aperture : l.stateBits=Write.aperture C.resolverSize C.aliasBits C.lanes
  radix : 0<l.radix
  lanes : 0<l.lanes
  before : Write.Early C.inputs w start
  entries : ∀p j,((C.refs p j).expr l.hosts).inputEnd≤(l.scratch start).base
  stop : l.endAddress start<2^w

theorem any (start : ℕ) (m : Memory w) (fit : C.Fits w start) : (C.phase w start).Runs m :=
  issue l start fit.stop C.resolverSize C.aliasBits C.field C.hosts C.groups C.lanes C.inputs m C.refs
    (l.groups*l.radix) fit.rows fit.aperture rfl fit.lanes fit.radix fit.before fit.entries

theorem frame (start : ℕ) (m : Memory w) (fit : C.Fits w start) (a : ℕ) (apart : a < start ∨ l.endAddress start≤a) :
    C.image start m a=m a :=by
  have prepared:=normalized l start fit.stop
  have fst:=Write.run (k:=C.resolverSize) (b:=C.aliasBits) (coeff:=C.field)
    (H:=C.hosts) (G:=C.groups) (M:=C.lanes) C.inputs m fit.before
    (by simpa only [fit.aperture] using prepared.1) (by simpa only [fit.rows,Layout.pageCount,DescentOperandStateBanks.pageSize] using prepared.2)
  have chunks_eq:=chunks_group l.groups l.lanes l.radix fit.lanes fit.radix
  have foot:=DescentGatheredVectorReshape.frame C.refs l.hosts (l.groups*l.radix) l.groups l.radix l.lanes l.bookBits
    (l.tables start) (l.out start) (l.scratch start) (C.written start m) a
  have A : start≤(l.scratch start).base:=by dsimp only [Layout.scratch,Layout.norm];omega
  have B : (l.scratch start).base≤l.tables start:=Nat.le_add_right ..
  have T := (arranged l start fit.stop).early
  have E : l.out start+l.dstWords≤l.endAddress start:=Nat.le_add_right ..
  have sc : (l.scratch start).base+(l.pageCount*l.lows)*(l.hosts*chunks l.groups l.lanes)≤l.tables start:=by
    change _≤(l.scratch start).base+rounded l.srcWords
    apply Nat.add_le_add_left
    have h : l.srcWords≤rounded l.srcWords:=(Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)
    simpa only [Layout.srcWords,sourceWords,Nat.mul_assoc] using h
  have normEnd : l.norm start+l.pageCount*l.normalizedRows≤(l.scratch start).base:=Nat.le_add_right ..
  rcases apart with low|high
  · have before:=low.trans_le A
    exact (foot (.inl before) (.inl (before.trans_le B)) (.inl ((before.trans_le B).trans_le ((Nat.le_add_right ..).trans T)))).trans (fst.2.2.1 a (.inl low))
  · have afterOut:=E.trans high
    have startAfter : l.out start≤a:=(Nat.le_add_right ..).trans afterOut
    have tableAfter:=T.trans startAfter
    have baseAfter : l.tables start≤a:=(Nat.le_add_right ..).trans tableAfter
    have closed:=foot (.inr (by rw [chunks_eq];exact sc.trans baseAfter)) (.inr tableAfter) (.inr afterOut)
    apply closed.trans
    apply fst.2.2.1 a
    right;right
    simpa only [fit.rows,Layout.pageCount,DescentOperandStateBanks.pageSize] using
      normEnd.trans (B.trans baseAfter)

end Wiring
end
end Hierarchy.DescentOperandVectorArena

end OAI
