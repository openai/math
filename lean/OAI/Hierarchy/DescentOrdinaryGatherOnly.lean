import OAI.Hierarchy.DescentOrdinaryVectorPhase

namespace OAI
/-! # Move the already-issued operand books on an ordinary transition -/
namespace Hierarchy.DescentOperandVectorArena
open DescentOperandStateBanks DescentSIMDLookup DescentVectorBookReshape
open DescentOrdinaryAtomFieldRAM.ScalarOperand DescentSixParty.Chronology
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
noncomputable section
variable {D k K cap w : ℕ}
abbrev References (l : Layout) (D k K cap : ℕ) :=Fin l.pageCount→Fin l.lows→Refs D k K cap
namespace References
variable {l : Layout} (C : References l D k K cap)
def image (start : ℕ) (m : Memory w):=DescentGatheredVectorReshape.result C l.hosts (l.groups*l.radix)
  l.groups l.radix l.lanes l.bookBits (l.tables start) (l.out start) (l.scratch start) m
def phase (w start : ℕ) : NativePhase w :=
  ⟨DescentGatheredVectorReshape.program C l.hosts (l.groups*l.radix) l.groups l.radix l.lanes l.bookBits
      (l.tables start) (l.out start) w (l.scratch start),
    DescentGatheredVectorReshape.ticks C l.hosts (l.groups*l.radix) l.groups l.radix l.lanes l.bookBits (l.scratch start),
    image C start, DescentGatheredVectorReshape.cheap C l.hosts (l.groups*l.radix) l.groups
      l.radix l.lanes l.bookBits (l.tables start) (l.out start) w (l.scratch start)⟩
structure Room (C : References l D k K cap) (w start : ℕ) : Prop where
  radix : 0<l.radix
  lanes : 0<l.lanes
  early : ∀p j,((C p j).expr l.hosts).inputEnd≤(l.scratch start).base
  fits : l.endAddress start<2^w

theorem any (start : ℕ) (m : Memory w) (fit : Room C w start) :
    (phase C w start).Runs m ∧ ∀a,a<start ∨ l.endAddress start≤a → image C start m a=m a :=by
  have shifts:=chunks_group l.groups l.lanes l.radix fit.lanes fit.radix
  refine ⟨?_,?_⟩
  · exact DescentGatheredVectorReshape.exec C l.hosts (l.groups*l.radix) l.groups l.radix l.lanes l.bookBits
      (l.tables start) (l.out start) (l.scratch start) m fit.early (by rw [shifts];exact gather_room l start fit.fits)
      (arranged l start fit.fits)
  intro a apart
  have A : start≤(l.scratch start).base:=by dsimp only [Layout.scratch,Layout.norm];omega
  have B : (l.scratch start).base≤l.tables start:=Nat.le_add_right ..
  have T := (arranged l start fit.fits).early
  have E : l.out start+l.dstWords≤l.endAddress start:=Nat.le_add_right ..
  have sc : (l.scratch start).base+(l.pageCount*l.lows)*(l.hosts*chunks l.groups l.lanes)≤l.tables start:=by
    change _≤(l.scratch start).base+rounded l.srcWords
    apply Nat.add_le_add_left
    have h : l.srcWords≤rounded l.srcWords:=(Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)
    simpa only [Layout.srcWords,sourceWords,Nat.mul_assoc] using h
  apply DescentGatheredVectorReshape.frame C l.hosts (l.groups*l.radix) l.groups l.radix l.lanes l.bookBits
    (l.tables start) (l.out start) (l.scratch start) m a
  · rcases apart with h|h
    · exact .inl (h.trans_le A)
    · right;rw [shifts];exact sc.trans <| ((Nat.le_add_right ..).trans (T.trans <| (Nat.le_add_right ..).trans <| E.trans h))
  · exact apart.imp (fun h=>h.trans_le (A.trans B)) (fun h=>T.trans ((Nat.le_add_right ..).trans (E.trans h)))
  · exact apart.imp (fun h=>h.trans_le (A.trans (B.trans ((Nat.le_add_right ..).trans T)))) (fun h=>E.trans h)

end References
end
end Hierarchy.DescentOperandVectorArena

end OAI
