import OAI.Hierarchy.DescentPackedScore
import OAI.Hierarchy.ProtocolRAMEndpointPrefix
import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # Native reduction of the packed local private-word counts -/

namespace Hierarchy.DescentPackedPrivateSum
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open ProtocolRAM DescentSIMDLookup
open scoped Fin.CommRing BigOperators
noncomputable section

structure Layout where
  source : Bank
  rom : Bank
  words : ℕ
  starts : ℕ

namespace Layout
variable (L : Layout) {w a M H r : ℕ}

def count (H r M : ℕ) := H * chunks r M

def program (w H r M : ℕ) :=
  (scan w L.words (count H r M) (DescentPackedScore.read L.source L.rom)).seq
    (ProtocolRAMEndpointPrefix.exclusive w L.words L.starts (count H r M))

def billed (H r M : ℕ) := (4+count H r M*28)+(10+(3+12*count H r M))

structure Room (w H r M : ℕ) : Prop where
  src : L.source.Fits w L.words
  rom : L.rom.Fits w L.words
  sep : L.words+count H r M≤L.starts
  endMem : L.starts+count H r M+1<2^w

def scores (H r M : ℕ) (m : Memory w) :=
  ProtocolRAM.image L.words (count H r M) (DescentPackedScore.read L.source L.rom) m

def prefixValue (H r M : ℕ) (m : Memory w) (t : ℕ) := ∑i∈Finset.range t,(L.scores H r M m (L.words+i)).val

def image (H r M : ℕ) (m : Memory w) :=
  ProtocolRAMEndpointPrefix.image L.starts (L.prefixValue H r M m) (L.scores H r M m) (count H r M)

theorem run (m : Memory w) (space : L.Room w H r M) :
    (L.program w H r M).Exec m (L.image H r M m) (billed H r M) := by
  have step : (scan w L.words (count H r M) (DescentPackedScore.read L.source L.rom)).Exec m
      (L.scores H r M m) (4+count H r M*28) := by
    have fit : (DescentPackedScore.read L.source L.rom).Fits w L.words := ⟨space.rom,space.src,trivial⟩
    have easy := space.sep
    have finish:= space.endMem
    intro labels registers slots machine pc reg pub exit rom advice cfg raw enter equal
    exact scan_exec L.words (count H r M) _ m fit (by omega) machine pc reg pub exit rom advice cfg raw enter equal
  have sums : (ProtocolRAMEndpointPrefix.exclusive w L.words L.starts (count H r M)).Exec (L.scores H r M m)
      (L.image H r M m) (10+(3+12*count H r M)) := by
    apply ProtocolRAMEndpointPrefix.run _ _ _ _ _ space.sep space.endMem
    · simp [prefixValue]
    · intro i _
      simp [prefixValue,Finset.sum_range_succ]
  intro P R C mach pc reg pub exit rom advice cfg raw enter equal
  exact Procedure.Exec.then step sums mach pc reg pub exit rom advice cfg raw enter equal

theorem read (f : Cell a→ℕ) (x : Fin H→Fin r→Cell a) (m : Memory w) (space : L.Room w H r M)
    (zero : f 0=0) (positive : 0<M) (rows : count H r M ≤ L.source.size) (width : L.rom.bits=a*M)
    (ready : DescentPackedScore.Input (M:=M) L.source L.rom f x m) :
    L.image H r M m (L.starts+count H r M)=((∑v,∑j,f (x v j)):ℕ) := by
  have cell := DescentPackedScore.expr_reads L.source L.rom L.words f x m space.src space.rom rows width ready
  have eqv (t : ℕ) (lim : t≤count H r M) :
      (L.prefixValue H r M m t:Word w)=(SumScores.total (DescentPackedScore.terms (M:=M) f x) t:Word w) := by
    induction t with
    | zero => simp [prefixValue]
    | succ t ih =>
      let i : Fin (count H r M) := ⟨t,by omega⟩
      have got:=ProtocolRAMGeneratedWrite.read_image L.words (count H r M)
        (DescentPackedScore.read L.source L.rom) m i
      have add := SumScores.total_next (DescentPackedScore.terms (M:=M) f x) i
      change SumScores.total _ (t+1)=_ at add
      rw [add,Nat.cast_add]
      have prev:=ih (by omega)
      have proj : (L.scores H r M m (L.words+t):Word w)=((DescentPackedScore.terms (M:=M) f x i):Word w) :=
        got.trans (cell i)
      simpa [prefixValue,Finset.sum_range_succ] using congrArg₂ (·+·) prev proj
  rw [image,ProtocolRAMEndpointPrefix.read _ _ _ _ _ (le_refl _),eqv _ (le_refl _)]
  exact congrArg (fun q : ℕ=>(q:Word w)) ((SumScores.total_all (DescentPackedScore.terms (M:=M) f x)).trans (DescentPackedScore.total f zero x positive))

theorem frame (H r M : ℕ) (m : Memory w) (address : ℕ) (before : address<L.words)
    (space : L.Room w H r M) : L.image H r M m address=m address := by
  have ord:=space.sep
  rw [image,ProtocolRAMEndpointPrefix.frame _ _ _ _ _ (.inl (by omega)),scores,
    ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl before)]

theorem tariff (w H r a : ℕ) (ha : 0<a) (wide : 2*a≤w) :
    billed H r (lanes w a)*w≤40*(w+H*w+4*H*r*a) ∧ 2^(a*lanes w a)≤2^(w/2) := by
  have vol:=volume H r w a ha wide
  obtain ⟨_,rom⟩:=DescentPackedScore.invoice H r w a ha wide
  refine ⟨?_,rom⟩
  change (4+H*chunks r (lanes w a)*28+(10+(3+12*(H*chunks r (lanes w a)))))*w≤_
  nlinarith only [Nat.mul_le_mul_left 40 vol,Nat.zero_le w]

end Layout
end
end Hierarchy.DescentPackedPrivateSum

end OAI
