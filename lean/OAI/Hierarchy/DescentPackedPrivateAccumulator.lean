import OAI.Hierarchy.DescentPackedPrivateSum
import OAI.Hierarchy.DescentPrivateExponentRAM

namespace OAI
/-! # Add whole absorbed widths from packed native site panels to the prior private-bit total -/

namespace Hierarchy.DescentPackedPrivateAccumulator
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open ProtocolRAM DescentPackedPrivateSum DescentSIMDLookup DescentPrivateEdgeCounter
open scoped Fin.CommRing BigOperators
noncomputable section
variable {w : ℕ} (L : Layout)

/-- The panel prefix produces its last word before both single-cell outputs. -/
structure Counters where
  prior : ℕ
  words : ℕ
  scaled : ℕ
  out : ℕ

namespace Counters
variable (C : Counters)

def scaling : DescentPrivateExponentRAM.Banks := ⟨C.prior,C.words,C.scaled,C.out⟩

def plus := Expr.op .add (cell C.prior) (cell C.scaled)

def add (w grain : ℕ) := (ProtocolRAMStaticPorts.program w C.scaled 1 grain (cell C.words)).seq
  (scan w C.out 1 C.plus)

def sumImage (grain used : ℕ) (m : Memory w) :=
  ProtocolRAM.image C.out 1 C.plus (C.scaling.scaled grain used m)

private theorem fits {a out : ℕ} (before : a<out) (space : 1<2^w) : (cell a).Fits w out :=
  ⟨⟨by simp [Bank.size],by simpa [Bank.size] using space,by simpa [Bank.size] using before⟩,trivial⟩

theorem add_run (grain : ℕ) (m : Memory w) (space : C.scaling.Room w) :
    (C.add w grain).Exec m (C.sumImage grain (m C.words).val m) (C.scaling.steps grain) := by
  have last:=space.endMem
  have t:=space.temp
  have u:=space.active
  have v:=space.volume
  change C.out+1<2^w at last
  change C.scaled<C.out at t
  change C.words<C.scaled at u
  change C.prior<C.scaled at v
  have enough : 1<2^w := by omega
  have scale : (ProtocolRAMStaticPorts.program w C.scaled 1 grain (cell C.words)).Exec m
      (C.scaling.scaled grain (m C.words).val m) (ProtocolRAMStaticPorts.work 1 grain (cell C.words)) := by
    apply ProtocolRAMStaticPorts.run _ _ (DescentPrivateExponentRAM.index (m C.words).val) _ _ (fits u enough) (by omega)
    intro i
    rw [cell_read]
    simp [DescentPrivateExponentRAM.index]
  have finish : (scan w C.out 1 C.plus).Exec (C.scaling.scaled grain (m C.words).val m)
      (C.sumImage grain (m C.words).val m) (4+1*(2*C.plus.work+4)) :=
    scan_exec _ _ _ _ (show C.plus.Fits w C.out from ⟨fits (by omega) enough,fits t enough⟩) last
  intro P R C₀ mach pc reg pub exit rom advice cfg raw enter equal
  exact Procedure.Exec.then scale finish mach pc reg pub exit rom advice cfg raw enter equal

theorem add_read (grain used old : ℕ) (m : Memory w) (space : C.scaling.Room w)
    (past : m C.prior=(old:Word w)) :
    C.sumImage grain used m C.out=((old+used*grain:ℕ):Word w) := by
  have got:=ProtocolRAMGeneratedWrite.read_image C.out 1 C.plus (C.scaling.scaled grain used m) (0:Fin 1)
  rw [show C.sumImage grain used m C.out=C.plus.eval (C.scaling.scaled grain used m) 0 by simpa [sumImage] using got]
  change (cell C.prior).eval _ 0+(cell C.scaled).eval _ 0=_
  rw [cell_read,cell_read]
  have atScale:=ProtocolRAMStaticPorts.read C.scaled grain (DescentPrivateExponentRAM.index used) m (0:Fin 1)
  rw [show C.scaling.scaled grain used m C.scaled=((used*grain:ℕ):Word w) by
    simpa [DescentPrivateExponentRAM.scaled,scaling,DescentPrivateExponentRAM.index] using atScale]
  change ProtocolRAMStaticPorts.image C.scaled grain (DescentPrivateExponentRAM.index used) m C.prior+_=_
  have lower : C.prior<C.scaled := space.volume
  rw [ProtocolRAMStaticPorts.frame _ _ _ _ _ (.inl lower),past,Nat.cast_add]

end Counters

variable (C : Counters) {H r M a : ℕ}

def program (w H r M grain : ℕ) := (L.program w H r M).seq (C.add w grain)

def image (H r M grain : ℕ) (m : Memory w) :=
  let readback:=L.image H r M m
  C.sumImage grain (readback C.words).val readback

theorem run (grain : ℕ) (m : Memory w) (room : L.Room w H r M) (space : C.scaling.Room w) :
    (program L C w H r M grain).Exec m (image L C H r M grain m) (Layout.billed H r M+C.scaling.steps grain) := by
  intro P R C₀ mach pc reg pub exit rom advice cfg raw enter equal
  exact Procedure.Exec.then (L.run m room) (C.add_run grain _ space) mach pc reg pub exit rom advice cfg raw enter equal

theorem read (score : Cell a→ℕ) (x : Fin H→Fin r→Cell a) (grain old : ℕ) (m : Memory w)
    (room : L.Room w H r M) (space : C.scaling.Room w) (zero : score 0=0) (positive : 0<M)
    (rows : Layout.count H r M≤L.source.size) (width : L.rom.bits=a*M)
    (ready : DescentPackedScore.Input (M:=M) L.source L.rom score x m)
    (atEnd : C.words=L.starts+Layout.count H r M) (held : C.prior<L.words) (oldVal : m C.prior=(old:Word w)) :
    image L C H r M grain m C.out=((old+(∑v,∑i,score (x v i))*grain:ℕ):Word w) := by
  have got:=L.read score x m room zero positive rows width ready
  rw [←atEnd] at got
  have preserved:= (L.frame H r M m C.prior held room).trans oldVal
  rw [image,C.add_read _ _ _ _ space preserved,Nat.cast_add,Nat.cast_mul]
  have lift : (((L.image H r M m C.words).val:ℕ):Word w)=((∑v,∑i,score (x v i):ℕ):Word w) := by simpa using got
  rw [lift,Nat.cast_add,Nat.cast_mul]

theorem tariff (w H r a grain : ℕ) (ha : 0<a) (wide : 2*a≤w) :
    (Layout.billed H r (lanes w a)+C.scaling.steps grain)*w ≤
      40*(w+H*w+4*H*r*a)+(56+4*ProtocolRAMPortScale.bitWidth grain)*w ∧ 2^(a*lanes w a)≤2^(w/2) := by
  obtain ⟨work,rom⟩:=Layout.tariff w H r a ha wide
  refine ⟨?_,rom⟩
  rw [Nat.add_mul,DescentPrivateExponentRAM.steps_eq]
  exact Nat.add_le_add_right work _

end
end Hierarchy.DescentPackedPrivateAccumulator

end OAI
