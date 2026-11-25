import OAI.Hierarchy.ProtocolRAMFrozenWindowBanks
import OAI.Hierarchy.ProtocolRAMPackedFinal
import OAI.Hierarchy.ProtocolRAMAnchoredRows

namespace OAI
/-! # The fixed CPU and observed two output boards of one paid report format -/
noncomputable section
namespace Hierarchy.ProtocolRAMFrozenWindow
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat Routing CallPool RAM RAM.DescriptorExpr PhysicalProcedure
open ProtocolRAM ProtocolRAMReportedPorts TaggedShorterGroups TaggedShorterEmitMachine TaggedShorterReportedPublish
open TaggedShorterReportAdvice ProtocolRAMTranslatedKey ProtocolRAMPackedRanked
open scoped Fin.CommRing Classical

structure Format where
  N : ℕ
  groups : ℕ
  D : ℕ
  B : ℕ
  M : ℕ
  n : ℕ
  w : ℕ
  menu : ℕ
  cap : ℕ
  γ : ℕ
  gb : ℕ
  rom : ℕ
  bits : ℕ

structure Inputs where
  owner : Expr
  directory : Bank
  offset : Bank
  left : Bank
  right : Bank
  width : Bank
  bias : Bank
  classes : Bank
  weights : Bank
  origins : Bank

def Format.window (f : Format) : Size :=
  ⟨f.N,2^f.gb*(f.menu+1),f.groups,f.D,capacity (Fin f.groups) f.D f.B f.M,f.cap⟩

def Format.tables (f : Format) (r : ℕ) (a : Inputs) : Tables :=
  let s := f.window
  TaggedShorterReportAdvice.tables f.rom f.bits a.width (s.rank r).group (s.rank r).rank (s.anchor r 1) (s.anchor r 3)

def Format.anchorPhase (f : Format) (W r : ℕ) (a : Inputs) :=
  let s := f.window
  ProtocolRAMPackedAnchorPair.program W f.N (s.anchor r 0).base (s.anchor r 1).base (s.anchor r 2).base
    (s.anchor r 3).base a.directory a.offset a.left a.right a.owner

def Format.rankPhase (f : Format) (W r : ℕ) (a : Inputs) :=
  let s := f.window
  ProtocolRAMPackedRanked.program (s.rank r) W f.N s.bins a.width (s.anchor r 2) a.bias a.classes a.weights

def Format.phase (f : Format) (W r : ℕ) (a : Inputs) :=
  let s := f.window
  let A := f.tables r a
  let tape := f.N*f.cap
  (f.anchorPhase W r a).seq ((f.rankPhase W r a).seq
    ((clearedProcedure W (s.base r) s.maskWords (s.src r) tape f.γ r A).seq
      (TaggedShorterSlotWidth.procedure W (s.widthBase r) f.groups f.D (s.widthSrc r) tape f.γ (r+1) A a.origins)))

def Format.clock (f : Format) (r : ℕ) (a : Inputs) :=
  let s := f.window
  let one := ProtocolRAMSupergroupPorts.work f.N a.owner
  let rank := ProtocolRAMPackedRanked.clock (s.rank r) f.N s.bins a.width (s.anchor r 2) a.bias a.classes a.weights
  (one+one)+(rank+(((4+6*s.maskWords)+(8+16230*(f.N*f.cap)))+((4+6*s.widthWords)+(8+4130*(f.N*f.cap)))))

def Format.rows {W : ℕ} (f : Format) (a : Inputs) (m : Memory W) (old : Fin f.N→ProtocolRAMEmit.Row) :=
  ProtocolRAMPackedPlacement.translated old (fun i=>(a.directory.read m (a.owner.eval m (i.val:Word W))).val)

def Format.starts {W : ℕ} (f : Format) (a : Inputs) (m : Memory W) (side : Bool) (i : Fin f.N) : ℕ :=
  (a.offset.read m (a.owner.eval m (i.val:Word W))+(if side then a.right else a.left).read m (i.val:Word W)).val

/-- The only dynamic values supplied to the format are the already-authenticated
input rows, paid widths and the directory; the four fresh pages are written by the native pair. -/
structure Format.Ready (f : Format) (W r : ℕ) (a : Inputs) : Prop where
  room : f.window.stop r<2^W
  owner : a.owner.Fits W r
  inputs : ∀b∈[a.directory,a.offset,a.left,a.right,a.width,a.bias,a.classes,a.weights,a.origins],b.Fits W r
  publicROM : ∀j : Fin 13,(bank f.rom f.bits j).Fits W r

theorem Format.anchors (f : Format) (W r : ℕ) (a : Inputs) (ready : f.Ready W r a) (m : Memory W)
    (old : Fin f.N→ProtocolRAMEmit.Row) :
    let s := f.window
    let one := ProtocolRAMSupergroupPorts.work f.N a.owner
    ∃ out,(f.anchorPhase W r a).Exec m out (one+one) ∧
      (∀i : Fin f.N,(s.anchor r 2).read out (i.val:Word W)=((f.rows a m old i).group:Word W)) ∧
      (∀(b : Bool)(i : Fin f.N),(s.anchor r (if b then 3 else 1)).read out (i.val:Word W)=
        (f.starts a m b i:Word W)) ∧
      ∀t,t<r → out t=m t := by
  intro s one
  have starts:=s.anchor_sep r
  have space:=ready.room
  have done:=(s.start_base r).trans (s.base_stop r)
  have first : r≤(s.anchor r 0).base := by change r≤r+2+0*s.page;omega
  have low (b : Bank) (h : b.Fits W r) : b.Fits W (s.anchor r 0).base := ⟨h.1,h.2.1,h.2.2.trans first⟩
  obtain ⟨endMem,exec,read,below⟩ := ProtocolRAMPackedAnchorPair.run (s.anchor r 0).base (s.anchor r 1).base
    (s.anchor r 2).base (s.anchor r 3).base a.directory a.offset a.left a.right a.owner m
    (ProtocolRAMGeneratedWrite.fits_mono _ first ready.owner) (low _ (ready.inputs _ (by simp)))
    (low _ (ready.inputs _ (by simp))) (low _ (ready.inputs _ (by simp))) (low _ (ready.inputs _ (by simp)))
    starts.1 starts.2.1 starts.2.2.1 (starts.2.2.2.trans_lt (done.trans_lt space))
  have readPage (j : Fin 4) (i : Fin f.N) : (s.anchor r j).read endMem (i.val:Word W)=endMem ((s.anchor r j).base+i.val) := by
    have cap : f.N≤ s.page := group_capacity f.N
    have wFit := (s.anchor_fits r W ready.room j).2.1
    change endMem ((s.anchor r j).base+(i.val:Word W).val%s.page)=_
    rw [Fin.val_cast_of_lt (i.isLt.trans (cap.trans_lt wFit)),Nat.mod_eq_of_lt (i.isLt.trans_le cap)]
  refine ⟨endMem,exec,?_,?_,fun t ht=>below t (ht.trans_le first)⟩
  · intro i
    exact (readPage 2 i).trans ((read i).1.trans (Fin.cast_val_eq_self _).symm)
  · intro b i
    cases b
    · exact (readPage 1 i).trans ((read i).2.1.trans (Fin.cast_val_eq_self _).symm)
    · exact (readPage 3 i).trans ((read i).2.2.trans (Fin.cast_val_eq_self _).symm)

end Hierarchy.ProtocolRAMFrozenWindow

end
end OAI
