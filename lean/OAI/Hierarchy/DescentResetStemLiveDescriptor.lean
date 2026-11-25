import OAI.Hierarchy.DescentResetStemReindexed
import OAI.Hierarchy.DescentResetStemIncidence

namespace OAI
/-! # One native execution from physical host IDs and old signed fields to issued stem metadata -/
namespace Hierarchy.DescentResetStemPackedIssue.Mixed
open DescentSIMDLookup DescentPackedZip DescentDyadicSpan DescentResetStemIncidence
open DescentResetFieldAssembler DescentSixParty.ClosedReset
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {D f b K P H G M Q pitch w : ℕ}

def polarity (K : ℕ) (j : Fin (2*K)) : Bool := finTwoEquiv (finProdFinEquiv.symm j : Fin 2×Fin K).1

@[simp] theorem polarity_headIndex (s : Bool) (j : Fin K) : polarity K (headIndex s j)=s := by
  simp [polarity,headIndex]

def metaAt (scene : Scene (2*K) H pitch) (s : Bool) (j : Fin K) (h : Fin H) :=
  Window.stemWord (scene.here h).val (scene.neighbors (scene.here h)) s
    (scene.oldHub (headIndex s j) h) ((scene.ends (headIndex s j) h).map (fun ab=>(ab.1.val,ab.2.val)))

namespace Layout
variable (A : Layout) (parse : DescentResetStemKey.Decoder D f) (side : Fin Q→Bool) (src : Fin Q→Fin (D+2)→Expr)
variable (ports : DescentResetStemIncidence.Ports (2*K))

def native (b location M P H G w : ℕ) :=
  (DescentResetStemDescriptorRAM.code (ports.inputs (polarity K)) b w H location A.raw).seq
    (A.code parse side src (b*7) K M P H G w)

def budget (b location M P H G w : ℕ) :=
  DescentResetStemDescriptorRAM.ticks (ports.inputs (polarity K)) H location A.raw+
    A.ticks parse side src (b*7) K M P H G w

def result (b location M P H G : ℕ) (m : Memory w) :=
  A.output parse side src (b*7) K M P H G (DescentResetStemDescriptorRAM.output
    (ports.inputs (polarity K)) b H location A.raw m)

theorem native_run (b location : ℕ) (m : Memory w) (scene : Scene (2*K) H pitch) (origin : Reads ports scene m)
    (interfaceFits : ports.All (Expr.Fits w location)) (hostRoom : pitch<2^w)
    (dead : parse 0=none) (x : Fin Q→Fin P→Fin G→Fin (D+2)→Cell f) (owner : Fin H→Fin P)
    (inputs : ∀q i,(src q i).Fits w location)
    (reads : ∀q i,Source (src q i) (fun h g=>x q h g i) M m)
    (directory : DescentResetStemKeyReindex.Directory A.pointer owner m)
    (ptrRoom : A.pointer+span H≤ location) (literalRoom : location+56≤A.raw)
    (early : A.raw+(2*K)*H+span H≤A.base) (wide : (b*7)*M≤ w)
    (room : A.stop D f (b*7) K M P H G Q<2^w) :
    let last:=A.result parse side src ports b location M P H G m
    (A.native parse side src ports b location M P H G w).Exec m last (A.budget parse side src ports b location M P H G w) ∧
    (∀q (p : Row H G M),last (A.out D f (b*7) K M P H G Q+q.val*(H*chunks G M)+(row H G M p).val)=
      ((data (fun h g=>DescentResetStemMux.pick (DescentResetStemKey.word parse (side q) (x q (owner h) g))
        (fun j=>DescentResetFieldAssembler.raw b (metaAt scene (side q) j h))) p).val:Word w)) ∧
    (∀u,u< location ∨ A.stop D f (b*7) K M P H G Q≤ u→last u=m u) ∧ CheapCode (A.native parse side src ports b location M P H G w) := by
  let stage:=DescentResetStemDescriptorRAM.output (ports.inputs (polarity K)) b H location A.raw m
  have rb : A.base≤A.stop D f (b*7) K M P H G Q := by
    unfold stop out mux hdr mapping DescentResetStemKey.Columns.stop DescentResetStemKey.Columns.start
      DescentResetStemHeaders.outputBase
    omega
  have rawRoom : A.raw+(2*K)*H<2^w := (Nat.le_add_right _ (span H)).trans_lt (early.trans_lt (rb.trans_lt room))
  have fixed:=ports.publish scene (polarity K) b location A.raw m origin interfaceFits hostRoom literalRoom rawRoom
  have start : location≤A.base:=by omega
  have original (u : ℕ) (lo : u< location) : stage u=m u :=
    fixed.2.2.1 u (.inl lo) (.inl (by omega))
  have keep (q i) : Source (src q i) (fun h g=>x q h g i) M stage := by
    intro p
    exact (eval_below _ _ m stage (inputs q i) original).trans (reads q i p)
  have ptr : DescentResetStemKeyReindex.Directory A.pointer owner stage := by
    intro h
    have small:=h.isLt.trans_le (span_ge H)
    exact (original _ (by omega)).trans (directory h)
  have finished:= A.run parse side src stage dead x owner _
    (fun q i=>ProtocolRAMGeneratedWrite.fits_mono _ start (inputs q i)) keep ptr fixed.2.1
    (ptrRoom.trans start) early wide room
  refine ⟨?_,?_,?_,cheap_seq fixed.2.2.2 finished.2.2.2⟩
  · intro nPC nReg nPub machine pc reg slots exit rom advice cfg rawMem enter same
    exact Procedure.Exec.then fixed.1 finished.1 machine pc reg slots exit rom advice cfg rawMem enter same
  · intro q p
    change A.output parse side src (b*7) K M P H G stage _ = _
    rw [finished.2.1 q p]
    simp only [metaAt,polarity_headIndex]
  · intro u hu
    rcases hu with lo|hi
    · exact (finished.2.2.1 u (.inl (lo.trans_le start))).trans (original u lo)
    · exact (finished.2.2.1 u (.inr hi)).trans
        (fixed.2.2.1 u (.inr (by omega)) (.inr (by omega)))

end Layout
end
end Hierarchy.DescentResetStemPackedIssue.Mixed

end OAI
