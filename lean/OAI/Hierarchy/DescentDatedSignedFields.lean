import OAI.Hierarchy.DescentResetFieldReturn
import OAI.Hierarchy.DescentResetDatedControls

namespace OAI
/-! # The measured reset permutes the individual old signed-port words

The selected row-functional matrix is read from its saved physical word. The
input channels are the previous separate signed slots, including empty slots.
The aggregate pair counts used to select the reset are separate data.
-/
namespace Hierarchy.DescentGLPacked.BankImage.SignedFields
open DescentGLPacked DescentGL DescentColonies DescentGLNielsen DescentSIMDLookup
open DescentGLControlCode DescentPackedColony.Phase.Arena
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section

variable {D H h l b w : ℕ}

def controlBanks (origin d : ℕ) : Tables :=
  ⟨⟨origin,Nat.clog 2 (Count d)⟩,⟨origin+Count d,Nat.clog 2 (Count d*2^(d*d))⟩⟩

def controlEnd (origin d : ℕ) := origin+Count d+Count d*2^(d*d)

def controlSheet (origin d w : ℕ) : Image w :=
  ⟨origin,controlEnd origin d,mount (controlBanks origin d) (chosenName d) (fun _=>0)⟩

theorem control_read (origin d : ℕ) (mem : Memory w)
    (reads : (controlSheet origin d w).Resident mem) :
    installed (controlBanks origin d) (chosenName d) mem := by
  let B:=controlBanks origin d
  have actual:=mounted B (chosenName d) ((fun _=>0) : Memory w) (by exact le_rfl)
  constructor
  · intro i
    have hi:=i.isLt
    apply (reads (B.offsets.base+i.val) (by simp [B,controlBanks,controlSheet]) (by
      change origin+i.val<origin+Count d+Count d*2^(d*d)
      omega)).trans (actual.1 i)
  · intro j
    have hi:=j.isLt
    apply (reads (B.switches.base+j.val) (by dsimp [B,controlBanks,controlSheet];omega) (by
      change origin+Count d+j.val<origin+Count d+Count d*2^(d*d)
      omega)).trans (actual.2 j)

def endAddress (C : Chart) (d : ℕ) := C.heap d+(schedule d).length*C.page

def program (origin : ℕ) (C : Chart) (saved : Bank) (field : ℕ→Expr) (D H h l b w : ℕ) :=
  let d:=h+l
  let n:=(schedule d).length
  let rows:=H*2^h
  let gs:=DescentPackedFlowBatch.passes C.input.base rows rows field 0 D
  let ps:=steps (C.chosen d) (D*H) (2^h) 0 n
  let key:=Expr.lookup saved (.lit 0)
  let remap:=(ProtocolRAM.program w gs).seq
    ((scan w C.flags n ((controlBanks origin d).expr key)).seq (ProtocolRAM.program w ps))
  (((controlSheet origin d w).program).seq (Dated.routes C (D*H) h l b w).program).seq remap

def duration (origin : ℕ) (C : Chart) (saved : Bank) (field : ℕ→Expr) (D H h l b w : ℕ) :=
  let d:=h+l
  let n:=(schedule d).length
  let rows:=H*2^h
  let gs:=DescentPackedFlowBatch.passes C.input.base rows rows field 0 D
  let ps:=steps (C.chosen d) (D*H) (2^h) 0 n
  (8+10*((controlSheet origin d w).length+(Dated.routes C (D*H) h l b w).length))+
    (clock gs+((4+n*(2*((controlBanks origin d).expr (.lookup saved (.lit 0))).work+4))+clock ps))

theorem issue (origin : ℕ) (C : Chart) (saved : Bank) (field : ℕ→Expr)
    (μ : DescentGL.Layout (h+l)) (X : Fin D→Fin H→Block (h+l)→Cell b)
    (mem : Memory w) (valid : Size C (D*H) h l b w)
    (keyFits : saved.Fits w origin)
    (measured : mem saved.base=((DescentExterior.matrixCode μ).val:Word w))
    (sourceFits : ∀j<D,(field j).Fits w origin)
    (source : ∀j,DescentPackedZip.Source (field j.val) (X j) (2^l) mem)
    (space : controlEnd origin (h+l)≤C.input.base)
    (offsetFits : (controlBanks origin (h+l)).offsets.Fits w C.input.base)
    (switchFits : (controlBanks origin (h+l)).switches.Fits w C.input.base)
    (gap : C.input.base+C.input.size≤C.flags) :
    ∃dst,(program origin C saved field D H h l b w).Exec mem dst
        (duration origin C saved field D H h l b w) ∧
      CheapCode (program origin C saved field D H h l b w) ∧
      (∀j,Dense (h:=h) (l:=l) (slice (((C.chosen (h+l)).bank (schedule (h+l)).length).base) H (2^h) j)
        (fun v z=>X j v ((rearrange μ).symm z)) dst) ∧
      ∀a,a<origin ∨ endAddress C (h+l)≤a→dst a=mem a := by
  let d:=h+l
  let I:=controlSheet origin d w
  let J:=Dated.routes C (D*H) h l b w
  let B:=controlBanks origin d
  let key:=Expr.lookup saved (.lit 0)
  let mid:=J.output (I.output mem)
  have start : origin≤C.input.base := (show origin≤controlEnd origin d by
    dsimp [controlEnd];omega).trans space
  have afterInput : C.input.base≤C.start := by have:=valid.input.2.2;omega
  have endStart : C.start≤C.heap (h+l):=Nat.le_add_right ..
  have top:=valid.top
  have lowI : I.low+I.length<2^w := by
    change origin+(controlEnd origin (h+l)-origin)<2^w
    omega
  have lowJ : J.low+J.length<2^w := by
    change C.start+(C.heap (h+l)-C.start)<2^w
    omega
  obtain ⟨stamped,controls,geometry,frame,cheap,_⟩:=I.pair J mem
    (Or.inl (space.trans afterInput)) lowI lowJ
  have before (z : ℕ) (hz : z<origin) : mid z=mem z :=
    frame z (.inl hz) (.inl (hz.trans_le (start.trans afterInput)))
  have narrow : saved.Fits w C.input.base :=
    ⟨keyFits.1,keyFits.2.1,keyFits.2.2.trans start⟩
  obtain ⟨keyFits',words,selected⟩:=from_code B saved C.input.base narrow μ mid
    ((before saved.base (by have pos : 0<saved.size:=Nat.two_pow_pos _;have:=keyFits.2.2;omega)).trans measured)
    (control_read origin d mid controls)
  have shifted (j : Fin D) : DescentPackedZip.Source (field j.val) (X j) (2^l) mid := by
    intro p
    exact (ProtocolRAM.eval_below _ _ mem mid (sourceFits _ j.isLt) before).trans (source j p)
  obtain ⟨dst,ran,hardware,outputs,outer⟩:=gather_and_reset C valid B (chosenName d) key μ X field mid
    (fun j hj=>ProtocolRAMGeneratedWrite.fits_mono _ start (sourceFits j hj))
    ⟨keyFits',offsetFits,switchFits⟩ (Nat.le_pow_clog (by decide) _)
    (Nat.le_pow_clog (by decide) _) words selected shifted gap (Dated.route_reads C mid geometry)
  refine ⟨dst,stamped.then ran,cheap_seq cheap hardware,outputs,?_⟩
  intro a bounds
  rcases bounds with lo|hi
  · exact (outer a (.inl (lo.trans_le start))).trans (before a lo)
  · have stop : C.heap d≤a:= (Nat.le_add_right ..).trans hi
    exact (outer a (.inr hi)).trans (frame a (.inr (space.trans (afterInput.trans (endStart.trans stop)))) (.inr stop))

end
end Hierarchy.DescentGLPacked.BankImage.SignedFields

end OAI
