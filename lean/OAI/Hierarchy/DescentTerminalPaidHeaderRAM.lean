import OAI.Hierarchy.DescentTerminalPaidHeaderEvents
import OAI.Hierarchy.DescentTerminalEmittedShelfReads

namespace OAI
/-! # Three paid scans issue physical live, mode and source-index words for both scatters -/
namespace Hierarchy.DescentTerminalPaidHeaderEvents
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
structure Output where
  active : Bank
  mode : Bank
  source : Bank
variable (I:Inputs) (O:Output) (H D n:ℕ)
local notation "e" c => expr I H D c
def program (w:ℕ) := ((scan w O.active.base n (e .active)).seq (scan w O.mode.base n (e .mode))).seq
  (scan w O.source.base n (e .source))
def ticks := ((4+n*(2*(e .active).work+4))+(4+n*(2*(e .mode).work+4)))+(4+n*(2*(e .source).work+4))
def afterActive {w:ℕ} (m:Memory w) := ProtocolRAM.image O.active.base n (e .active) m
def afterMode {w:ℕ} (m:Memory w) := ProtocolRAM.image O.mode.base n (e .mode) (afterActive I O H D n m)
def after {w:ℕ} (m:Memory w) := ProtocolRAM.image O.source.base n (e .source) (afterMode I O H D n m)
structure Room (w:ℕ) : Prop where
  input : ∀c:Column,(e c).Fits w O.active.base
  am : O.active.base+n≤O.mode.base
  ms : O.mode.base+n≤O.source.base
  finish : O.source.base+n<2^w

theorem tariff (w:ℕ) : DescentStaticWordColumn.names (program I O H D n w)=
    33+4*((e .active).work+(e .mode).work+(e .source).work) := by
  simp only [program,DescentStaticWordColumn.names_seq,DescentStaticWordColumn.names_scan]
  omega

private theorem grow {w a b:ℕ} (x:Expr) (f:x.Fits w a) (later:a≤b) : x.Fits w b := by
  induction x with
  | row|lit=>trivial
  | lookup bank i ih=>exact ⟨⟨f.1.1,f.1.2.1,f.1.2.2.trans later⟩,ih f.2⟩
  | op op x y ih jh=>exact ⟨ih f.1,jh f.2⟩
  | branch op x y yes no ih jh kh lh=>exact ⟨ih f.1,jh f.2.1,kh f.2.2.1,lh f.2.2.2⟩

variable {w:ℕ} (m:Memory w) (ok:Room I O H D n w)
include ok in
theorem executed : (program I O H D n w).Exec m (after I O H D n m) (ticks I H D n) ∧
    CheapCode (program I O H D n w) := by
  have am:=ok.am;have ms:=ok.ms;have fit:=ok.finish
  let activeScan := scan w O.active.base n (e .active)
  let modeScan := scan w O.mode.base n (e .mode)
  let sourceScan := scan w O.source.base n (e .source)
  have activeRun := @scan_exec w O.active.base n (e .active) m (ok.input .active) (by omega)
  have modeRun := @scan_exec w O.mode.base n (e .mode) (afterActive I O H D n m)
    (grow _ (ok.input .mode) (by omega)) (by omega)
  have sourceRun := @scan_exec w O.source.base n (e .source) (afterMode I O H D n m)
    (grow _ (ok.input .source) (by omega)) fit
  have firstTwo := @Procedure.Exec.then w activeScan modeScan m (afterActive I O H D n m)
    (afterMode I O H D n m) _ _ (@activeRun) (@modeRun)
  exact ⟨@Procedure.Exec.then w (activeScan.seq modeScan) sourceScan m (afterMode I O H D n m)
      (after I O H D n m) _ _ (@firstTwo) (@sourceRun),
    @cheap_seq w (activeScan.seq modeScan) sourceScan
      (@cheap_seq w activeScan modeScan (@scan_cheap w O.active.base n (e .active))
        (@scan_cheap w O.mode.base n (e .mode)))
      (@scan_cheap w O.source.base n (e .source))⟩

def Output.get (c:Column) : Bank := match c with | .active=>O.active | .mode=>O.mode | .source=>O.source
include ok in
theorem before (j:ℕ) (h:j<O.active.base) : after I O H D n m j=m j := by
  have am:=ok.am;have ms:=ok.ms
  exact (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl (by omega))).trans
    ((ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl (by omega))).trans
      (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl h)))

include ok in
theorem issued (i:Fin n) (c:Column) : after I O H D n m ((O.get c).base+i.val)=(e c).eval m (i.val:Word w) := by
  have am:=ok.am;have ms:=ok.ms;have h:=i.isLt
  have low₁ (j:ℕ) (hj:j<O.active.base) : afterActive I O H D n m j=m j :=
    ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl hj)
  have low₂ (j:ℕ) (hj:j<O.active.base) : afterMode I O H D n m j=m j :=
    (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl (by omega))).trans (low₁ j hj)
  cases c with
  | active=>
    exact (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl (by change O.active.base+i.val<O.source.base;omega))).trans
      ((ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl (by change O.active.base+i.val<O.mode.base;omega))).trans
        (ProtocolRAMGeneratedWrite.read_image _ n _ m i))
  | mode=>
    exact (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl (by change O.mode.base+i.val<O.source.base;omega))).trans
      ((ProtocolRAMGeneratedWrite.read_image _ n _ _ i).trans (eval_below _ _ _ _ (ok.input .mode) low₁))
  | source=>exact (ProtocolRAMGeneratedWrite.read_image _ n _ _ i).trans (eval_below _ _ _ _ (ok.input .source) low₂)

end
end Hierarchy.DescentTerminalPaidHeaderEvents

end OAI
