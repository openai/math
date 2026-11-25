import OAI.Hierarchy.DescentTerminalPreflightChipInput

namespace OAI
/-! # The native chronological bridge from site acquisition to chip startup -/
namespace Hierarchy.DescentTerminalPreflightSpace.Spec
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open ProtocolRAM DescentTerminalHeaderDraft DescentTerminalCompiledPrefix.AddressPlan.HeaderColumns
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable (x : Spec) (begin_ q grain : ℕ) (peer : Bank) (old : Fin x.scalar.blocks→Fin (2*x.cap)→Bank)
    (total modulo homes : Bank) (boundary : ℕ)
local notation "P_" => x.cables begin_ peer old
local notation "U_" => x.publicWidths begin_
local notation "A_" => x.draft begin_ total modulo homes boundary
local notation "L_" => x.eventInputs begin_ peer old
local notation "lit_" => x.literalBase begin_

def afterWidths {w : ℕ} (m : Memory w) := (U_).lastMem q grain ((P_).final q grain m)

def afterSiteControls {w : ℕ} (m : Memory w) :=
  data A_ L_ x.degree (litMem lit_ x.paidRows (x.afterWidths begin_ q grain peer old m))

def afterSiteProgram (w : ℕ) :=
  (((P_).program w q grain).seq ((U_).program w q grain)).seq
    ((litProc w lit_ x.paidRows).seq (machine A_ L_ x.degree w))

def afterSiteTime :=
  ((P_).time q grain + (U_).clocks q grain) +
    ((4+40*DescentTerminalHeaderDraft.span x.paidRows)+clocks A_ L_ x.degree)

local notation "out_" => x.afterSiteControls begin_ q grain peer old total modulo homes boundary
local notation "run_" => x.afterSiteProgram begin_ q grain peer old total modulo homes boundary
local notation "time_" => x.afterSiteTime begin_ q grain peer old total modulo homes boundary

/-- All four real stages occupy successive address intervals. At their common
output every previously emitted directory word is exactly its acquisition value. -/
theorem after_site_run {w : ℕ} (m : Memory w) (paid actors : Fin x.scalar.blocks→Bank)
    (boot : x.Before begin_ paid actors old peer total modulo homes boundary)
    (room : x.maskBase begin_<2^w) (positive : 0<w) :
    (run_ w).Exec m (out_ m) time_ ∧ CheapCode (run_ w) ∧
      ∀i<(x.controls begin_).finish,out_ m i=m i := by
  have cable := (P_).run q grain m (x.fits_cables begin_ room paid actors old peer total modulo homes boundary boot)
  have fit := x.after_public begin_ room
  have pubs := (U_).any q grain ((P_).final q grain m) fit.1 fit.2
  have low := (U_).before q grain ((P_).final q grain m) fit.2
  have draft := (x.fits_draft begin_ room paid actors old peer total modulo homes boundary boot).1
  have issue := preflight A_ L_ x.degree lit_ x.paidRows
    (x.afterWidths begin_ q grain peer old m) draft (le_refl _) positive
  obtain ⟨cableRun, cableCheap, _, cableKeep⟩ := cable
  obtain ⟨pubRun, pubCheap⟩ := pubs
  obtain ⟨issueRun, issueCheap, issueKeep⟩ := issue
  have price := @cheap_seq w ((P_).program w q grain) ((U_).program w q grain) (@cableCheap) (@pubCheap)
  refine ⟨Procedure.Exec.then (Procedure.Exec.then (@cableRun) (@pubRun)) (@issueRun),
    @cheap_seq w (((P_).program w q grain).seq ((U_).program w q grain))
      ((litProc w lit_ x.paidRows).seq (machine A_ L_ x.degree w)) (@price) (@issueCheap), ?_⟩
  obtain ⟨_,_,_,_,_,ctrl,pub,_,_⟩:=x.layers begin_
  intro i hi
  exact (issueKeep i (hi.trans_le (ctrl.trans pub))).trans
    ((low i (hi.trans_le ctrl)).trans (cableKeep i hi))

end
end Hierarchy.DescentTerminalPreflightSpace.Spec

end OAI
