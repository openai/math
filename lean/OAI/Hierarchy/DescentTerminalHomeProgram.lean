import OAI.Hierarchy.DescentTerminalHomeFormat
import OAI.Hierarchy.DescentTerminalMeterSuffix
import OAI.Hierarchy.DescentTerminalHomeAny

namespace OAI
/-! # A fixed terminal program sharing the native per-home measurement and local scalar records -/

namespace Hierarchy.DescentTerminalCompiledPrefix.Home
open DescentTerminalVertexFields Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open PhysicalProcedure ProtocolRAM
noncomputable section

variable {blocks bw : ℕ} (V : Format) (S : Shape) (L : Layout)
  (C : PrivateCounter.Banks (blocks:=blocks)) (O : DescentPrivateExponentRAM.Banks)
set_option quotPrecheck false
local notation "capacity" => cohortSize (q:=V.publicArity) (t:=V.roles) (H:=V.privateWords)
  (N:=V.nodes) (A:=V.addresses) (w:=V.piece) (groups:=V.groups) (blocks:=blocks)
local notation "counter" => PrivateCounter.machine (q:=V.publicArity) (t:=V.roles) (H:=V.privateWords)
  (N:=V.nodes) (A:=V.addresses) (p:=V.piece) (groups:=V.groups) (homes:=S.sites) (bw:=bw) C O
local notation "raw" => PrivateCounter.rawFinal (q:=V.publicArity) (t:=V.roles) (H:=V.privateWords)
  (N:=V.nodes) (A:=V.addresses) (p:=V.piece) (groups:=V.groups) (homes:=S.sites) C O
local notation "true_" => PrivateCounter.final (q:=V.publicArity) (t:=V.roles) (H:=V.privateWords)
  (N:=V.nodes) (A:=V.addresses) (p:=V.piece) (groups:=V.groups) (homes:=S.sites) C O

def program := (counter).seq (Suffix.program (w:=bw) S L C.layout)
def measured (m : Memory bw) := raw m
def result (m : Memory bw) := Suffix.output S L C.layout (raw m)
def time := DescentCompiler.TerminalScale.privateHomeClock capacity S.sites blocks V.piece+
  Suffix.time S L blocks

structure Fits (bw : ℕ) : Prop where
  home : PrivateCounter.Room (q:=V.publicArity) (t:=V.roles) (H:=V.privateWords) (N:=V.nodes)
    (A:=V.addresses) (p:=V.piece) (groups:=V.groups) C bw
  endHome : C.base+capacity+S.sites+S.sites+1<2^bw
  scalar : O.Room bw
  suffix : Suffix.Fits S L C.layout bw

theorem run (m : Memory bw) (ok : Fits V S L C O bw) (positive : 0<bw)
    (plan : L.row.mark.Fixed S.sites (DescentTerminalRowPlan.header L.row S.sites (raw m)))
    (emitter : DescentTerminalEmitter.Static S.terminal L.emit (Suffix.events S L C.layout (raw m))) :
    (program (bw:=bw) V S L C O).Exec m (result V S L C O m) (time V S L (blocks:=blocks)) ∧
      CheapCode (program (bw:=bw) V S L C O) := by
  obtain ⟨countExec, countCheap⟩ := PrivateCounter.any_raw (q:=V.publicArity) (t:=V.roles) (H:=V.privateWords)
    (N:=V.nodes) (A:=V.addresses) (p:=V.piece) (groups:=V.groups) (homes:=S.sites)
    C O m ok.home ok.endHome ok.scalar
  obtain ⟨suffixExec, suffixCheap⟩ := Suffix.run S L C.layout (raw m) ok.suffix positive plan emitter
  exact ⟨@Procedure.Exec.then bw (counter) (Suffix.program (w:=bw) S L C.layout)
      m (raw m) (result V S L C O m) (DescentCompiler.TerminalScale.privateHomeClock capacity S.sites blocks V.piece)
      (Suffix.time S L blocks) (@countExec) (@suffixExec),
    @cheap_seq bw (counter) (Suffix.program (w:=bw) S L C.layout) (@countCheap) (@suffixCheap)⟩

/-- The count observed by the common scalar gate is the digit from exactly
the home counter that processed the same packed tape as the later scalar rows. -/
theorem count (m : Memory bw) (ok : Fits V S L C O bw)
    (shifts : PrivateCounter.Shift (q:=V.publicArity) (t:=V.roles) (H:=V.privateWords) (N:=V.nodes)
      (A:=V.addresses) (p:=V.piece) (groups:=V.groups) C.layout m)
    (address : O.usedWords=C.base+capacity+S.sites+S.sites)
    (frozen : Frozen L O.deadBits) (slots : O.deadBits<slotBase S L) (pages : O.deadBits<L.directory.texture.base)
    (lo : DescentTerminalEmitter.BeforeKey S.terminal L.emit O.deadBits)
    (hi : DescentTerminalEmitter.AfterFlights S.terminal L.emit O.deadBits) :
    result V S L C O m O.deadBits=true_ m O.deadBits := by
  rw [result,Suffix.saved S L C.layout (raw m) ok.suffix frozen slots pages lo hi,
    PrivateCounter.raw_eq_final (q:=V.publicArity) (t:=V.roles) (H:=V.privateWords)
      (N:=V.nodes) (A:=V.addresses) (p:=V.piece) (groups:=V.groups) (homes:=S.sites)
      C O m ok.home ok.endHome ok.scalar shifts address]

end
end Hierarchy.DescentTerminalCompiledPrefix.Home

end OAI
