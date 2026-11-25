import OAI.Hierarchy.DescentTerminalPlacedHeaderColumns
import OAI.Hierarchy.DescentTerminalNativeHeaderField
import OAI.Hierarchy.DescentTerminalChipBootWords
import OAI.Hierarchy.DescentTerminalEmittedChip

namespace OAI
/-! # Both dated header scatters in one terminal chip -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan.HeaderColumns
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentTerminalEmitter DescentTerminalRowArena
open DescentTerminalPaidHeaderEvents DescentTerminalHeaderDraft DescentTerminalChipBootWords
open DescentTerminalChipRuntime DescentTerminalChipPins DescentTerminalChipSource DescentTerminalBinReaddress
open DescentTerminalDenseWindow DescentTerminalScalarPadded DescentTerminalRecipeRows DescentTerminalGraphPositions
open DescentKernelHistory DescentTerminalCableOrder DescentTerminalDenseGraphRead Computability.BorderVNP.Crossing
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false

private def align {α : Type} {w n : ℕ} (s : Fixed) (O : Output) (inside outside dest : Bank)
    (src shift blank : ℕ) (m : Memory w) (chart : α ↪ Fin n) (word : α → Computability.VPVNP.BurstRAM.Word w)
    (h : Header) (same : h=DescentTerminalHeaderDraft.header n s O inside outside dest src shift blank)
    (size : n=h.count) (emitted : Header.Emits
      (DescentTerminalHeaderDraft.header n s O inside outside dest src shift blank) m chart word) :
    Header.Emits h m (chart.trans (finCongr size).toEmbedding) word := by
  subst h
  have idChart : chart.trans (finCongr size).toEmbedding=chart := by ext x; rfl
  rw [idChart]
  exact emitted

variable {P Tag : Type} [Fintype P] {D H K W q piece bitsW : ℕ} {bits : P→ℕ}
  (cfg : DescentTerminalCompiledPrefix.Shape) (I : Input) (base : ℕ) (N : Network D P bits)
  (home : N.Site→Fin H) (native : N.Edge ↪ Fin (Fintype.card N.Edge))
  (ext : P ↪ ℕ) (nodes : N.Site ↪ ℕ) (ops : ∀v,Boundary N v ↪ ℕ)
local notation "p_" => W*piece
variable (r : ∀v,Recipe Tag (DescentTerminalBundleRows.SiteRef (p:=W*piece) N v)) (hp : 0<W*piece)
  (birth : ∀v,(r v).Node ↪ ℕ) (wp : 0<W) (qp : 0<q)
local notation "groups_" => DescentTerminalBundleRows.site (order N home native p_ ext nodes ops) r hp birth
variable (bins : Bins (W:=W) (q:=q)
  (DescentTerminalBundleRows.site (DescentTerminalCableOrder.order N home native (W*piece) ext nodes ops) r hp birth) ≤ K)
local notation "rowMap" => DescentTerminalScatterColumns.fixed groups_ wp bins
local notation "E_" => emitter cfg I base
variable (s : Fixed) (O : Output) (codes front empty : ℕ) (m : Memory bitsW)
local notation "b_" => chipBanks (K:=K) (W:=W) (q:=q) (p:=piece) codes E_ front empty
local notation "cable" => (bodyPlane cfg I base).header
local notation "exterior" => publicHeader cfg I base
local notation "draft" => fixed s cfg I base

/-- Consume the native index issuer after the two width scans and the native format
issuer after the index pass. The output banks here are the ones read by the chip. -/
def ports (prior : Uses s O I.sources) (ni : I.indexEvents=cfg.terminal.rows)
    (nf : I.formatEvents=cfg.terminal.rows) (rows : cfg.terminal.rows=K*W)
    (blank : I.blank=(formatIndex q p_ (DescentTerminalScalarPadded.blank q p_)).val)
    (nativeFields : ∀ mode : Bool,
      let h := if mode then (E_).formats else (E_).indices
      Header.Emits (DescentTerminalHeaderDraft.header (K*W) draft O
        (DescentTerminalHeaderDraft.fieldBank cable mode) (DescentTerminalHeaderDraft.fieldBank exterior mode)
        h.output h.src (if mode then 0 else cfg.terminal.plane.rawRows+2) (if mode then I.blank else 0))
        (if mode then indexed cfg.terminal E_ m else external cfg.terminal E_ m) rowMap
        (DescentTerminalHeaderDraft.fieldWord (rawRows:=cfg.terminal.plane.rawRows)
          N home native ext nodes ops r hp birth qp mode)) :
    ControlColumns cfg.terminal E_ m N home native ext nodes ops r hp birth wp qp bins b_ := by
  refine ⟨rows.symm,rows.symm,rfl,blank,rfl,rfl,?_,?_,?_,?_⟩
  · refine align _ _ _ _ _ _ _ _ _ _ _ _ ?_ rows.symm (nativeFields false)
    simpa only [←rows, DescentTerminalHeaderDraft.fieldBank, Bool.false_eq_true, ite_false, ite_true]
      using issuer s O cfg I base prior ni nf false
  · refine align _ _ _ _ _ _ _ _ _ _ _ _ ?_ rows.symm (nativeFields true)
    simpa only [←rows, DescentTerminalHeaderDraft.fieldBank, Bool.false_eq_true, ite_false, ite_true]
      using issuer s O cfg I base prior ni nf true
  · intro i
    exact Allocation.indices_live cfg.terminal I.indexEvents I.formatEvents _ (inputs cfg I base)
      (bodyPlane cfg I base) (publicHeader cfg I base) I.blank (i.cast rows.symm)
  · intro i
    exact Allocation.formats_live cfg.terminal I.indexEvents I.formatEvents _ (inputs cfg I base)
      (bodyPlane cfg I base) (publicHeader cfg I base) I.blank (i.cast rows.symm)

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan.HeaderColumns

end OAI
