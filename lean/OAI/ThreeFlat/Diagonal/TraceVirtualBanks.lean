import OAI.ThreeFlat.Diagonal.TraceSeedCapacity
import OAI.ThreeFlat.RAM.TraceRawOverlay
import OAI.ThreeFlat.RAM.HistoryInitialTraceFrame

namespace OAI
/-! # Only the small physically mounted banks are needed by the logical H trace -/
namespace ThreeFlat.Diagonal.TraceBitHeader
open Computability.VPVNP.BurstRAM RAM RAM.TraceBucketAtom LaneCursor LaneCursor.RowLayout RAM.HistoryInitialSeed
open scoped Fin.CommRing
variable {F : Type*} [Fintype F] [Field F] {w W b p S f q low : ℕ}
variable (hF : Fintype.card F ≤ 2^w) (hw : 3≤w+1) (hp : p≤2^(w+1))
    (base : ℕ) (st : Word w) (hs : S≤2^w) (hf : f≤2^(w+1)) (r k : ℕ)
    (fit : S+f≤2^(1+((q+1)+low))) (copies raw dict masks ids : ℕ)
set_option quotPrecheck false
local notation "d" => (q+1)+low
local notation "G" => TraceStaticRow.gateTable hF hw hp base f st r k d
local notation "N" => network hF hw hp base st hs hf r k d
local notation "B" => bucketShape (q:=q) (low:=low) (S:=S) (f:=f) hF hw hp base st r k copies raw dict masks ids
local notation "P" => layout hF hw hp base st hs hf r k fit
local notation "banks" => Banks hF hw hp base st hs hf r k fit ids masks dict
local notation "view" => TraceRawOverlay.memory N

/-- All real addresses that accompany the logical raw interval are outside it.
This is static placement of the small literal and input banks. -/
structure Visible (raw cells ids slots dict rows masks offsets : ℕ) (im : RAM.PhysicalPrelude.Image F w)
    (loc : TraceSuffixOracle.Locations) : Prop where
  constants : 2≤raw
  ids : ids+slots≤raw ∨ raw+11*cells≤ ids
  dictionary : dict+rows≤raw ∨ raw+11*cells≤dict
  masks : masks+offsets≤raw ∨ raw+11*cells≤ masks
  description : loc.description+im.advice≤raw ∨ raw+11*cells≤loc.description
  parameters : loc.parameters+im.parameters≤raw ∨ raw+11*cells≤loc.parameters
  table : loc.table+w*FixedTraceImage.count im.G≤raw ∨ raw+11*cells≤loc.table

theorem Visible.banks {im : RAM.PhysicalPrelude.Image F w} {loc : TraceSuffixOracle.Locations}
    (h : Visible raw (N).cells ids (G).cells dict (2^(q+1)*2^low) masks (1+(d+d)) im loc)
    (code : FieldCode F W) (m : Memory W) (saved : banks m) : banks (view code raw m) := by
  refine ⟨fun j=>?_,fun a=>?_,fun i=>?_⟩
  · rw [TraceRawOverlay.span N code raw m h.ids j.isLt];exact saved.1 j
  · rw [TraceRawOverlay.span N code raw m h.dictionary ((P).offset ((P).code a)).isLt];exact saved.2.1 a
  · rw [TraceRawOverlay.span N code raw m h.masks i.isLt];exact saved.2.2 i

theorem Visible.mounted {im : RAM.PhysicalPrelude.Image F w} {loc : TraceSuffixOracle.Locations}
    {slots rows offsets cells : ℕ} {D : Fin im.advice→Bool} {par : Fin im.parameters→Bool}
    (h : Visible raw cells ids slots dict rows masks offsets im loc)
    {pins : ℕ} (M : BitNetwork F pins) (hc : M.cells=cells) (code : FieldCode F W) (m : Memory W)
    (saved : TraceSuffixOracle.Mounted im loc (fun i=>(m i).val) D par) :
    TraceSuffixOracle.Mounted im loc (fun i=>(TraceRawOverlay.memory M code raw m i).val) D par := by
  subst cells
  exact ⟨fun i=>(congrArg Fin.val (TraceRawOverlay.span M code raw m h.description i.isLt)).trans (saved.description i),
    fun i=>(congrArg Fin.val (TraceRawOverlay.span M code raw m h.parameters i.isLt)).trans (saved.parameters i),
    fun i=>(congrArg Fin.val (TraceRawOverlay.span M code raw m h.table i.isLt)).trans (saved.table i)⟩

/-- The capacity proof is purely numerical apart from the short physical seed banks.
All long raw columns are supplied by the logical read-only view. -/
theorem virtual_capacity (field : Fintype.card F≤2^W) (m : Memory W)
    (room : SeedRoom (G).cells (1+(d+d)) (2^(q+1)*2^low) ids masks dict W)
    (size : (B).footprint<2^b) (words : 5*b+128≤W)
    (endRaw : raw+11*((B).shape.rows*(G).cells)+4≤2^W) (coeff : Fintype.card F≤2+S+(B).shape.count)
    (saved : banks m) {im : RAM.PhysicalPrelude.Image F w} {loc : TraceSuffixOracle.Locations}
    (visible : Visible raw (N).cells ids (G).cells dict (2^(q+1)*2^low) masks (1+(d+d)) im loc) :
    ImageCapacity B (view (FieldCode.ofCardLe field) raw m) b :=
  seeded_capacity hF hw hp base st hs hf r k fit copies raw dict masks ids field _ room size words endRaw coeff
    (Visible.banks hF hw hp base st hs hf r k fit raw dict masks ids visible _ m saved)
    (TraceRawOverlay.loaded N _ raw m)


end ThreeFlat.Diagonal.TraceBitHeader

end OAI
