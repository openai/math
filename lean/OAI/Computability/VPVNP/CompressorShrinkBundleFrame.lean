import OAI.Computability.VPVNP.CompressorShrinkInputTerms

/-!
# Reusing the gathered-key rectangle

After ranking, the sorted widths and their starts are above the gathered-key
rectangle. The old incidence, greedy assignments and preliminary placements
are below it. All these tables survive when the absolute motif directory
replaces the gathered keys.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkInput

open BurstRAM Compression ShrinkRankSpace
open scoped Classical

variable {w a g : ℕ} {X : State a (packingLaneBits a g)} {T : IncidenceDirectory w} {start : ℕ}
local notation "Z" => plan X start
local notation "sh" => placementBank X T start
local notation "wb" => widthBase X start
local notation "thick" => thickBank X T start
local notation "cd" => cdBank X T start
local notation "ab" => piecesBank X T start

/-- Physical readbacks still required after the absolute motif directory is written. -/
structure Retained (X : State a (packingLaneBits a g)) (T : IncidenceDirectory w) (start : ℕ) (out : Memory w) : Prop where
  incidence : T.Represents X out
  placement : ShrinkRAM.PlacementColumns X.slots X.baseIndex (placementBank X T start) false out
  directory : Shrink.Directory X.slots X.baseIndex
    (ShrinkRAM.column (placementBank X T start) out 6) (ShrinkRAM.column (placementBank X T start) out 7)
    (ShrinkRAM.column (placementBank X T start) out 8) (ShrinkRAM.column (placementBank X T start) out 9)
  stored : ShrinkTermSelection.oldRows X (thickBank X T start) (cdBank X T start) (piecesBank X T start) out

namespace Run

variable {m : Memory w} (r : Run X T start m)

private theorem keepGeometry {out : Memory w} (room : stop X start < 2^w)
    (low : ∀ z < (Z).gathered, out z = r.post z) :
    T.Represents X out ∧ ShrinkRAM.PlacementColumns X.slots X.baseIndex sh false out ∧
      Shrink.Directory X.slots X.baseIndex
        (ShrinkRAM.column sh out 6) (ShrinkRAM.column sh out 7)
        (ShrinkRAM.column sh out 8) (ShrinkRAM.column sh out 9) := by
  obtain ⟨h₁,h₂,_,_⟩ := range_bounds X start
  have hg : rankBase X start ≤ (Z).gathered := by
    change rankBase X start ≤ rankBase X start+2*(Z).A+2*(Z).B+(Z).rectangleSize
    omega
  exact ⟨r.incidence.retain (fun c ↦ (r.greedy.old c).trans (h₁.trans (h₂.trans hg))) low,
    (r.placement room).retain (fun t ↦ (pre_starts X T start room t).trans hg) low,
    r.directory_before (fun z hz ↦ low z (hz.trans_le (h₂.trans hg)))⟩

theorem keepAbsoluteFrame {out : Memory w} (room : stop X start < 2^w)
    (frame : ∀ z, z < (Z).gathered ∨ (Z).ranks ≤ z → out z = r.post z) :
    Retained X T start out := by
  have h₄ := (range_bounds X start).2.2.2
  obtain ⟨inc,place,dir⟩ := r.keepGeometry room (fun z h ↦ frame z (.inl h))
  refine ⟨inc,place,dir,?_⟩
  let B := (Z).B
  let Q := (Z).Q
  let q := Shape.collectBank (plan X start) w
  let block := B*(q 4).val
  have hv := (Z).values T sh Fintype.card_pos (h₄.trans_lt room)
  have bs : block = B*Q := by change B*(q 4).val = _; rw [hv.stride]
  have limit : wb+6*block+2*B < 2^w := bs.symm ▸ room
  have rankBefore : (Z).ranks ≤ wb := Nat.le_add_right ..
  have hbase : wb % (2^w) = wb := Nat.mod_eq_of_lt (by omega)
  have t₂ : (thick 2).val = wb := by
    change (wb % (2^w)) % (2^w) = wb
    rw [hbase,hbase]
  have c₂ : (cd 2).val = wb+block := by
    change (wb % (2^w)+block) % (2^w) = wb+block
    rw [hbase,Nat.mod_eq_of_lt (by omega)]
  have t₃ : (thick 3).val = wb+2*block :=
    Nat.mod_eq_of_lt (show wb+2*block < 2^w by omega)
  have c₃ : (cd 3).val = wb+2*block+block :=
    Nat.mod_eq_of_lt (show wb+2*block+block < 2^w by omega)
  have a₃ : (ab 3).val = wb+2*block+2*block+2*B :=
    Nat.mod_eq_of_lt (show wb+2*block+2*block+2*B < 2^w by omega)
  have a₄ : (ab 4).val = wb+2*block+2*block+2*B+B*Q :=
    Nat.mod_eq_of_lt (show wb+2*block+2*block+2*B+B*Q < 2^w by omega)
  have keep (base i j : ℕ) (h : wb ≤ base) :
      (out (base+i+j)).val = (r.post (base+i+j)).val :=
    congrArg Fin.val (frame _ (.inr (by omega)))
  exact ⟨fun b i ↦ (keep _ _ _ t₂.ge).trans (r.stored.thickWidths b i),
    fun b i ↦ (keep _ _ _ (by omega : wb ≤ (cd 2).val)).trans (r.stored.cdWidths b i),
    fun b x ↦ (keep _ _ _ (by omega : wb ≤ (thick 3).val)).trans (r.stored.thickStarts b x),
    fun b x ↦ (keep _ _ _ (by omega : wb ≤ (cd 3).val)).trans (r.stored.cdStarts b x),
    ⟨fun b i ↦ (keep _ _ _ (by omega : wb ≤ (ab 3).val)).trans (r.stored.ab.widths b i),
     fun b i ↦ (keep _ _ _ (by omega : wb ≤ (ab 4).val)).trans (r.stored.ab.starts b i)⟩⟩

/-- An absolute-ID pass can be followed by a demand or term pass which
writes into higher addresses. All the input readbacks still hold. -/
theorem keepAbsoluteThenTerms {abs out : Memory w}
    (frameAbs : ∀ z, z < (Z).gathered ∨ (Z).ranks ≤ z → abs z = r.post z)
    (stride : ℕ) (room : termEnd X start stride < 2^w)
    (frameTerms : ∀ z < stop X start, out z = abs z) : Retained X T start out := by
  have endRoom : stop X start < 2^w := by unfold termEnd at room; omega
  have lo : (Z).gathered ≤ stop X start := by
    change (Z).gathered ≤ (Z).gathered+(Z).rectangleSize+(Z).A+6*((Z).B*(Z).Q)+2*(Z).B
    omega
  obtain ⟨inc,place,dir⟩ := r.keepGeometry endRoom fun z hz ↦
    (frameTerms z (hz.trans_le lo)).trans (frameAbs z (.inl hz))
  have absRows := (r.keepAbsoluteFrame endRoom frameAbs).stored
  have earlier := (termLayout X T start stride room).2.1
  have hd : (demandHead (w := w) X start).val = stop X start := Nat.mod_eq_of_lt endRoom
  rw [hd] at earlier
  exact ⟨inc,place,dir,ShrinkDemandFrame.retain absRows earlier frameTerms⟩

end Run

end CompressorRecords.ShrinkInput

end VPVNP
end Computability
end OAI
