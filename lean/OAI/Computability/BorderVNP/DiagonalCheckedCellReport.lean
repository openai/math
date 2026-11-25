import OAI.Computability.BorderVNP.DiagonalCellReportCountChoice
import OAI.Computability.BorderVNP.PackedBottomFixedUseTape
import OAI.Computability.BorderVNP.PackedFinalCellObservationTail
import OAI.Computability.BorderVNP.PackedSupplementResources
import OAI.Computability.BorderVNP.FiniteDiagonalCellTraceUnique

/-! # Exact positive signed weight on the unique checked cell report bit string -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open CellSparse Packing.BottomReports VPVNP.TapeWord
open scoped Classical
open private append_blocks from OAI.Computability.BorderVNP.PackedSupplementResources
open private bank_words from OAI.Computability.BorderVNP.DiagonalCellReportCountChoice
open private count_bits from OAI.Computability.BorderVNP.DiagonalTallyReportBitsRead

/-- Count words as delivered by the physical count-first report bank. -/
def countPart {g d : ℕ} (v : Fin g → Fin d → Bool) : List Bool := (List.ofFn fun i => List.ofFn (v i)).flatten

@[simp] theorem countPart_length {g d : ℕ} (v : Fin g → Fin d → Bool) : (countPart v).length = g*d := by
  simp [countPart,List.length_flatten,List.map_ofFn,Function.comp_def,List.ofFn_const]

private theorem countPart_injective {g d : ℕ} : Function.Injective (@countPart g d) := by
  intro a b eqn
  let m := fun i => (lookup (countPart a) i).toNat
  have ha : literalBitsAt m 0 (countPart a) := by simpa [m] using bank_words [] (countPart a)
  have hb : literalBitsAt m 0 (countPart b) := eqn ▸ ha
  funext i j
  have e := (count_bits m 0 a ha i j).symm.trans (count_bits m 0 b hb i j)
  cases ha : a i j <;> cases hb : b i j <;> simp_all

/-- Actual checked report chosen by a fixed core: exact row counts followed
by the copied original weighted-source choices. -/
noncomputable def canonicalTail (obs : List (Bool × Option ℕ)) (g d : ℕ) (pre : List Bool) (bs : List Bundle) : List Bool :=
  countPart (observationCounts obs g d) ++ useTape pre bs

private theorem append_checked {D : Directory} (extra : List Record) (wire : ∀ r ∈ extra, Wiring r)
    (bank : ℕ → Bool) (os : List (Bool × Option ℕ)) :
    (appendRows D extra).guardedObservations bank = some os ↔
      D.guardedObservations bank = some os ∧ ∀ r ∈ extra, r.Valid D.boxes bank := by
  have eq : (appendRows D extra).occurrences=D.occurrences := by
    rw [← Directory.blocks_visits,← Directory.blocks_visits,append_blocks _ _ wire]
  simp only [Directory.guarded_some,appendRows,List.forall_mem_append]
  change ((_ ∧ _) ∧ (appendRows D extra).observations bank=some os) ↔ ((_ ∧ _) ∧ _)
  have ho : (appendRows D extra).observations bank=D.observations bank := by unfold Directory.observations; rw [eq]
  rw [ho]
  tauto

/-- Conditional on a fixed passing core, the actual typed packet has integer
weight one on its unique report spelling and zero on every other spelling. -/
theorem checked_report_weight {l : ReportLayout} (c : ReportCell l) (D : Directory) (pre : List Bool)
    (bs : List Bundle) (obs : List (Bool × Option ℕ)) (unsigned : D.SignFree)
    (layout : D.reportedCounts = countFields pre.length l.gadgets l.countWidth)
    (seen : D.guardedObservations (lookup (pre++c.bits)) = some obs)
    (core : ∀ b ∈ bs, b.CorePass pre)
    (width : (c.bundles.map ReportBundle.useCount).sum = (bs.map Bundle.useBits).sum)
    (range : ∀ i ∈ obs.filterMap Prod.snd, i < l.gadgets)
    (fit : ∀ i : Fin l.gadgets, (obs.filterMap Prod.snd).count i.val < 2^l.countWidth) :
    let extra := supplements (pre.length+l.gadgets*l.countWidth) bs
    (appendRows D extra).weight (lookup (pre++c.bits)) =
      if c.bits=canonicalTail obs l.gadgets l.countWidth pre bs then 1 else 0 := by
  let extra := supplements (pre.length+l.gadgets*l.countWidth) bs
  let bank := lookup (pre++c.bits)
  let uses := c.bundles.flatMap fun b => List.ofFn b.uses
  have unsigned' : (appendRows D extra).SignFree := unsigned
  have huse : uses.length=(bs.map Bundle.useBits).sum := by
    simp only [uses,List.length_flatMap,List.length_ofFn]
    exact width
  have useIff : (∀ r ∈ extra, r.Valid D.boxes bank) ↔ uses=useTape pre bs := by
    have result := supplements_iff_useTape pre (countPart c.counts) uses bs D.boxes core huse
    rw [countPart_length] at result
    simpa only [List.append_assoc,ReportCell.bits,bank,extra,countPart,uses] using result
  have check : (∃ os, (appendRows D extra).guardedObservations bank = some os ∧
      countsValid bank (appendRows D extra).reportedCounts os) ↔ c.bits=canonicalTail obs l.gadgets l.countWidth pre bs := by
    constructor
    · rintro ⟨os,pass,counts⟩
      obtain ⟨orig,extraPass⟩ := (append_checked extra (supplements_wiring _ _) bank os).mp pass
      have eq := Option.some.inj (seen.symm.trans orig)
      subst os
      change countsValid bank D.reportedCounts obs at counts
      rw [layout] at counts
      have digit := (c.checkedCounts pre obs range fit).mp counts
      exact congrArg₂ List.append (congrArg countPart digit) (useIff.mp extraPass)
    · intro spell
      have parts := List.append_inj (show countPart c.counts ++ uses =
        countPart (observationCounts obs l.gadgets l.countWidth) ++ useTape pre bs from spell)
        (by rw [countPart_length,countPart_length])
      refine ⟨obs,(append_checked extra (supplements_wiring _ _) bank obs).mpr ⟨seen,useIff.mpr parts.2⟩,?_⟩
      change countsValid bank D.reportedCounts obs
      rw [layout]
      exact (c.checkedCounts pre obs range fit).mpr (countPart_injective parts.1)
  change (appendRows D extra).weight bank = if c.bits=canonicalTail obs l.gadgets l.countWidth pre bs then 1 else 0
  rw [unsigned'.weight_guarded]
  exact if_congr check rfl rfl

/-- On a failing original core every count and use spelling is rejected by
the same positive native checker. -/
theorem checked_report_absent {l : ReportLayout} (c : ReportCell l) (D : Directory) (pre : List Bool)
    (bs : List Bundle) (unsigned : D.SignFree)
    (none_ : D.guardedObservations (lookup (pre++c.bits)) = none) :
    let extra := supplements (pre.length+l.gadgets*l.countWidth) bs
    (appendRows D extra).weight (lookup (pre++c.bits)) = 0 := by
  let extra := supplements (pre.length+l.gadgets*l.countWidth) bs
  let bank := lookup (pre++c.bits)
  have h : (appendRows D extra).SignFree := unsigned
  change (appendRows D extra).weight bank = 0
  rw [h.weight_guarded]
  apply ite_eq_right
  rintro ⟨os,pass,_⟩
  have orig := ((append_checked extra (supplements_wiring _ _) bank os).mp pass).1
  have absurd : none = some os := none_.symm.trans orig
  cases absurd

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
