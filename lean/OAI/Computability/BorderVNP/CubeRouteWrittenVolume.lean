import OAI.Computability.BorderVNP.CubeRouteWrittenRecords
import OAI.Computability.BorderVNP.CubeGroupPhysicalRows
import OAI.Computability.BorderVNP.CubeGroupWeightCheckedSchedule
import OAI.Computability.BorderVNP.CubeGroupDirectoryVolume

/-! # Bounds for the physical routing table

Every populated demand originates on one of the actual teams. The budget check
bounds the sum of the physical widths of those demands and of the strict shared
lists because the histogram counts each demand once and each shared list twice.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.RouteRecords

open Physical GroupWeights RoutingISA RoutingISA.Transmission TeamContraction Packing.Directory

/-- A populated private row comes from an occupied block of the reserved processor tails.
A live row comes from the enumerated team in its candidate index. -/
theorem populated_sender (d : Packing.Directory.Layout) (pp lp : ℕ → ℕ × ℕ)
    (processors : 0 < d.processors) (fields : 0 < d.fields)
    (storage : d.entries*d.description ≤ d.teams*d.processors*(d.literal/2))
    (r : Row) (populated : r ∈ d.directory pp lp) : r.team < d.teams := by
  obtain ⟨i,hi,rfl,pos⟩ := (d.mem_directory_iff pp lp r).mp populated
  by_cases branch : i < 2*d.entries
  · simp only [Packing.Directory.Layout.row,ite_eq_left branch] at pos ⊢
    let start := (i/2)*d.description
    let proc := start/(d.literal/2)+i%2
    let part := slice start d.description (d.literal/2) (i%2)
    change 0 < part.2 at pos
    have bit := (mem_slice_iff start d.description (d.literal/2) (i%2) part.1).mp
      (show part.1 ≤ part.1 ∧ part.1 < part.1+part.2 by omega)
    have entry : i/2 < d.entries := (Nat.div_lt_iff_lt_mul (by decide : 0<2)).mpr (by omega)
    have high : start+d.description ≤ d.entries*d.description := by
      rw [show start+d.description = (i/2+1)*d.description by simp [start,Nat.add_mul]]
      exact Nat.mul_le_mul_right _ entry
    have lt : proc*(d.literal/2) < d.teams*d.processors*(d.literal/2) :=
      lt_of_le_of_lt bit.2.2.1 (lt_of_lt_of_le bit.2.1 (high.trans storage))
    exact (Nat.div_lt_iff_lt_mul processors).mpr (Nat.lt_of_mul_lt_mul_right lt)
  · simp only [Packing.Directory.Layout.row,ite_eq_right branch,Packing.Directory.Layout.liveRow] at ⊢
    apply (Nat.div_lt_iff_lt_mul processors).mpr
    apply (Nat.div_lt_iff_lt_mul fields).mpr
    apply (Nat.div_lt_iff_lt_mul (Nat.zero_lt_succ (d.literal/d.block+1))).mpr
    change i < 2*d.entries + d.teams*d.processors*d.fields*(d.literal/d.block+2) at hi
    change i-2*d.entries < d.teams*d.processors*d.fields*(d.literal/d.block+2)
    omega

/-- The aggregate group histogram dominates the scheduler's unscaled sum of widths.
This remains true for shared lists whose two symbol owners are the same team. -/
theorem widths_le_weights {A : Type*} [Fintype A] {l : GroupWeights.Layout} {mem : ℕ → ℕ}
    {n blocks b K h : ℕ} {D : LengthDeclaration n l.groups} {label : Fin l.cells → Label (n+1) l.groups}
    {recv : A → Fin l.cells} {width : A → ℕ} (image : PhysicalImage l mem blocks b K h D label recv width) :
    (∑ i, width i) + (∑ p, SharedRows.reserved blocks K h D p) ≤
      ∑ i ∈ Finset.range l.groups, l.weight mem i := by
  rw [← Fin.sum_univ_eq_sum_range]
  have hist := Finset.sum_le_sum (s := Finset.univ) (f := fun s : Fin l.groups =>
    SharedRows.incident blocks K h D s + SharedRows.dataAt (label ∘ recv) width D.1 s)
    (g := fun s => l.weight mem s.val) (fun s _ => by
      rw [image.weight_eq_groupWords s,SharedRows.groupWords,dite_eq_left s.isLt,TeamNative.scaledWeight]
      simp only [Fin.eta]
      omega)
  rw [Finset.sum_add_distrib,SharedRows.sum_incident,SharedRows.sum_dataAt] at hist
  omega

/-- The native aggregate guard provides word room for the scheduler's exact
width sum at the returned team schedule. -/
theorem widths_fit_of_guard {A : Type*} [Fintype A] {l : GroupWeights.Layout} {t : TeamNative.Layout}
    {orig mem : ℕ → ℕ} {n blocks b K h w X : ℕ} {D : LengthDeclaration n l.groups}
    {label : Fin l.cells → Label (n+1) l.groups} {recv : A → Fin l.cells} {width : A → ℕ}
    (image : PhysicalImage l orig blocks b K h D label recv width)
    (schedule : ScheduleResult l t orig mem) (guard : (TeamBudget.Layout.mk (t.r+1) X t.totals).Passes mem)
    (room : (TeamBudget.Layout.mk (t.r+1) X t.totals).totalLimit < 2^w) :
    (∑ i, width i) + (∑ p, SharedRows.reserved blocks K h D p) < 2^w :=
  lt_of_le_of_lt ((widths_le_weights image).trans ((schedule.passes_iff X).mp guard).2) room

/-- The allocated word envelope for the native budget test includes its aggregate cap. -/
theorem budgetLimit_fit {budget : TeamBudget.Layout} {frame w : ℕ} (fit : budget.Fits frame w) :
    budget.totalLimit < 2^w :=
  lt_of_le_of_lt (Nat.div_le_self _ _) fit.allScaled

/-- Match the width sum of the semantic prefix to the physical group inventory,
at the actual published seven-word demand directory. -/
theorem published_width_sum {w : ℕ} (dir : LabelIndex.Layout) (m : VPVNP.BurstRAM.Memory w)
    (data : List Row) (head : ℕ) (count : dir.deliveryCount = data.length)
    (before : head+9 < dir.deliveries)
    (fits : ∀ i : Fin data.length, ∀ a ∈ data[i.val].words, a < 2^w) :
    (∑ i : Fin data.length, data[i.val].width) = ∑ j : Fin dir.deliveryCount,
      (LabelIndex.deliveryAt dir (readings (ISA.publish m head dir.deliveries data)) j.val).2 := by
  rw [Packing.CableTriples.published_deliveryWidth_eq dir m data head count before fits]
  conv_rhs => rw [← List.ofFn_get data,List.map_ofFn,List.sum_ofFn]
  rfl

/-- A genuine populated directory and checked physical group histogram furnish all
label and aggregate bounds consumed by the native router. -/
theorem rowsFit_of_schedule {l : GroupWeights.Layout} {t : TeamNative.Layout} {orig mem : ℕ → ℕ}
    {n blocks b K h w X : ℕ} {D : LengthDeclaration n l.groups}
    (d : Packing.Directory.Layout) (pp lp : ℕ → ℕ × ℕ)
    (processors : 0 < d.processors) (fields : 0 < d.fields)
    (storage : d.entries*d.description ≤ d.teams*d.processors*(d.literal/2))
    (owners : ℕ → Fin (t.r+1)) (group : Fin l.groups → Fin (t.r+1))
    {A : Type*} [Fintype A] {label : Fin l.cells → Label (n+1) l.groups}
    {recv : A → Fin l.cells} {width : A → ℕ}
    (image : PhysicalImage l orig blocks b K h D label recv width)
    (schedule : ScheduleResult l t orig mem) (guard : (TeamBudget.Layout.mk (t.r+1) X t.totals).Passes mem)
    (room : (TeamBudget.Layout.mk (t.r+1) X t.totals).totalLimit < 2^w)
    (volume : (∑ i : Fin (d.directory pp lp).length, (d.directory pp lp)[i.val].width) = ∑ a, width a)
    (tab : TableLayout) (count : tab.count = (d.directory pp lp).length+l.groups.choose 2)
    (teams : t.r+1 = tab.teams) (sources : d.teams = t.r+1) :
    tab.RowsFit w (combinedRow (d.directory pp lp) owners blocks K h D group) := by
  apply rowsFit _ _ _ _ _ _ _ tab count teams
  · intro i
    rw [← sources]
    exact populated_sender d pp lp processors fields storage _ (List.getElem_mem i.isLt)
  · rw [volume]
    exact widths_fit_of_guard image schedule guard room

end Cube.RouteRecords

end BorderVNP
end Computability
end OAI
