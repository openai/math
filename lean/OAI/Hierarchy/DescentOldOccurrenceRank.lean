import OAI.Hierarchy.DescentOccurrenceCount
import OAI.Hierarchy.DescentTerminalSortLex
import OAI.Hierarchy.DescentPackingOrdinals

namespace OAI
/-! # Exact positions in a stably sorted three-key original-edge stream -/

namespace Hierarchy.DescentOldOccurrenceRAM
open scoped BigOperators Classical
noncomputable section
variable {n g t s : ℕ}

theorem count_equiv {I J : Type*} [Fintype I] [Fintype J] (e : I ≃ J)
    (p : I → Prop) (q : J → Prop) (h : ∀i,p i ↔ q (e i)) : count p = count q := by
  rw [count_eq_sum,count_eq_sum]
  exact Fintype.sum_equiv e _ _ (fun i => by rw [h i])

theorem position_count (order : Fin n ≃ Fin n) (i : Fin n) :
    (order.symm i).val = count (fun j => order.symm j < order.symm i) := by
  rw [count_equiv order.symm _ (fun j => j < order.symm i) (fun _ => Iff.rfl)]
  unfold count
  calc
    _ = (Finset.Iio (order.symm i)).card := (Fin.card_Iio _).symm
    _ = _ := by
      apply congrArg Finset.card
      ext j
      simp

theorem count_four_lex (a : Fin n→Fin g) (b : Fin n→Fin t) (c : Fin n→Fin s) (e : Fin n) :
    ((DescentTerminalSortRAM.order a b c).symm e).val =
      count (fun f => a f < a e) +
      count (fun f => a f=a e ∧ b f < b e) +
      count (fun f => a f=a e ∧ b f=b e ∧ c f < c e) +
      count (fun f => a f=a e ∧ b f=b e ∧ c f=c e ∧ f < e) := by
  rw [position_count]
  simp only [count_eq_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro f _
  rw [DescentTerminalSortRAM.ordered_positions]
  rcases lt_trichotomy (a f) (a e) with ha|ha|ha
  · simp [ha,ha.ne]
  · simp only [ha,lt_self_iff_false,false_or,true_and,ite_false,zero_add]
    rcases lt_trichotomy (b f) (b e) with hb|hb|hb
    · simp [hb,hb.ne]
    · simp only [hb,lt_self_iff_false,false_or,true_and,ite_false,zero_add]
      rcases lt_trichotomy (c f) (c e) with hc|hc|hc
      · simp [hc,hc.ne]
      · simp [hc]
      · simp [hc.ne',not_lt.mpr hc.le]
    · simp [hb.ne',not_lt.mpr hb.le]
  · simp [ha.ne',not_lt.mpr ha.le]

theorem prefix_ones {I : Type*} [Fintype I] (rank : I → ℕ) (i : I) :
    ProtocolRAMPortRanks.«prefix» (fun _ : I => 1) rank i = count (fun j=>rank j < rank i) := by
  simp [ProtocolRAMPortRanks.«prefix»,count]
  apply congrArg Finset.card
  ext j
  simp

/-- The two ordered fields of every thin/thick pool expose their physical prefix sums. -/
theorem prefix_count_fibers {I J : Type*} [Fintype I] [Fintype J]
    (bucket : I → J) (keep : I → Prop) (rank : J → ℕ) (j : J) :
    ProtocolRAMPortRanks.«prefix» (fun a => count (fun i => keep i ∧ bucket i=a)) rank j =
      count (fun i => keep i ∧ rank (bucket i) < rank j) := by
  simp only [ProtocolRAMPortRanks.«prefix»,count_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases active : keep i
  · simp [active]
  · simp [active]

end
end Hierarchy.DescentOldOccurrenceRAM

end OAI
