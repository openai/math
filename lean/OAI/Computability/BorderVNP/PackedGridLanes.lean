import OAI.Computability.BorderVNP.PackedGridRoutedFactors

/-! # Trivalence and the size of the physical fine tables after routing -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.Network

open BorderVNP.Shortening Finset
open scoped Classical
variable {D : ℕ} {P : Type} [Fintype P] (N : Network D P (fun _ => 1))

private theorem degree_eq (v : N.Site) : N.bitDegree v =
    (univ.filter fun e => N.src e = v).card + (univ.filter fun e => N.dst e = v).card +
      (univ.filter fun p => N.attach p = v).card := by
  unfold bitDegree
  simp only [card_eq_sum_ones,sum_filter]
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl,Sum.elim_inr]
  conv_lhs => arg 2; rw [Fintype.sum_prod_type_right,Fintype.sum_bool]
  simp only [Bool.false_eq_true,ite_false,ite_true]
  rw [Nat.add_comm (∑ a : P, _) _, Nat.add_comm (∑ e : N.Edge, _) (∑ e : N.Edge, _)]
  congr 1

private theorem local_records_one (v : N.Site) :
    localRecords N false (fun _ => 0) (fun _ => 0) (· = v) = 1+N.bitDegree v := by
  rw [degree_eq]
  simp only [localRecords,testedWidth,boxCost,recordCost, Bool.false_eq_true, ite_false,
    Nat.add_zero,Nat.zero_add,card_eq_sum_ones,sum_filter]
  simp only [sum_ite_eq',mem_univ,ite_true]
  omega

/-- A loop has two port incidences and only one shared tensor argument. Thus the number
of one-bit input lanes of a table is at most the incidence degree used by Lemma 2.3. -/
theorem lane_count_le (unit : ∀ e, N.width e = 1) (v : N.Site) :
    Fintype.card (CellBox.Lane N v) ≤ N.bitDegree v := by
  rw [degree_eq]
  simp only [CellBox.Lane,Fintype.card_sum,Fintype.card_sigma,Fintype.card_fin,unit,
    sum_const,card_univ,nsmul_eq_mul,Nat.mul_one,Fintype.card_subtype]
  apply Nat.add_le_add_right
  simp only [card_eq_sum_ones,sum_filter,← sum_add_distrib]
  apply sum_le_sum
  intro e _
  by_cases hs : N.src e = v <;> by_cases hd : N.dst e = v <;> simp [hs,hd]

/-- Every physical cable of a routed trivalent batch is still a bit cable, and every
equality box has two port incidences. The incidence count of an old site is preserved. -/
theorem trivalent_subdivide (tri : N.Trivalent) (routes : N.WireRoutes) :
    (N.subdivide routes).Trivalent := by
  refine ⟨fun e => tri.1 e.1, fun v => ?_⟩
  have hr := BorderVNP.Cover.subdivision_records_eq N routes false (fun _ => 0)
    (fun _ => 0) (· = v)
  have hs := (N.subdivide routes).local_records_one v
  have hz : (Sum.elim (fun _ : N.Site => 0) (fun _ : (e : N.Edge) × Fin (routes.interior e) => 0)) =
      (fun _ => (0:ℕ)) := by funext i; cases i <;> rfl
  rw [hz] at hr
  replace hr := hs.symm.trans hr
  cases v with
  | inl a =>
    have he : (fun i : N.Site => (Sum.inl i : (N.subdivide routes).Site) = .inl a) = (· = a) := by
      funext i; simp
    erw [he,local_records_one] at hr
    simp only [reduceCtorEq,ite_false,sum_const_zero,Nat.add_zero] at hr
    have hd := tri.2 a
    omega
  | inr p =>
    have hs : localRecords N false (fun _ => 0) (fun _ => 0)
        (fun i => (Sum.inl i : (N.subdivide routes).Site) = .inr p) = 0 := by
      simp [localRecords,testedWidth]
    erw [hs,Nat.zero_add] at hr
    have hh : (∑ q : (e : N.Edge) × Fin (routes.interior e), if
        (Sum.inr q : (N.subdivide routes).Site) = .inr p then 1+2*recordCost false (N.width q.1) else 0) = 3 := by
      simp [recordCost]
    let cost (q : (e : N.Edge) × Fin (routes.interior e)) := if
        (Sum.inr q : (N.subdivide routes).Site) = .inr p then 1+2*recordCost false (N.width q.1) else 0
    have htot := (Fintype.sum_sigma cost).symm.trans hh
    have h3 : 1 + (N.subdivide routes).bitDegree (.inr p) = 3 := by
      apply hr.trans
      apply Eq.trans _ htot
      apply sum_congr rfl
      intro e _
      apply sum_congr rfl
      intro j _
      dsimp only [cost]
      split <;> split <;> simp_all [recordCost]
      exact ‹¬_› rfl
    omega

end Crossing.Network

end BorderVNP
end Computability
end OAI
