import OAI.Computability.BorderVNP.CubePhysicalDeclaration

/-! # The physical communication budget for the declared cut

The singleton bits are enumerated once for each ordered label pair and each
padded offset. Packet contributions come from the widths of the edges of the
selected ordinary summand. Identifying the two finite sums with the loads of
Section 8.2 applies (8.1) to the concrete least minimizing coordinate.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical

open VPVNP VPVNP.MotifBase
open scoped Classical BigOperators

/-- Counting the individual retained bit slots that change the coordinate
is exactly the singleton load defined by counting destinations per source. -/
theorem singleSlot_cross_sum (n d blocks width : ℕ) (j : Fin (n+1)) :
    (∑ z : SingleSlot n d blocks width, (decide (z.1.val.1 j ≠ z.1.val.2 j)).toNat) =
      singletonLoad n d blocks width j := by
  let single (p : Label (n+1) d × Label (n+1) d) := ¬∀ i, p.1 i ≠ p.2 i
  let cost (p : Label (n+1) d × Label (n+1) d) := (blocks*width) * (decide (p.1 j ≠ p.2 j)).toNat
  change (∑ z : {p // single p} × Fin (blocks*width), (decide (z.1.val.1 j ≠ z.1.val.2 j)).toNat) = _
  rw [Fintype.sum_prod_type]
  change (∑ p : {p // single p}, ∑ _ : Fin (blocks*width), (decide (p.val.1 j ≠ p.val.2 j)).toNat) = _
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  change (∑ z : {p // single p}, cost z.val) = _
  rw [← Finset.sum_subtype (p := single) (Finset.univ.filter single) (fun _ => by simp) cost,
    Finset.sum_filter, Fintype.sum_prod_type]
  unfold singletonLoad
  apply Finset.sum_congr rfl
  intro u _
  have hc : ((singletons u).filter fun v => u j ≠ v j).card =
      ∑ v ∈ singletons u, if u j ≠ v j then (1 : ℕ) else 0 := by
    simpa only [Nat.cast_id] using (Finset.sum_boole (R := ℕ) (fun v : Label (n+1) d => u j ≠ v j) (singletons u)).symm
  rw [hc, Finset.mul_sum, singletons, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v _
  change (if single (u,v) then cost (u,v) else 0) =
    (if ∃ i, v i = u i then blocks*width*(if u j ≠ v j then 1 else 0) else 0)
  have hs : single (u,v) ↔ ∃ i, v i = u i := by simp [single, eq_comm]
  by_cases ha : single (u,v)
  · rw [ite_eq_left ha, ite_eq_left (hs.mp ha)]
    by_cases he : u j = v j <;> simp [cost, he]
  · rw [ite_eq_right ha, ite_eq_right (mt hs.mpr ha)]

variable {n d blocks K h : ℕ}

/-- The width computed by the physical declaration is the sum of the actual
selected edge load and the retained singleton load. -/
theorem cutWidth_eq_load (b s : ℕ) (select : Packet n d blocks → Selector n K h) (j : Fin (n+1)) :
    (cutWidth b s select j : ℝ) =
      edgeLoad (fun p e => (payload (onEdge s) (select p).2 e : ℝ)) j + singletonLoad n d blocks (h*b) j := by
  unfold cutWidth
  rw [Fintype.sum_sum_type]
  simp only [crossCount, singleSlot_cross_sum, edgeLoad, Nat.cast_add, Nat.cast_sum]

/-- Equation (8.1) for the grouping coordinate in the unique passing physical
declaration, including one fixed selector encoding per packet. -/
theorem chosen_coordinate_budget (b s : ℕ) (select : Packet n d blocks → Selector n K h)
    (hd : 0 < d) {η : ℝ} (hη : 0 ≤ η)
    (hwidth : ∀ σ : Fin h → Edge (n+1), (∑ e, (payload (onEdge s) σ e : ℝ)) ≤
      2 * 2^n * Real.sqrt (n+1) * (h*b : ℕ))
    (hsel : (MotifWidths.selectorBits K (Fintype.card (Edge (n+1))) h : ℝ) ≤ η * (h*b : ℕ)) :
    (cutWidth b s select (chosen b s select) : ℝ) +
        ∑ _p : Packet n d blocks, (MotifWidths.selectorBits K (Fintype.card (Edge (n+1))) h : ℝ) ≤
      padded n d blocks (h*b) * (2/Real.sqrt (n+1) + (n+1)/d + η) := by
  obtain ⟨i, _, hi⟩ := coordinate_budget n d blocks (h*b) hd hη
    (fun p e => (payload (onEdge s) (select p).2 e : ℝ))
    (fun _ => (MotifWidths.selectorBits K (Fintype.card (Edge (n+1))) h : ℝ))
    (fun p => hwidth (select p).2) (fun _ => hsel)
  rw [← cutWidth_eq_load b s select i] at hi
  have hm : cutWidth b s select (chosen b s select) ≤ cutWidth b s select i := firstMinimum_le _ i
  exact (add_le_add_left (Nat.cast_le.mpr hm) _).trans hi

/-- Every field admits arbitrarily large block widths and ordinary antipodal
packet identities whose true selectors satisfy the physical declaration budget
for every positive alphabet size and every block count. -/
theorem exists_identity_with_chosen_budget (F : Type*) [Field F] (n B : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ b h K s : ℕ, B ≤ h*b ∧ 0 < h*b ∧ 1 ≤ K ∧
      BaseIdentity F (@start n) (@stop n) Prod.fst head (fun _ => b) (onEdge s) K h ∧
      ∀ d blocks : ℕ, 0 < d → ∀ select : Packet n d blocks → Selector n K h,
        (cutWidth b s select (chosen b s select) : ℝ) +
          ∑ _p : Packet n d blocks, (MotifWidths.selectorBits K (Fintype.card (Edge (n+1))) h : ℝ) ≤
        padded n d blocks (h*b) * (2/Real.sqrt (n+1) + (n+1)/d + η) := by
  obtain ⟨b, h, K, s, hB, hb, hK, hident, hsel, hw⟩ := antipodal_wire_identity F n B η hη
  exact ⟨b, h, K, s, hB, hb, hK, hident,
    fun _ _ hd select => chosen_coordinate_budget b s select hd hη.le hw hsel⟩

end Cube.Physical

end BorderVNP
end Computability
end OAI
