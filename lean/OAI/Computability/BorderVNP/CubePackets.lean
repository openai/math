import OAI.Computability.BorderVNP.CubeIdentity
import Mathlib.Data.Fintype.BigOperators

/-!
# Cube packets and coordinate selection

Section 8.2 assigns every ordered label pair differing in all coordinates to its
unique binary cube. Its first coordinate fixes the orientation, leaving one bit per
remaining coordinate to index the antipodal pairs in the packet. Pairs agreeing in
some coordinate are charged separately. Averaging the new edge widths over the cuts
gives the bound (8.1).
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube

/-- The two distinct symbols in one coordinate of a binary subcube, in increasing order. -/
abbrev Symbols (d : ℕ) := {p : Fin d × Fin d // p.1 < p.2}

/-- A label in a product of equal alphabets. -/
abbrev Label (a d : ℕ) := Fin a → Fin d

/-- The ordered label pairs that belong to a binary cube packet. -/
abbrev FullPair (a d : ℕ) := {p : Label a d × Label a d // ∀ i, p.1 i ≠ p.2 i}

private def ordered {d : ℕ} (u v : Fin d) (h : u ≠ v) : Symbols d :=
  if hlt : u < v then ⟨(u,v), hlt⟩ else ⟨(v,u), lt_of_le_of_ne (le_of_not_gt hlt) h.symm⟩

/-- Full pairs correspond to one unique binary subcube and one corner of it. -/
def fullPairEquiv (a d : ℕ) : FullPair a d ≃ (Fin a → Symbols d) × (Fin a → Bool) where
  toFun p := (fun i ↦ ordered (p.val.1 i) (p.val.2 i) (p.property i),
    fun i ↦ decide (p.val.2 i < p.val.1 i))
  invFun q :=
    ⟨(fun i ↦ if q.2 i then (q.1 i).val.2 else (q.1 i).val.1,
      fun i ↦ if q.2 i then (q.1 i).val.1 else (q.1 i).val.2),
      fun i ↦ by
        cases hi : q.2 i
        · simpa [hi] using (q.1 i).property.ne
        · simpa [hi] using (q.1 i).property.ne'⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> funext i <;> rcases lt_or_gt_of_ne (p.property i) with h | h <;>
      simp [ordered, h, h.not_gt]
  right_inv q := by
    rcases q with ⟨box,corner⟩
    apply Prod.ext <;> funext i <;> cases hi : corner i <;>
      simp [ordered, hi, (box i).property, (box i).property.not_gt]

/-- Every block of full-pair wires is enumerated by packet (cube, orientation, block),
antipodal pair within that packet, and bit position. -/
def packetEquiv (n d blocks b : ℕ) :
    FullPair (n+1) d × (Fin blocks × Fin b) ≃
      (((Fin (n+1) → Symbols d) × Bool) × Fin blocks) × ((Fin n → Bool) × Fin b) :=
  calc
    _ ≃ ((Fin (n+1) → Symbols d) × (Fin (n+1) → Bool)) × (Fin blocks × Fin b) :=
      (fullPairEquiv _ _).prodCongr (Equiv.refl _)
    _ ≃ ((Fin (n+1) → Symbols d) × (Bool × (Fin n → Bool))) × (Fin blocks × Fin b) :=
      ((Equiv.refl _).prodCongr (Fin.consEquiv (fun _ ↦ Bool)).symm).prodCongr (Equiv.refl _)
    _ ≃ _ := Equiv.prodAssoc .. |>.trans (by
      exact
        { toFun := fun ⟨box,⟨o,c⟩,k,j⟩ ↦ (((box,o),k),c,j)
          invFun := fun ⟨⟨⟨box,o⟩,k⟩,c,j⟩ ↦ (box,⟨o,c⟩,k,j)
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl })

/-- The labels sharing a coordinate with a specified source are precisely the
possible singleton destinations. -/
def singletons {a d : ℕ} (u : Label a d) : Finset (Label a d) :=
  Finset.univ.filter fun v ↦ ∃ i, v i = u i

/-- The union bound counts at most `a*d^(a-1)` singleton destinations per label. -/
theorem singleton_count {n d : ℕ} (u : Label (n+1) d) :
    (singletons u).card ≤ (n+1) * d^n := by
  let agree (i : Fin (n+1)) := Finset.univ.filter (fun v : Label (n+1) d ↦ v i = u i)
  have h (i : Fin (n+1)) : (agree i).card = d^n := by
    simpa only [agree, Fintype.piFinset_univ, Finset.card_univ, Fintype.card_fin,
      Nat.add_sub_cancel] using Fintype.card_filter_piFinset_const_eq_of_mem
        (Finset.univ : Finset (Fin d)) i (Finset.mem_univ (u i))
  have hu : singletons u = Finset.univ.biUnion agree := by ext v; simp [singletons, agree]
  rw [hu]
  exact Finset.card_biUnion_le.trans (by simp [h])

/-- Padded singleton wires occupy at most the fraction `(n+1)/d` of all padded wires. -/
theorem singleton_fraction (n d S : ℕ) (hd : 0 < d) :
    (∑ u : Label (n+1) d, ((S * (singletons u).card : ℕ) : ℝ)) ≤
      (S * (d^(n+1))^2 : ℕ) * ((n+1 : ℕ) / (d : ℝ)) := by
  have hc : Fintype.card (Label (n+1) d) = d^(n+1) := by simp [Label]
  calc
    _ ≤ ∑ _u : Label (n+1) d, ((S * ((n+1) * d^n) : ℕ) : ℝ) :=
      Finset.sum_le_sum fun u _ ↦ by exact_mod_cast Nat.mul_le_mul_left S (singleton_count u)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, hc, nsmul_eq_mul]
      push_cast
      rw [pow_succ (d : ℝ) n]
      field_simp [show (d : ℝ) ≠ 0 by exact_mod_cast hd.ne']

/-- If each packet edge is charged to its unique coordinate and the singleton and
selector budgets are bounded as in Section 8.2, a minimizing coordinate satisfies (8.1). -/
theorem minimizing_coordinate {n : ℕ} (edge single : Fin (n+1) → ℝ) {P d η sel : ℝ}
    (hwidth : ∑ i, edge i ≤ 2 * Real.sqrt (n+1) * P)
    (hsingle : ∀ i, single i ≤ P * ((n+1)/d))
    (hsel : sel ≤ P * η) :
    ∃ i, (∀ j, edge i + single i ≤ edge j + single j) ∧
      edge i + single i + sel ≤ P * (2 / Real.sqrt (n+1) + (n+1)/d + η) := by
  obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ
    (fun i : Fin (n+1) ↦ edge i + single i) Finset.univ_nonempty
  refine ⟨i, fun j ↦ hi j (Finset.mem_univ _), ?_⟩
  have lower := Finset.sum_le_sum (s := Finset.univ) hi
  have upper := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hsingle j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one, Finset.sum_add_distrib] at lower upper
  have hs := Real.sq_sqrt (show 0 ≤ (n : ℝ) + 1 by positivity)
  have hroot : 0 < Real.sqrt ((n : ℝ)+1) := Real.sqrt_pos.mpr (by positivity)
  have hfirst : edge i + single i ≤ P*(2 / Real.sqrt (n+1) + (n+1)/d) := by
    apply (mul_le_mul_iff_right₀ (show (0 : ℝ) < n+1 by positivity)).mp
    calc
      _ ≤ _ := lower
      _ ≤ 2 * Real.sqrt (n+1) * P + (n+1)*(P*((n+1)/d)) := add_le_add hwidth upper
      _ = _ := by
        have hr : 2 * Real.sqrt (n+1) = (n+1) * (2 / Real.sqrt (n+1)) := by
          field_simp
          linarith only [hs]
        rw [hr]; ring
  linarith only [hfirst, hsel]

/-- Every antipodal pair meets both selected symbol groups of its binary packet. -/
theorem packet_meets_group {a d : ℕ} (p : FullPair a d) (i : Fin a) (s : Fin d) :
    let box := ((fullPairEquiv a d) p).1 i
    (s = box.val.1 ∨ s = box.val.2) ↔ s = p.val.1 i ∨ s = p.val.2 i := by
  dsimp [fullPairEquiv]
  rcases lt_or_gt_of_ne (p.property i) with h | h
  · simp [ordered,h]
  · simp [ordered,h.not_gt,or_comm]

end Cube

end BorderVNP
end Computability
end OAI
