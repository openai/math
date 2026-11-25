import OAI.Computability.NearSquareRoot.SynchronizedAuxiliaryLayout

/-! # Numeric addressing of the fifteen borrowing batches

The flat local address ranges through both Fourier halves. Primary positions
occupy the active interval; the remaining local positions enumerate physical
cells in row-major order, skipping that interval.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace SynchronizedBorrowing

/-- Raw physical rank of one occupied local cell. -/
def physicalRank (start v a r i flat : ℕ) : ℕ :=
  if flat < a then (start + i) * a + flat else
    let z := i * (2*r-a) + (flat-a)
    if z < start*a then z else z+v*a

/-- Invert the placement, returning the local fiber and both-halves address.
Unused physical cells have no local address. -/
def lookupRank (start v a r phys : ℕ) : Option (ℕ × ℕ) :=
  if start*a ≤ phys ∧ phys < (start+v)*a then some (phys/a-start,phys%a) else
    let z := if phys < start*a then phys else phys-v*a
    let c := 2*r-a
    if z < v*c then some (z/c,a+z%c) else none

theorem placement_rank {start v b a r : ℕ} (h : start+v ≤ b) (hv : v ≤ b/8)
    (hr : 2*r ≤ 8*a) (i : Fin v) (t : Fin a ⊕ Fin (2*r-a)) :
    (finProdFinEquiv (placement h hv hr (i,t))).val =
      physicalRank start v a r i.val (finSumFinEquiv t).val := by
  cases t with
  | inl t =>
    change t.val + a * (start+i.val) = physicalRank start v a r i.val t.val
    simp [physicalRank, t.isLt, Nat.add_comm, Nat.mul_comm]
  | inr t =>
    have ha : 0 < a := by have := t.isLt; omega
    let z := t.val + (2*r-a)*i.val
    change z%a + a*(if z/a < start then z/a else z/a+v) = physicalRank start v a r i.val (a+t.val)
    have hz : i.val*(2*r-a)+((a+t.val)-a) = z := by simp [z, Nat.add_comm, Nat.mul_comm]
    have ht : ¬ a+t.val < a := by omega
    simp only [physicalRank, ite_eq_right ht, hz]
    have hcmp : z/a < start ↔ z < start*a := Nat.div_lt_iff_lt_mul ha
    have hrem := Nat.div_add_mod z a
    by_cases H : z < start*a <;> simp [H, hcmp, Nat.mul_add, Nat.mul_comm v a] <;> omega

theorem batchPlacement_rank {a r : ℕ} (b : ℕ) (j : Fin 15) (hr : 2*r ≤ 8*a)
    (har : a ≤ r) (i : Fin (size b j)) (x : Fin r ⊕ Fin r) :
    (finProdFinEquiv (batchPlacement b j hr (i, ShortFourier.auxiliaryLayout har x))).val =
      physicalRank (first b j) (size b j) a r i.val (finSumFinEquiv x).val := by
  exact (placement_rank (batchFits b j) (show size b j ≤ b/8 from min_le_left _ _) hr i
    (ShortFourier.auxiliaryLayout har x)).trans (by simp [ShortFourier.auxiliaryLayout])

private theorem grouped_div {i t n : ℕ} (ht : t < n) : (i*n+t)/n = i := by
  rw [Nat.mul_comm i n, Nat.mul_add_div (Nat.zero_lt_of_lt ht), Nat.div_eq_of_lt ht, Nat.add_zero]

private theorem grouped_mod {i t n : ℕ} (ht : t < n) : (i*n+t)%n = t := by
  simp [Nat.add_comm (i*n), Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]

private theorem grouped_lt {i t v n : ℕ} (hi : i < v) (ht : t < n) : i*n+t < v*n := by
  calc
    i*n+t < (i+1)*n := by rw [Nat.add_mul, one_mul]; omega
    _ ≤ v*n := Nat.mul_le_mul_right n hi

theorem lookup_physicalRank {start v a r i flat : ℕ} (_ha : 0 < a) (har : a ≤ r)
    (hi : i < v) (hf : flat < 2*r) :
    lookupRank start v a r (physicalRank start v a r i flat) = some (i,flat) := by
  by_cases h : flat < a
  · have h₀ : start*a ≤ (start+i)*a+flat := by rw [Nat.add_mul]; omega
    have h₁ := grouped_lt (show start+i < start+v by omega) h
    simp [physicalRank, h, lookupRank, h₀, h₁, grouped_div h, grouped_mod h]
  · let c := 2*r-a
    let z := i*c+(flat-a)
    have h₀ : flat-a < c := by dsimp [c]; omega
    have h₁ : z < v*c := grouped_lt hi h₀
    have hd : z/c = i := grouped_div h₀
    have hm : z%c = flat-a := grouped_mod h₀
    have hflat : a+(flat-a) = flat := by omega
    rw [physicalRank, ite_eq_right h]
    change lookupRank start v a r (if z<start*a then z else z+v*a) = _
    by_cases he : z < start*a
    · simp [he, lookupRank, Nat.not_le.mpr he, ← show c = 2*r-a from rfl, h₁, hd, hm, hflat]
    · have H : (start+v)*a ≤ z+v*a := by rw [Nat.add_mul]; omega
      have H' : ¬ z+v*a < start*a := by omega
      simp [he, lookupRank, Nat.not_lt.mpr H, H', ← show c = 2*r-a from rfl, h₁, hd, hm, hflat]

/-- Every successful physical query is in bounds and reproduces this address. -/
theorem physical_lookupRank {start v a r i flat phys : ℕ} (ha : 0 < a) (har : a ≤ r)
    (h : lookupRank start v a r phys = some (i,flat)) :
    i < v ∧ flat < 2*r ∧ physicalRank start v a r i flat = phys := by
  by_cases hactive : start*a ≤ phys ∧ phys < (start+v)*a
  · simp only [lookupRank, hactive] at h
    obtain ⟨rfl, rfl⟩ := h
    have h₀ : start ≤ phys/a := (Nat.le_div_iff_mul_le ha).mpr hactive.1
    have h₁ : phys/a < start+v := (Nat.div_lt_iff_lt_mul ha).mpr hactive.2
    have hm := Nat.mod_lt phys ha
    have he : start + (phys/a-start) = phys/a := by omega
    refine ⟨by omega, by omega, ?_⟩
    simpa [physicalRank, hm, he, Nat.mul_comm] using Nat.div_add_mod phys a
  · let z := if phys < start*a then phys else phys-v*a
    let c := 2*r-a
    have hc : 0 < c := by dsimp [c]; omega
    change (if _ then _ else _) = _ at h
    rw [ite_eq_right hactive] at h
    change (if z<v*c then some (z/c,a+z%c) else none) = some (i,flat) at h
    split at h
    next hbound =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      have hi : z/c < v := (Nat.div_lt_iff_lt_mul hc).mpr hbound
      have hm := Nat.mod_lt z hc
      have hflat : a+z%c < 2*r := by dsimp [c] at *; omega
      refine ⟨hi,hflat,?_⟩
      have hnot : ¬ a+z%c < a := by omega
      simp only [physicalRank, ite_eq_right hnot, Nat.add_sub_cancel_left]
      change (if z/c*c+z%c < start*a then z/c*c+z%c else z/c*c+z%c+v*a) = phys
      rw [Nat.div_add_mod']
      by_cases he : phys < start*a
      · simp [z,he]
      · have hafter : (start+v)*a ≤ phys := by omega
        rw [Nat.add_mul] at hafter
        have hcmp : ¬ phys-v*a < start*a := by omega
        simp [z, he, hcmp]
        omega
    next => simp at h

theorem lookupRank_iff {start v a r i flat phys : ℕ} (ha : 0 < a) (har : a ≤ r) :
    lookupRank start v a r phys = some (i,flat) ↔
      i < v ∧ flat < 2*r ∧ physicalRank start v a r i flat = phys := by
  refine ⟨physical_lookupRank ha har, ?_⟩
  rintro ⟨hi,hf,rfl⟩
  exact lookup_physicalRank ha har hi hf

end SynchronizedBorrowing

end NearSquareRoot
end Computability
end OAI
