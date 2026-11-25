import OAI.Optimization.LinearProgramming.Geometry.FrankWolfeDenominator

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace FWRAM

open Matrix
open scoped BigOperators Matrix

/-- Common bit bound for every partial matrix dot product and every partial energy sum
through all prescribed rounds. Here `B` bounds the encoding length of one matrix entry. -/
def fwGradientWidth (n B : ℕ) : ℕ :=
  3+(n+1)^3+4*(B*n^2 + 4*(fwRounds n+1)*(fwRounds n+2)*n)

private theorem prefix_to_finset {n k : ℕ} (h : k≤n) (f : Fin n → ℚ) :
    ∃ s : Finset (Fin n), (∑ j : Fin k, f (j.castLE h)) = ∑ j ∈ s, f j := by
  let e : Fin k ↪ Fin n := ⟨Fin.castLE h,fun _ _ hj => Fin.ext (congrArg (fun k : Fin n => k.val) hj)⟩
  refine ⟨Finset.univ.map e,?_⟩
  rw [Finset.sum_map]
  rfl

/-- A single polynomial width covers the two kinds of scalar arithmetic in the geometric
test. The matrix-product clauses include individual multiplications and every partial
addition in a scanned row. The energy clauses include each square and every prefix sum. -/
theorem fwGradient_bounds {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℚ) (hs : Qᵀ=Q) (he : Q*Q=Q)
    (i : Fin n) (B : ℕ) (hB : ∀ r j, RAM.ratBits (Q r j)≤B) (p : ℕ) (hp : p≤fwRounds n) :
    let z := fwIterate Q i p
    (∀ r j, RAM.ratBits (Q r j*z j) ≤ fwGradientWidth n B) ∧
    (∀ r : Fin n, ∀ k : ℕ, ∀ hk : k≤n,
      RAM.ratBits (∑ j : Fin k, Q r (j.castLE hk)*z (j.castLE hk)) ≤ fwGradientWidth n B) ∧
    (∀ j, RAM.ratBits (((Q *ᵥ z) j)^2) ≤ fwGradientWidth n B) ∧
    (∀ k : ℕ, ∀ hk : k≤n,
      RAM.ratBits (∑ j : Fin k, ((Q *ᵥ z) (j.castLE hk))^2) ≤ fwGradientWidth n B) := by
  let z := fwIterate Q i p
  let D := matrixDenominator Q
  let E := ∏ j, (z j).den
  let T := 4*(fwRounds n+1)*(fwRounds n+2)
  let X := B*n^2 + T*n
  have hd (r j : Fin n) : (Q r j).den ∣ D := den_dvd_matrixDenominator Q r j
  have hu (j : Fin n) : (z j).den ∣ E :=
    Finset.dvd_prod_of_mem (fun a => (z a).den) (Finset.mem_univ j)
  have hdp : 0<D := matrixDenominator_pos Q
  have hep : 0<E := Finset.prod_pos fun j _ => (z j).pos
  have hD : D ≤ 2^(B*n^2) := by
    simpa [D,pow_two,Nat.mul_assoc] using matrixDenominator_bound Q hB
  have hzden (j : Fin n) : (z j).den ≤ T := by
    by_cases hp0 : p=0
    · subst p
      change (fwLower (K:=ℚ) i j).den≤T
      have hT : 4≤T := by dsimp [T]; nlinarith
      by_cases h : j=i
      · have hd4 : (1/4:ℚ).den = 4 := calc
          _ = (4:ℚ)⁻¹.den := congrArg Rat.den (one_div (4:ℚ))
          _ = 4 := Rat.inv_natCast_den_of_pos (a:=4) (by decide)
        simpa only [fwLower,h,ite_true,hd4] using hT
      · simpa [fwLower,h] using (show (1:ℕ)≤T by omega)
    · have h := (fwArray_reduced_size Q i p (Nat.pos_of_ne_zero hp0) j).1
      rw [fwArray_correct] at h
      exact h.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 4 (by omega)) (by omega))
  have hE : E ≤ 2^(T*n) := calc
    _ ≤ ∏ _j : Fin n, (2:ℕ)^T := Finset.prod_le_prod fun j _ => (hzden j).trans T.lt_two_pow_self.le
    _ = _ := by simp [← pow_mul]
  have hDE : D*E ≤ 2^X := by
    dsimp [X]
    rw [pow_add]
    exact Nat.mul_le_mul hD hE
  have hbox := ((inLabelBox_iff i z).mp (fwIterate_mem Q i p)).1
  have hpartial (r : Fin n) (s : Finset (Fin n)) := fwIntermediateBounds Q hs he D E hd z hu hbox r s
  have hlin (r : Fin n) (s : Finset (Fin n)) :
      RAM.ratBits (∑ j ∈ s, Q r j*z j) ≤ fwGradientWidth n B := by
    have hb := fwBounded_ratBits (k:=2*X) (Nat.mul_pos hdp hep)
      (hDE.trans (Nat.pow_le_pow_right (by decide) (by omega))) (hpartial r s).1
    have hle : n ≤ (n+1)^3 := (Nat.le_succ n).trans (Nat.le_self_pow (by decide) _)
    change _ ≤ 3+(n+1)^3+4*X
    omega
  have henergy (s : Finset (Fin n)) :
      RAM.ratBits (∑ j ∈ s, ((Q *ᵥ z) j)^2) ≤ fwGradientWidth n B := by
    have hd2 : (D*E)^2 ≤ 2^(2*X) := by
      rw [mul_comm 2 X,pow_mul]
      exact Nat.pow_le_pow_left hDE 2
    have hh : FWBounded ((D*E)^2) ((n^3 : ℕ) : ℚ) (∑ j ∈ s, ((Q *ᵥ z) j)^2) := by
      simpa only [Nat.cast_pow, pow_two] using (hpartial i s).2.2
    have h := fwBounded_ratBits (by positivity : 0<(D*E)^2) hd2 hh
    have hle : n^3 ≤ (n+1)^3 := Nat.pow_le_pow_left (Nat.le_succ n) 3
    change _ ≤ 3+(n+1)^3+4*X
    omega
  refine ⟨?_,?_,?_,?_⟩
  · intro r j
    simpa using hlin r {j}
  · intro r k hk
    obtain ⟨s,eq⟩ := prefix_to_finset hk (fun j => Q r j*z j)
    exact eq ▸ hlin r s
  · intro j
    simpa using henergy {j}
  · intro k hk
    obtain ⟨s,eq⟩ := prefix_to_finset hk (fun j => ((Q *ᵥ z) j)^2)
    exact eq ▸ henergy s

end FWRAM
end Geometry
end LinearProgramming
end Optimization
end OAI
