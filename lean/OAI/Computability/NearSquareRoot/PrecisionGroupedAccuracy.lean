import OAI.Computability.NearSquareRoot.PrecisionPieceEstimate
import OAI.Computability.NearSquareRoot.PhysicalWalshGrouped

/-! # Numerical correctness of the physical grouped Walsh pass

The original records enter the same zero-padded root consumed by the
interpreter. Truncation is a contraction and the terminal pair pass is
unitary, so the two rounding budgets add in the original finite array.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.Pieces
open Matrix Filter IntegerMultiplication KernelPass PhysicalWalshNode FlatWalshNode FixedPoint

noncomputable section

private theorem pad_norm {k m : ℕ} (h : 2^k ≤ m) (x : ℕ → Record k) :
    ‖atWidth m (decoded (fractionBits k) (zeroAfter (2^k) x))‖ =
      ‖recordArray (fun j : Fin (2^k) => x j.val)‖ := by
  obtain ⟨e,rfl⟩ := Nat.exists_eq_add_of_le h
  let v := recordArray (fun j : Fin (2^k) => x j.val)
  have eq : atWidth (2^k+e) (decoded (fractionBits k) (zeroAfter (2^k) x)) =
      WithLp.toLp 2 (Padding.extend (2^k+e) (fun j => v j)) := by
    apply PiLp.ext
    intro j
    change Grid.meaning _ _ (if j.val < 2^k then x j.val else 0) = _
    by_cases hj : j.val < 2^k
    · simp [Padding.extend,hj,v,recordArray,FixedPoint.value]
    · simp [Padding.extend,hj,Padding.meaning_zero]
  rw [eq]
  exact Padding.norm_extend _ _ v

private theorem budget {k : ℕ} (hk : 1 ≤ k) :
    1/(2:ℝ)^(55*k)+1/(2:ℝ)^(67*k) ≤ 1/(2:ℝ)^(50*k) := by
  have d (m : ℕ) (hm : 50*k+1 ≤ m) : 1/(2:ℝ)^m ≤ 1/(2:ℝ)^(50*k+1) :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) hm)
  refine (add_le_add (d _ (by omega)) (d _ (by omega))).trans_eq ?_
  rw [pow_succ]
  field_simp
  ring

/-- Pointwise numerical certificate at address width `k`. -/
def GroupedAccurateAt {a W : ℕ} (ha : 1<a+1) (hw : 0<W) (plan : Plan (a+1) W W) (k : ℕ) : Prop :=
  ∀ (s : ℕ) (hs : s ≤ k), ∀ x : ℕ → Record k,
    ‖recordArray (fun j : Fin (2^k) => x j.val)‖ ≤ (2:ℝ)^(13*k) →
    (root k s x).Feasible hw plan ha ∧
    ‖recordArray (result hw plan k s x) - WithLp.toLp 2
      (BoxFin.flatWalsh (FlatWalshWindow.bits k s 0 (by omega)) *ᵥ
        (fun i => FixedPoint.value k (x i.val)))‖ ≤ 1/(2:ℝ)^(50*k)

theorem grouped_accurate_of_even {a W k : ℕ} (ha : 1<a+1) (hw : 0<W) (plan : Plan (a+1) W W)
    (hk : 1 ≤ k)
    (even : EvenAccurateAt ha hw plan k) :
    GroupedAccurateAt ha hw plan k := by
  intro s hs x hx
  let n := 2^k
  let m := extent (a+1) W k s
  have capacity : n ≤ m := by
    have h := Padding.total (a+1) hw hs
    exact (Nat.le_add_right _ _).trans_eq h
  let b := root k s x
  let u := decoded (fractionBits k) b.row
  let z := b.stage hw plan (b.pieces (a:=a) hw).length
  let zf := fun i : Fin n => z i.val
  let y := evenTarget s u
  have hn : ‖atWidth m u‖ = ‖recordArray (fun j : Fin n => x j.val)‖ := pad_norm capacity x
  obtain ⟨good,isom,err⟩ := even s hs b.row (hn.trans_le hx)
  have exactNorm : ‖atWidth n y‖ ≤ (2:ℝ)^(13*k) :=
    (Padding.norm_project capacity (atWidth m y)).trans ((isom.trans hn).trans_le hx)
  have prior : ‖recordArray zf - atWidth n y‖ ≤ 1/(2:ℝ)^(67*k) :=
    (Padding.project_error capacity (atWidth m (decoded (fractionBits k) z)) (atWidth m y)).trans err
  have guard : ‖recordArray zf‖ ≤ (2:ℝ)^(14*k) := by
    have unit : 1/(2:ℝ)^(67*k) ≤ 1 := (div_le_one (by positivity)).2 (one_le_pow₀ (by norm_num))
    calc
      _ ≤ ‖recordArray zf - atWidth n y‖ + ‖atWidth n y‖ := norm_le_norm_sub_add _ _
      _ ≤ 1+(2:ℝ)^(13*k) := add_le_add (prior.trans unit) exactNorm
      _ ≤ (2:ℝ)^(13*k+1) := by rw [pow_succ]; linarith [one_le_pow₀ (by norm_num : 1 ≤ (2:ℝ)) (n:=13*k)]
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
  have h := Odd.complete_error (a+1) W ha hw hs (componentBits k) u zf guard
    (e:=1/(2:ℝ)^(67*k)) (by rw [ideal_even _ _ ha hw]; exact prior)
  have onPrefix : (fun i : Fin n => u i.val) = (fun i => FixedPoint.value k (x i.val)) := by
    funext i
    change Grid.meaning _ _ (zeroAfter (2^k) x i.val) = _
    simp [zeroAfter,show i.val < 2^k from i.isLt]
  rw [onPrefix] at h
  exact ⟨good,h.trans (budget hk)⟩

theorem eventually_grouped_accurate {a W : ℕ} (ha : 1<a+1) (hw : 0<W) (plan : Plan (a+1) W W)
    (hp : Correct plan) : ∀ᶠ k : ℕ in atTop, GroupedAccurateAt ha hw plan k := by
  filter_upwards [eventually_even_accurate ha hw plan hp, eventually_ge_atTop (1:ℕ)] with k even hk
  exact grouped_accurate_of_even ha hw plan hk even

end
end PhysicalWalsh.Pieces

end NearSquareRoot
end Computability
end OAI
