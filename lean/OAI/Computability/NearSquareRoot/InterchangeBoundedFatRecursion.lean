import OAI.Computability.NearSquareRoot.InterchangeBQuestMixedBranch
import OAI.Computability.NearSquareRoot.InterchangeBQuestMixedResolve
import OAI.Computability.NearSquareRoot.InterchangeCenterThick

/-! # Time and space of the recursive interchange on thick requests

The physical center selects a thickness exponent before its requests are
restricted. After restricting both child lists, one tied program uses the
width test to stop at the bounded-width leaf. On the recursive branch the
small children leave room for a whole row and the full children leave room
for the remaining descriptors.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeAddress.Request

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Loom NearSquareRoot.InterchangeSpace Space

open private sum_volume from OAI.Computability.NearSquareRoot.InterchangeFatRecursion

variable {b : ℕ}

/-- A common recursive tape command has quasilinear running time in the
record volume and linear space. Multiplicities in each call ledger count
toward the time bound. -/
theorem close_bounded_fat_recursion (valid : Request b → Prop) (hb : 2 ≤ b)
    (ok : ∀ a, valid a → Admissible a) (positive : ∀ a, valid a → 0 < a.width)
    (data : Manifest _ (fun a : Subtype valid => a.val.recordWidth) (fun a => a.val.contents))
    (m n : ℕ) (α θ : ℝ) (hm : 1 < m) (hmn : m ≤ n) (hα : 0 ≤ α) (hθ0 : 0 ≤ θ)
    (hθ : θ < (m : ℝ) ^ α)
    (step : ∃ (small full : Internal valid n → List (Request b)) (park : Internal valid n → ℕ) (H : ℕ),
      (∀ u, stepAccount valid n θ u.val.val (small u ++ full u)) ∧
      (∀ u y, y ∈ small u → 3 * y.rows.count ≤ 2 * u.val.val.rows.count) ∧
      (∀ u, park u ≤ H * (Nat.log 2 u.val.val.recordVolume + 1)) ∧
      CenterBody (regime internalRequest) (fun u => u.val.val.rows.count)
        (fun u => u.val.val.recordWidth) (job b) small full park ((job b).issue ∘ internalRequest)
        ((job b).reply ∘ internalRequest)) :
    ∃ k : ℕ, BoundedTask
      (fun x : ThickRequest valid k => ⌈(x.val.recordVolume : ℝ) * (x.val.width : ℝ) ^ α⌉₊)
      (fun x => x.val.recordVolume) (fun x => (job b).issue x.val) (fun x => (job b).reply x.val) := by
  classical
  obtain ⟨small, full, park, H, account, shrinks, header, center⟩ := step
  obtain ⟨k, s, f, hs, hf, body⟩ := center_on_thick valid hb ok n θ small full park H account header center
  let X := ThickRequest valid k
  let xs (x : X) := x.val
  let width (x : X) := (xs x).width
  let V (x : X) := (xs x).recordVolume
  let S := branch_ledger xs n s
  let F := branch_ledger xs n f
  let children (x : X) := S x ++ F x
  have adm (x : X) := ok (xs x) x.property.1
  have stored : Manifest _ (fun x : X => (xs x).recordWidth) (fun x => (xs x).contents) :=
    ⟨data.size.choose, fun x => data.size.choose_spec ⟨x.val, x.property.1⟩⟩
  have dispatch := branch_mixed xs n hb adm stored s f body
  have law (x : X) : stepAccount valid n θ (xs x) ((children x).map xs) := by
    by_cases h : n < (xs x).width
    · let q : ThickInternal valid n k := ⟨x, h⟩
      have image : (children x).map xs = small (fromThick q) ++ full (fromThick q) := by
        change ((branch_ledger xs n s x ++ branch_ledger xs n f x).map xs) = _
        simp only [branch_ledger, h, ↓reduceDIte, List.map_append]
        exact congrArg₂ List.append (hs q) (hf q)
      rw [image]
      exact account (fromThick q)
    · have empty : children x = [] := by simp [children, S, F, branch_ledger, h]
      rw [empty]
      refine ⟨by simp, ?_⟩
      simpa using mul_nonneg hθ0 (Nat.cast_nonneg (xs x).rows.count)
  have spec (x y : X) (hy : y ∈ children x) :=
    (law x).1 (xs y) (List.mem_map_of_mem hy)
  have childWidth (x y : X) (hy : y ∈ children x) : width y * m ≤ width x := by
    dsimp [width]
    rw [(spec x y hy).2.1]
    exact (Nat.mul_le_mul_left _ hmn).trans (lanes_mul_le _ _)
  have total (x : X) : ((children x).map (fun y => (V y : ℝ))).sum ≤ θ * V x := by
    simpa only [List.map_map, Function.comp_def] using sum_volume valid (law x)
  obtain ⟨ε, hε, slack⟩ := interchange_fare_slack width V children m α θ hm hα hθ childWidth total
  let fare (x : X) := (V x : ℝ) * (width x : ℝ) ^ α
  have powBound (x : X) : 2 ^ width x ≤ V x := by
    calc
      _ ≤ 2 ^ (xs x).digits := Nat.pow_le_pow_right (by decide) (by dsimp [digits, width]; omega)
      _ ≤ (xs x).rows.count := pow_digits_le _ hb (adm x)
      _ ≤ V x := rows_le_recordVolume _
  have wp (x : X) : 0 < width x := positive _ x.property.1
  refine ⟨k, Mixed.resolve (job := thickJob valid k) dispatch width fare ε hε powBound ?_ slack ?_ ?_ ?_⟩
  · intro x
    exact le_mul_of_one_le_right (Nat.cast_nonneg _) (Real.one_le_rpow (by exact_mod_cast wp x) hα)
  · intro x y hy
    exact (by simpa using Nat.mul_lt_mul_of_pos_left hm (wp y) : width y < width y*m).trans_le
      (childWidth x y hy)
  · intro x y hy
    have hw := (spec x y (List.mem_append_left _ hy)).2.2.1
    have count : 3 * (xs y).rows.count ≤ 2 * (xs x).rows.count := by
      by_cases h : n < (xs x).width
      · let q : ThickInternal valid n k := ⟨x,h⟩
        have member : y ∈ s q := by simpa only [branch_ledger, h, ↓reduceDIte] using hy
        apply shrinks (fromThick q)
        rw [← hs q]
        exact List.mem_map_of_mem member
      · simp [branch_ledger,h] at hy
    simpa only [V, recordVolume, hw, ← Nat.mul_assoc] using
      Nat.mul_le_mul_right ((xs x).recordWidth + 1) count
  · intro x y hy
    have q := (spec x y (List.mem_append_right _ hy)).2.2
    dsimp only [V, recordVolume]
    rw [q.1]
    exact Nat.mul_le_mul_right _ q.2

end InterchangeAddress.Request

end NearSquareRoot
end Computability
end OAI
