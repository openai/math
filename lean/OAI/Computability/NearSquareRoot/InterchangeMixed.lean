import OAI.Computability.NearSquareRoot.InterchangeFrameBody
import OAI.Computability.NearSquareRoot.InterchangeRequestHeader
import OAI.Computability.NearSquareRoot.InterchangeBatchFrame
import OAI.Computability.NearSquareRoot.InterchangeSpectralFibre

/-! # Combining the small-row and full-volume child ledgers -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeFrame

open IntegerMultiplication.Code IntegerMultiplication.Strip IntegerMultiplication.Strip.Dims
  IntegerMultiplication.Adic IntegerMultiplication.Loom NearSquareRoot.InterchangeAddress

variable {I J : Type} {b n : ℕ} {r : Regime I} {l : I → ℕ}

/-- The exact row geometry and number of calls in one of the two phases. -/
def Phase (valid : I → Request b → Prop) (N : I → ℕ) (limit : ℕ)
    (i : I) (calls : List (Request b)) : Prop :=
  calls.length ≤ limit ∧ ∀ a ∈ calls, valid i a ∧ a.rows.count = N i

/-- The recurrence uses all calls with their actual row counts, including any repetitions. -/
def Mixed (valid : I → Request b → Prop) (N : I → ℕ) (cost : ℝ)
    (i : I) (calls : List (Request b)) : Prop :=
  (∀ a ∈ calls, valid i a ∧ a.rows.count ≤ N i) ∧
    (calls.map fun a => (a.rows.count : ℝ)).sum ≤ cost * N i

private theorem rows_sum {a : ℕ} (xs : List (Request b)) (h : ∀ y ∈ xs, y.rows.count = a) :
    (xs.map fun y => (y.rows.count : ℝ)).sum = xs.length * a := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add_one,add_mul,one_mul,
      h _ List.mem_cons_self,ih (fun y hmem => h _ (List.mem_cons_of_mem _ hmem))]
    ring

/-- Merge the two phase charges at the exact padded-volume ratio `group/b`. -/
theorem merge_ledgers {small N : I → ℕ} {s g c : ℕ} {valid : I → Request b → Prop}
    (hb : 0 < b) (hs : ∀ i, small i ≤ N i) (ratio : ∀ i, b * small i ≤ g * N i)
    (i : I) (x y : List (Request b)) (hx : Phase valid small c i x) (hy : Phase valid N s i y) :
    Mixed valid N (((c*g : ℕ):ℝ)/b + s) i (x++y) := by
  refine ⟨fun a h => (List.mem_append.mp h).elim
    (fun t => ⟨(hx.2 _ t).1,(hx.2 _ t).2.le.trans (hs i)⟩)
    (fun t => ⟨(hy.2 _ t).1,(hy.2 _ t).2.le⟩),?_⟩
  rw [List.map_append,List.sum_append,rows_sum x (fun a h => (hx.2 a h).2),
    rows_sum y (fun a h => (hy.2 a h).2),add_mul]
  apply add_le_add _ (mul_le_mul_of_nonneg_right (by exact_mod_cast hy.1) (by positivity))
  have scale : (b:ℝ)*small i ≤ g*N i := by exact_mod_cast ratio i
  calc
    _ ≤ (c:ℝ)*small i := mul_le_mul_of_nonneg_right (by exact_mod_cast hx.1) (by positivity)
    _ ≤ (↑(c*g : ℕ):ℝ)/b * N i := by
      rw [div_mul_eq_mul_div,le_div_iff₀ (by exact_mod_cast hb),Nat.cast_mul]
      calc
        _ = c * ((b:ℝ)*small i) := by ring
        _ ≤ c * ((g:ℝ)*N i) := mul_le_mul_of_nonneg_left scale (by positivity)
        _ = _ := by ring

/-- Use the actual monitored docket as the ledger of a framed phase. -/
theorem monitored {s : I → Type} {rows : (i:I) → Series (s i)} (valid : I → Request b → Prop)
    (N : I → ℕ) (limit : ℕ) (good : I → Tree → Prop) (op : (i : I) → s i → s i)
    {zone : I → Request b → Prop}
    (child : ∀ i a, zone i a → valid i a ∧ a.rows.count = N i)
    (run : ∀ v : (i:I) → s i → Tree, Manifest _ l v → (∀ i a, good i (v i a)) →
      Hopto (Request.job b) r (fun i => (rows i).count) l zone limit
        (together r.header (stackRun rows v)) (stackRun rows fun i => v i ∘ op i)) :
    Program (Request.job b) r l (Phase valid N limit) good rows op := by
  intro v hv hg
  obtain ⟨uses,legal,budget,work⟩ := (run v hv hg).safe
  exact ⟨uses,fun i => ⟨by exact_mod_cast budget i,fun a h => child i a (legal i a h)⟩,work⟩

end InterchangeFrame

end NearSquareRoot
end Computability
end OAI
