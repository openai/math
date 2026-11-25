import OAI.Computability.NearSquareRoot.KernelPassRectFree
import OAI.Computability.NearSquareRoot.KernelPassRectCharged

/-! # A single restricted pencil from a signed rectangle decomposition

The label identity cancels every cross-label block. Source and destination
endpoint costs are charged only at the incident labels. A charged rectangle
uses one common bank per query.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPass.Rect

open Matrix Finset
open scoped BigOperators

variable {A : ℕ} {L W J F C : Type} [Fintype L] [Fintype W] [Fintype J] [Fintype F] [Fintype C]
variable [DecidableEq L] [DecidableEq W]

structure Support (L : Type) where
  sources : Finset L
  destinations : Finset L
  weight : Coefficient

def Support.coeff (r : Support L) (w v : L) : ℚ :=
  if v ∈ r.sources ∧ w ∈ r.destinations then value r.weight else 0

structure FreeData (A : ℕ) (L J : Type) extends Support L where
  source : L → Single A
  target : L → Single A
  middle : J → L → L → Single A
  middle_free : ∀ j w v, (middle j w v).calls = 0

structure ChargedData (A : ℕ) (L J : Type) extends Support L where
  input : J → L → Single A
  output : J → L → Single A
  common : J → Single A
  input_free : ∀ j v, (input j v).calls = 0
  output_free : ∀ j w, (output j w).calls = 0

abbrev Kernels (A : ℕ) (J L : Type) := (h : ℕ) → J → L → L → Mat A h

def FreeData.Factors (r : FreeData A L J) (H : Kernels A J L) : Prop :=
  ∀ h j w v, v ∈ r.sources → w ∈ r.destinations →
    oneRow ((r.target w).eval h) * oneRow ((r.middle j w v).eval h) * oneRow ((r.source v).eval h) =
      H h j w v

def ChargedData.Factors (r : ChargedData A L J) (H : Kernels A J L) : Prop :=
  ∀ h j w v, v ∈ r.sources → w ∈ r.destinations →
    oneRow ((r.output j w).eval h) * oneRow ((r.common j).eval h) * oneRow ((r.input j v).eval h) =
      H h j w v

/-- The pointwise coefficient of the pencil, applied on every label's own bank. -/
noncomputable def constantPart (B : W → W → Coefficient) : On A (L × W) (L × W) :=
  mixing (fun b a : L × W => if b.1 = a.1 then B b.2 a.2 else (0,0))

noncomputable def FreeData.plan (r : FreeData A L J) (B : J → W → W → Coefficient) :
    On A (L × W) (L × W) := free r.sources r.destinations r.weight B r.source r.target r.middle

noncomputable def ChargedData.plan (r : ChargedData A L J) (B : J → W → W → Coefficient) :
    On A (L × W) (L × W) := total fun j =>
      charged r.sources r.destinations r.weight (B j) (r.input j) (r.output j) (r.common j)

/-- The row numbering and the entire finite instruction list are shared by every width. -/
noncomputable def pencil (Frees : F → FreeData A L J) (Charged : C → ChargedData A L J)
    (B₀ : W → W → Coefficient) (B : J → W → W → Coefficient) : On A (L × W) (L × W) :=
  addPlan (constantPart B₀) (addPlan (total (fun r => (Frees r).plan B)) (total (fun r => (Charged r).plan B)))

omit [DecidableEq L] [DecidableEq W] in
theorem block_addPlan (p q : On A L W) (h : ℕ) :
    block (O := W) (I := L) (addPlan p q) h = block (O := W) (I := L) p h + block (O := W) (I := L) q h := by
  ext b a y x
  simp only [block, eval_addPlan, Matrix.add_apply]

omit [DecidableEq W] in
private theorem FreeData.block_plan (r : FreeData A L J) (H : Kernels A J L) (hr : r.Factors H)
    (B : J → W → W → Coefficient) (h : ℕ) (w v : L) (k l : W) :
    block (I := L × W) (O := L × W) (r.plan B) h (w,k) (v,l) =
      r.coeff w v • ∑ j, value (B j k l) • H h j w v := by
  rw [FreeData.plan, block_free]
  by_cases hmem : v ∈ r.sources ∧ w ∈ r.destinations
  · simp [Support.coeff, hmem, hr h _ w v hmem.1 hmem.2]
  · simp [Support.coeff, hmem]

private theorem ChargedData.block_plan (r : ChargedData A L J) (H : Kernels A J L) (hr : r.Factors H)
    (B : J → W → W → Coefficient) (h : ℕ) (w v : L) (k l : W) :
    block (I := L × W) (O := L × W) (r.plan B) h (w,k) (v,l) =
      r.coeff w v • ∑ j, value (B j k l) • H h j w v := by
  rw [ChargedData.plan, block_total]
  simp only [Matrix.sum_apply, block_charged]
  by_cases hmem : v ∈ r.sources ∧ w ∈ r.destinations
  · simp [Support.coeff, hmem, hr h _ w v hmem.1 hmem.2, Finset.smul_sum]
  · simp [Support.coeff, hmem]

/-- Each diagonal label carries the pencil and all cross-label operators cancel. -/
theorem block_pencil (Frees : F → FreeData A L J) (Charged : C → ChargedData A L J)
    (B₀ : W → W → Coefficient) (B : J → W → W → Coefficient) (H : Kernels A J L)
    (hfree : ∀ r, (Frees r).Factors H) (hpaid : ∀ r, (Charged r).Factors H)
    (hId : ∀ w v, (∑ r, (Frees r).coeff w v) + (∑ r, (Charged r).coeff w v) =
      if w = v then 1 else 0)
    (h : ℕ) (w v : L) (k l : W) :
    block (I := L × W) (O := L × W) (pencil Frees Charged B₀ B) h (w,k) (v,l) =
      if w = v then value (B₀ k l) • (1 : Mat A h) + ∑ j, value (B j k l) • H h j w v else 0 := by
  simp only [pencil, block_addPlan, block_total, constantPart, block_mixing,
    Matrix.add_apply, Matrix.sum_apply, Matrix.of_apply, FreeData.block_plan _ H (hfree _),
    ChargedData.block_plan _ H (hpaid _)]
  rw [← Finset.sum_smul, ← Finset.sum_smul, ← add_smul, hId]
  by_cases e : w = v <;> simp [e, value]

/-- Actual child count in each finite instruction list for the whole pencil. -/
theorem calls_pencil (Frees : F → FreeData A L J) (Charged : C → ChargedData A L J)
    (B₀ : W → W → Coefficient) (B : J → W → W → Coefficient) :
    (pencil Frees Charged B₀ B).calls =
      (∑ f, Fintype.card W * ((∑ w ∈ (Frees f).destinations, ((Frees f).target w).calls) +
        ∑ v ∈ (Frees f).sources, ((Frees f).source v).calls)) +
      ∑ c, ∑ j, Fintype.card W * ((Charged c).common j).calls := by
  simp [pencil, constantPart, calls_total, FreeData.plan, ChargedData.plan,
    calls_free _ _ _ _ _ _ _ (FreeData.middle_free _),
    calls_charged _ _ _ _ _ _ _ (ChargedData.input_free _ _) (ChargedData.output_free _ _),
    mixing, Plan.calls]

end KernelPass.Rect

end NearSquareRoot
end Computability
end OAI
