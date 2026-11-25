import OAI.Combinatorics.Sunflower.CorrectionSpec

/-! # One recursive step of the binary equality filter

The first input block preserves a shared direction and runs the smaller filter on the
pair names in that direction. The second block removes the direction left by a mismatch.
-/

open scoped Classical BigOperators
open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor

namespace OAI
namespace Combinatorics
namespace Sunflower

noncomputable section

open Binary Control

variable {I : Type*} [Fintype I]

/-- A promised equality test need only specify its values on controls constant on
each of its two designated sets of sites. -/
def EqualityMaps (P T : Finset I) (A : Type) (R Q : Raw.{0} I ℂ) : Prop :=
  ∃ M : Map (fun _ : I => A) R.Leg Q.Leg, ∀ x y (c : I → A),
    (∀ i ∈ P, c i = x) → (∀ i ∈ T, c i = y) → ∀ o,
      eval M c R.coeff o = if x = y then Q.coeff o else 0

private def readDir {K : Finset I} {b : ℕ} (i : I)
    (a : MaskLeg K (Direction (b+1)) i) : Direction (b+1) :=
  if h : i ∈ K then a h else Classical.choice inferInstance

private def matchMap (K : Finset I) {b : ℕ} {R Q : Raw.{0} I ℂ}
    (V : Raw.{0} I ℂ) (M : Map (fun _ : I => Word b) R.Leg Q.Leg) :
    let D := Raw.maskDiagonal ℂ K (Direction (b+1))
    Map (fun _ : I => Word (b+1)) (R.mul (V.mul D)).Leg (Q.mul (V.mul D)).Leg :=
  fun i c o a => M i (pairName (readDir i o.2.2) c) o.1 a.1 *
    (if a.2 = o.2 then 1 else 0)

private theorem matchMap_eval {P T : Finset I} {b : ℕ} {R Q : Raw.{0} I ℂ}
    (V : Raw.{0} I ℂ) (M : Map (fun _ : I => Word b) R.Leg Q.Leg)
    (hM : ∀ x y (c : I → Word b), (∀ i ∈ P, c i = x) → (∀ i ∈ T, c i = y) → ∀ o,
      eval M c R.coeff o = if x = y then Q.coeff o else 0)
    (x y : Word (b+1)) (c : I → Word (b+1))
    (hcP : ∀ i ∈ P, c i = x) (hcT : ∀ i ∈ T, c i = y) :
    let K := P ∪ T
    let D := Raw.maskDiagonal ℂ K (Direction (b+1))
    ∀ o : ∀ i, (Q.mul (V.mul D)).Leg i,
      eval (matchMap K V M) c (R.mul (V.mul D)).coeff o =
        Q.coeff (fun i => (o i).1) * V.coeff (fun i => (o i).2.1) *
        ∑ p : Direction (b+1), if pairName p x = pairName p y then
          (if (fun i => (o i).2.2) = (fun _ _ => p) then 1 else 0) else 0 := by
  classical
  intro K D o
  let dir (i : I) := readDir (K := K) i (o i).2.2
  let names (i : I) := pairName (dir i) (c i)
  let N := pre (fun i w => pairName (dir i) w) M
  have h :
      eval (matchMap K V M) c (R.mul (V.mul D)).coeff o =
        eval M names R.coeff (fun i => (o i).1) *
          (V.coeff (fun i => (o i).2.1) * D.coeff (fun i => (o i).2.2)) := by
    calc
      _ = eval (prodMap N idMap) c (R.mul (V.mul D)).coeff o := by
        apply eval_congr_at
        intros
        rfl
      _ = _ := by
        change eval (prodMap N idMap) c
          (fun a => R.coeff (fun i => (a i).1) * (V.mul D).coeff (fun i => (a i).2)) o = _
        erw [eval_prodMap N idMap c R.coeff (V.mul D).coeff o, eval_idMap]
        rfl
  rw [h]
  dsimp only [D, Raw.maskDiagonal, Crossing.basisTensor]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hp : (fun i => (o i).2.2) = (fun _ _ => p)
  · have hd (i) (hi : i ∈ K) : dir i = p := by
      simp [dir, readDir, hi, congrFun hp i]
    have hP (i) (hi : i ∈ P) : names i = pairName p x := by
      simp [names, hd i (Finset.mem_union_left T hi), hcP i hi]
    have hT (i) (hi : i ∈ T) : names i = pairName p y := by
      simp [names, hd i (Finset.mem_union_right P hi), hcT i hi]
    rw [hM _ _ names hP hT]
    by_cases hxy : pairName p x = pairName p y <;> simp [hp, hxy]
  · by_cases hn : pairName p x = pairName p y
    all_goals simp only [hn, ↓reduceIte]
    all_goals repeat' split
    all_goals first | contradiction | simp
    exact Or.inr (ite_eq_right hp)

/-- Zero-bit labels are all equal, so the scalar identity is the starting filter. -/
theorem equalityMaps_one (P T : Finset I) :
    EqualityMaps P T (Word 0) (Raw.one I ℂ) (Raw.one I ℂ) := by
  refine ⟨idMap, fun x y c _ _ o => ?_⟩
  simp [Subsingleton.elim x y]

/-- A direct sum runs the smaller filter in each matching direction and
subtracts its unique erroneous output on unequal inputs. -/
theorem filter_step_maps (j : I) {P T : Finset I} {b : ℕ} {R Q U V : Raw.{0} I ℂ}
    (hM : EqualityMaps P T (Word b) R Q) (hC : CorrectionMaps P T b U V) :
    let D := Raw.maskDiagonal ℂ (P ∪ T) (Direction (b+1))
    EqualityMaps P T (Word (b+1)) ((R.mul (V.mul D)).add (Q.mul U)) (Q.mul (V.mul D)) := by
  classical
  intro D
  obtain ⟨M, hM⟩ := hM
  obtain ⟨C, hC⟩ := hC
  let L := matchMap (P ∪ T) V M
  let N := prodMap (idMap (A := Q.Leg)) C
  refine ⟨diffMap j L N, fun x y c hcP hcT o => ?_⟩
  erw [eval_diffMap j L N c (R.mul (V.mul D)).coeff (Q.mul U).coeff o]
  rw [show eval L c (R.mul (V.mul D)).coeff o = _ from
    matchMap_eval V M (fun a d e h1 h2 z => by
      have h := hM a d e h1 h2 z
      by_cases h' : a = d <;> simpa [h'] using h) x y c hcP hcT o]
  change _ - eval (prodMap (idMap (A := Q.Leg)) C) c
    (fun a => Q.coeff (fun i => (a i).1) * U.coeff (fun i => (a i).2)) o = _
  erw [eval_prodMap (idMap (A := Q.Leg)) C c Q.coeff U.coeff o, eval_idMap, hC x y c hcP hcT]
  by_cases he : x = y
  · subst y
    have hn (p : Direction (b+1)) : p.val ≠ 0 := p.property
    simp only [word_add_self, hn, ↓reduceIte, Finset.sum_const_zero, mul_zero, sub_zero]
    dsimp only [Raw.mul, D, Raw.maskDiagonal, Crossing.basisTensor]
    rw [← mul_assoc]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    split
    · exact ite_eq_left ‹_›
    · exact ite_eq_right ‹_›

  · simp only [pairName_eq_iff, he, false_or, ite_false]
    ring

end
end Sunflower
end Combinatorics
end OAI
