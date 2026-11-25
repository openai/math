import OAI.LinearAlgebra.MatrixExponent.Routing.Partitions
import Mathlib.Topology.Instances.Real.Lemmas
import OAI.LinearAlgebra.MatrixExponent.Prices.Finite
import OAI.LinearAlgebra.MatrixExponent.Prices.Fields

section
/-!
# A supporting slope for the displacement profile

Minimize the distance to the fixed set plus a small linear tilt. This
gives a supporting line of strictly negative slope at the chosen
radius without differentiating the distance to the moving fixed set.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Prices.Motion

open Filter Set
open scoped Topology

/-- Convexity at rational triples is enough for decreasing profiles. -/
def RationalSecants (R : ℝ → ℝ) : Prop :=
  ∀ a b c : ℚ, 0 < a → a < b → b < c →
    ((c : ℝ) - a) * R b ≤ ((c : ℝ) - b) * R a + ((b : ℝ) - a) * R c

theorem RationalSecants.real {R : ℝ → ℝ} (h : RationalSecants R)
    (hm : AntitoneOn R (Ioi 0)) {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c) :
    (c - a) * R b ≤ (c - b) * R a + (b - a) * R c := by
  obtain ⟨x, _, hx, lx⟩ := Real.exists_seq_rat_strictAnti_tendsto a
  obtain ⟨y, _, hy, ly⟩ := Real.exists_seq_rat_strictMono_tendsto b
  obtain ⟨z, _, hz, lz⟩ := Real.exists_seq_rat_strictAnti_tendsto c
  apply le_of_tendsto_of_tendsto ((lz.sub lx).mul_const (R b))
    (((lz.sub ly).mul_const (R a)).add ((ly.sub lx).mul_const (R c)))
  filter_upwards [lx.eventually_lt ly hab] with n hxy
  have hyz := (hy n).trans (hbc.trans (hz n))
  have hx0 := ha.trans (hx n)
  have hy0 := hx0.trans hxy
  have hc0 := (ha.trans hab).trans hbc
  have huv := h (x n) (y n) (z n) (by exact_mod_cast hx0)
    (by exact_mod_cast hxy) (by exact_mod_cast hyz)
  have h₁ := hm hy0 (ha.trans hab) (hy n).le
  have h₂ := hm ha hx0 (hx n).le
  have h₃ := hm hc0 (hc0.trans (hz n)) (hz n).le
  exact (mul_le_mul_of_nonneg_left h₁ (sub_nonneg.mpr (hxy.trans hyz).le)).trans
    (huv.trans (add_le_add (mul_le_mul_of_nonneg_left h₂ (sub_nonneg.mpr hyz.le))
      (mul_le_mul_of_nonneg_left h₃ (sub_nonneg.mpr hxy.le))))

/-- Uniform two-sided little-o estimate at the onset of displacement. -/
def Kink (R : ℝ → ℝ) (r k : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, |h| < δ →
    |R (r + h) - k * max (-h) 0| ≤ ε * |h|

private theorem kink_of_support {R : ℝ → ℝ} (h : RationalSecants R)
    (hm : AntitoneOn R (Ioi 0)) {a r c : ℝ} (ha : 0 < a) (har : a < r) (hc : 0 < c)
    (hs : ∀ x ∈ Ico a r, c * (r - x) ≤ R x) (hz : ∀ x, r ≤ x → R x = 0) :
    ∃ k, 0 < k ∧ Kink R r k := by
  let q (x : ℝ) := R x / (r - x)
  let S := q '' Ico a r
  have hn : S.Nonempty := ⟨_, a, ⟨le_rfl, har⟩, rfl⟩
  have hb : c ∈ lowerBounds S := by
    rintro _ ⟨x, hx, rfl⟩
    exact (le_div_iff₀ (sub_pos.mpr hx.2)).mpr (hs x hx)
  let k := sInf S
  refine ⟨k, hc.trans_le (le_csInf hn hb), fun ε hε => ?_⟩
  obtain ⟨_, ⟨x, hx, rfl⟩, he⟩ := exists_lt_of_csInf_lt hn (show k < k + ε by linarith)
  refine ⟨r - x, sub_pos.mpr hx.2, fun v hv => ?_⟩
  rcases lt_or_ge v 0 with hv' | hv'
  · have hl : x < r + v := by linarith [(abs_lt.mp hv).1]
    have hu : r + v < r := by linarith
    have hlow := csInf_le (show BddBelow S from ⟨c, hb⟩)
      (show q (r + v) ∈ S from ⟨r + v, ⟨hx.1.trans hl.le, hu⟩, rfl⟩)
    have hhi : q (r + v) ≤ q x := by
      apply (div_le_div_iff₀ (sub_pos.mpr hu) (sub_pos.mpr hx.2)).mpr
      have hd := h.real hm (ha.trans_le hx.1) hl hu
      rw [hz r le_rfl] at hd
      linarith only [hd]
    have lo := (le_div_iff₀ (sub_pos.mpr hu)).mp hlow
    have hi := (div_le_iff₀ (sub_pos.mpr hu)).mp (hhi.trans he.le)
    rw [abs_of_neg hv', max_eq_left (neg_nonneg.mpr hv'.le), abs_of_nonneg (by linarith)]
    linarith
  · rw [hz _ (by linarith), max_eq_right (neg_nonpos.mpr hv'), mul_zero, sub_zero, abs_zero]
    positivity

/-- Each radius t selects a profile R t vanishing from that radius on.
Its earlier values bound the change in the projection distance f. -/
theorem first_displacement {R : ℝ → ℝ → ℝ} {f : ℝ → ℝ} {a b M : ℝ}
    (ha : 0 < a) (hab : a < b) (hf : f b < f a)
    (hs : ∀ t ∈ Icc a b, RationalSecants (R t))
    (hm : ∀ t ∈ Icc a b, AntitoneOn (R t) (Ioi 0))
    (hz : ∀ t ∈ Icc a b, ∀ x, t ≤ x → R t x = 0)
    (hM : ∀ t ∈ Icc a b, R t (a / 2) ≤ M)
    (hp : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t →
      f t ≤ f s ∧ f s - f t ≤ R t s) :
    ∃ r ∈ Ioc a b, ∃ k : ℝ, 0 < k ∧ Kink (R r) r k := by
  let L := (|M| + 1) / (a / 2)
  have hL : 0 < L := by unfold L; positivity
  have bound {s t : ℝ} (hs' : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) :
      f s - f t ≤ L * (t - s) := by
    rcases hst.eq_or_lt with rfl | hst
    · simp
    have H := (hs t ht).real (hm t ht) (half_pos ha) (by linarith [hs'.1]) hst
    rw [hz t ht t le_rfl, mul_zero, add_zero] at H
    obtain ⟨h₁, h₂⟩ := hp s hs' t ht hst.le
    have h₃ := mul_le_mul (show a / 2 ≤ t - a / 2 by linarith [ht.1]) h₂
      (sub_nonneg.mpr h₁) (show 0 ≤ t - a / 2 by linarith [ht.1])
    have h₄ := mul_le_mul_of_nonneg_left ((hM t ht).trans
      ((le_abs_self M).trans (le_add_of_nonneg_right zero_le_one))) (sub_nonneg.mpr hst.le)
    unfold L
    rw [div_mul_eq_mul_div, le_div_iff₀ (half_pos ha)]
    linarith only [H, h₃, h₄]
  have cont : ContinuousOn f (Icc a b) := by
    apply Metric.continuousOn_iff.mpr
    intro t ht ε hε
    refine ⟨ε / L, div_pos hε hL, fun s hs' hst => ?_⟩
    rw [Real.dist_eq, lt_div_iff₀ hL] at hst
    rw [Real.dist_eq]
    rcases le_total s t with h | h
    · rw [abs_of_nonpos (sub_nonpos.mpr h)] at hst
      rw [abs_of_nonneg (sub_nonneg.mpr (hp s hs' t ht h).1)]
      linarith only [bound hs' ht h, hst]
    · rw [abs_of_nonneg (sub_nonneg.mpr h)] at hst
      rw [abs_of_nonpos (sub_nonpos.mpr (hp t ht s hs' h).1)]
      linarith only [bound ht hs' h, hst]
  let c := (f a - f b) / (2 * (b - a))
  have hc : 0 < c := div_pos (by linarith) (by linarith)
  have he : c * (2 * (b - a)) = f a - f b := div_mul_cancel₀ _ (by linarith)
  obtain ⟨r, hr, hr'⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab.le)
    (show ContinuousOn (fun t => f t + c * t) _ from cont.add (continuousOn_const.mul continuousOn_id))
  have har : a < r := by
    rcases hr.1.eq_or_lt with rfl | h
    · have h : f a + c * a ≤ f b + c * b := hr' ⟨hab.le, le_rfl⟩
      linarith
    · exact h
  refine ⟨r, ⟨har, hr.2⟩, kink_of_support (hs r hr) (hm r hr) ha har hc ?_ (hz r hr)⟩
  intro x hx
  have hx' : x ∈ Icc a b := ⟨hx.1, hx.2.le.trans hr.2⟩
  have hl : f r + c * r ≤ f x + c * x := hr' hx'
  linarith only [hl, (hp x hx' r hr hx.2.le).2]

end OAI.LinearAlgebra.MatrixExponent.Prices.Motion
end

/-!
# Finite realizations of geodesic expressions

Every finite set of expressions can be realized at one spectral point.
When a missing expression is added, all previously correct expressions
keep their original sites and prices.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing
open Spectral Tensor

def SpectralComparison (K : Type) [Field K] : Prop :=
  ∀ (S : Type) [Fintype S] [DecidableEq S] [Nonempty S] (f : Tensor K S →+* ℝ),
    Monotone f → ∀ (a m b : S) (u : Fraction), Between f a m b u →
      ∀ z : S, Tensor.dist f m z ^ 2 ≤ (1 - u.val) * Tensor.dist f a z ^ 2 +
        u.val * Tensor.dist f b z ^ 2 - u.val * (1 - u.val) * Tensor.dist f a b ^ 2

variable {K S : Type} [Field K] [Fintype S] [DecidableEq S] [Nonempty S]

structure TermModel (f : Tensor K S →+* ℝ) where
  Site : Type
  [finiteSites : Fintype Site]
  [decEq : DecidableEq Site]
  [inh : Nonempty Site]
  g : Tensor K Site →+* ℝ
  mono : Monotone g
  point : Term S → Site
  initial : ∀ A, g (place (point ∘ Term.mark) A) = f A

attribute [instance] TermModel.finiteSites TermModel.decEq TermModel.inh

namespace TermModel
variable {f : Tensor K S →+* ℝ}

def start (hf : Monotone f) : TermModel f where
  Site := S
  g := f
  mono := hf
  point
    | .mark i => i
    | .seg .. => Classical.arbitrary S
  initial A := congrArg f (place_id A)

def Valid (M : TermModel f) : Term S → Prop := Fits (values 1 M.g) M.point

omit [Nonempty S] in
theorem valid_iff (M : TermModel f) (t : Fraction) (a b : Term S) :
    M.Valid (.seg t a b) ↔ M.Valid a ∧ M.Valid b ∧
      Between M.g (M.point a) (M.point (.seg t a b)) (M.point b) t := by
  simp only [Valid, Fits, AtFraction, Between, gap, values, Tensor.dist, one_mul]

omit [Nonempty S] in
private theorem append (M : TermModel f) (t : Fraction) (a b : Term S)
    (ha : M.Valid a) (hb : M.Valid b) :
    ∃ N : TermModel f, N.Valid (.seg t a b) ∧ ∀ c, M.Valid c → N.Valid c := by
  classical
  let d := Term.seg t a b
  by_cases h : M.Valid d
  · exact ⟨M, h, fun _ h => h⟩
  obtain ⟨g, hg, he, hd, _⟩ := geodesic M.g M.mono
    (fun _ : Unit => M.point a) (fun _ => M.point b) t.2.1 t.2.2
  let p (c : Term S) : M.Site ⊕ Unit := if c = d then .inr () else .inl (M.point c)
  have pm : p ∘ Term.mark = Sum.inl ∘ (M.point ∘ Term.mark) := by
    funext i
    simp [p, d]
  let N : TermModel f :=
    { Site := M.Site ⊕ Unit, g := g, mono := hg, point := p
      initial := fun A => by rw [pm, place_comp, place_inl, he, M.initial] }
  have keep (c : Term S) (hc : M.Valid c) : N.point c = .inl (M.point c) :=
    ite_eq_right (fun hcd : c = d => h (hcd ▸ hc))
  have preserve (c : Term S) (hc : M.Valid c) : N.Valid c := by
    induction c with
    | mark => trivial
    | seg v s r ih ik =>
      obtain ⟨hs, hr, hu⟩ := (M.valid_iff v s r).mp hc
      refine (N.valid_iff v s r).mpr ⟨ih hs, ik hr, ?_⟩
      rw [keep _ hc, keep s hs, keep r hr]
      change Between g _ _ _ _
      simpa only [Between, dist_pad he] using hu
  refine ⟨N, (N.valid_iff t a b).mpr ⟨preserve a ha, preserve b hb, ?_⟩, preserve⟩
  rw [keep a ha, keep b hb]
  have hp : N.point d = .inr () := ite_eq_left rfl
  rw [hp]
  exact hd ()

omit [Nonempty S] in
private theorem add_term (a : Term S) (M : TermModel f) :
    ∃ N : TermModel f, N.Valid a ∧ ∀ b, M.Valid b → N.Valid b := by
  induction a generalizing M with
  | mark => exact ⟨M, trivial, fun _ h => h⟩
  | seg u a b ha hb =>
    obtain ⟨L, hL, hl⟩ := ha M
    obtain ⟨N, hN, hn⟩ := hb L
    obtain ⟨P, hp, keep⟩ := N.append u a b (hn a hL) hN
    exact ⟨P, hp, fun i hi => keep i (hn i (hl i hi))⟩

theorem exists_model (hf : Monotone f) (w : Finset (Term S)) :
    ∃ M : TermModel f, ∀ a ∈ w, M.Valid a := by
  classical
  induction w using Finset.induction_on with
  | empty => exact ⟨start hf, by simp⟩
  | insert a w _ ih =>
    obtain ⟨M, hM⟩ := ih
    obtain ⟨N, hN, hn⟩ := add_term a M
    refine ⟨N, fun b hb => ?_⟩
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact hN
    · exact hn b (hM b hb)

theorem same_distance (M N : TermModel f) {a b : Term S}
    (ha : M.Valid a) (hb : M.Valid b) (ha' : N.Valid a) (hb' : N.Valid b) :
    Tensor.dist M.g (M.point a) (M.point b) = Tensor.dist N.g (N.point a) (N.point b) := by
  have h : Agree (values 1 M.g) (values 1 N.g) (M.point ∘ Term.mark) (N.point ∘ Term.mark) :=
    fun A => by rw [values, values, M.initial, N.initial]
  have e := terms_determine (D := 1) (E := 1)
    ⟨1, ⟨zero_le_one, le_rfl⟩, M.g, M.mono, rfl⟩
    ⟨1, ⟨zero_le_one, le_rfl⟩, N.g, N.mono, rfl⟩ a b ha hb ha' hb' h
  simpa only [gap, values, one_mul, Tensor.dist] using e

end TermModel
end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# Completing a spectral placement

Pairwise distances of formal terms are independent of the finite model.
Use larger finite models to prove the triangle and comparison inequalities
for these distances, and pass to metric completion.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.TermModel
open Spectral UniformSpace

variable {K S : Type} [Field K] [Fintype S] [DecidableEq S] [Nonempty S]
  {f : Tensor K S →+* ℝ}

open Classical in
def length (hf : Monotone f) (a b : Term S) : ℝ :=
  let M := (exists_model hf {a, b}).choose
  Tensor.dist M.g (M.point a) (M.point b)

theorem length_eq (hf : Monotone f) (M : TermModel f) {a b : Term S}
    (ha : M.Valid a) (hb : M.Valid b) : length hf a b = Tensor.dist M.g (M.point a) (M.point b) := by
  classical
  have h := (exists_model hf {a, b}).choose_spec
  exact same_distance _ M (h a (by simp)) (h b (by simp)) ha hb

abbrev termMetric (hf : Monotone f) (d : ℝ) (hd : 0 ≤ d) : PseudoMetricSpace (Term S) where
  dist a b := d * length hf a b
  dist_self a := by
    classical
    obtain ⟨M, hM⟩ := exists_model hf {a}
    have ha := hM a (by simp)
    rw [length_eq hf M ha ha, Tensor.dist_self, mul_zero]
  dist_comm a b := by
    classical
    obtain ⟨M, hM⟩ := exists_model hf {a, b}
    have ha := hM a (by simp)
    have hb := hM b (by simp)
    rw [length_eq hf M ha hb, length_eq hf M hb ha, Tensor.dist_comm]
  dist_triangle a b c := by
    classical
    obtain ⟨M, hM⟩ := exists_model hf {a, b, c}
    have ha := hM a (by simp)
    have hb := hM b (by simp)
    have hc := hM c (by simp)
    rw [length_eq hf M ha hb, length_eq hf M hb hc, length_eq hf M ha hc, ← mul_add]
    exact mul_le_mul_of_nonneg_left (Tensor.dist_triangle _ M.mono _ _ _) hd

theorem complete (hc : SpectralComparison K) (hf : Monotone f) (d : ℝ) (hd : 0 ≤ d) :
    ∃ (Y : Type) (_ : MetricSpace Y) (_ : CompleteSpace Y) (p : Term S → Y),
      Comparison Y ∧ DenseRange p ∧
        ∀ (M : TermModel f) (a b), M.Valid a → M.Valid b →
          dist (p a) (p b) = d * Tensor.dist M.g (M.point a) (M.point b) := by
  classical
  let _ := termMetric hf d hd
  have e (M : TermModel f) (a b : Term S) (ha : M.Valid a) (hb : M.Valid b) :
      dist a b = d * Tensor.dist M.g (M.point a) (M.point b) :=
    congrArg (d * ·) (length_eq hf M ha hb)
  have hs (u : Fraction) (a b : Term S) : Along u a b (.seg u a b) := by
    intro z
    obtain ⟨M, hM⟩ := exists_model hf {Term.seg u a b, z}
    have hw := hM (.seg u a b) (by simp)
    have hz := hM z (by simp)
    obtain ⟨ha, hb, hh⟩ := (M.valid_iff u a b).mp hw
    have H := hc _ M.g M.mono _ _ _ u hh (M.point z)
    rw [e M _ _ hw hz, e M _ _ ha hz, e M _ _ hb hz, e M _ _ ha hb]
    linarith only [mul_le_mul_of_nonneg_left H (sq_nonneg d)]
  have cmp : Comparison (Completion (Term S)) := by
    intro a b t ht ht'
    have h := completion_along (hs ⟨t, ht, ht'⟩) a b
    exact ⟨_, h.start, h⟩
  exact ⟨_, inferInstance, inferInstance, Completion.coe', cmp, Completion.denseRange_coe,
    fun M a b ha hb => (Completion.dist_eq a b).trans (e M a b ha hb)⟩

end OAI.LinearAlgebra.MatrixExponent.Routing.TermModel
end

/-!
# Finite prices on geodesic terms

These constructions precede squared-distance comparison and metric
completion. In particular they can be used to establish comparison.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.TermModel
open Spectral

variable {K S : Type} [Field K] [Fintype S] [DecidableEq S] [Nonempty S]
  {f : Tensor K S →+* ℝ} (hf : Monotone f)

theorem length_mark (a b : S) :
    length hf (.mark a) (.mark b) = Tensor.dist f a b :=
  length_eq hf (start hf) trivial trivial

theorem length_seg (u : Fraction) (a b : Term S) :
    length hf a (.seg u a b) = u.val * length hf a b ∧
    length hf (.seg u a b) b = (1 - u.val) * length hf a b := by
  classical
  obtain ⟨M, hM⟩ := exists_model hf {Term.seg u a b}
  have hz := hM (.seg u a b) (by simp)
  obtain ⟨ha, hb, h⟩ := (M.valid_iff u a b).mp hz
  rw [length_eq hf M ha hz, length_eq hf M hz hb, length_eq hf M ha hb]
  exact h

theorem length_ordinary (B : Type) [Fintype B] [DecidableEq B] [Nonempty B]
    (z : B → Term S) (D : ℝ) (_hD : 0 < D) (h : ∀ i j, length hf (z i) (z j) ≤ D) :
    ∃ P : Tensor K B → ℝ, (P = 0 ∨ P ∈ Tensor.ordinary K B (D * Fintype.card B)) ∧
      ∀ i j, P (Tensor.wire K i j 2) = length hf (z i) (z j) := by
  classical
  obtain ⟨M, hM⟩ := exists_model hf (Finset.univ.image z)
  have hv (i : B) := hM (z i) (Finset.mem_image_of_mem z (Finset.mem_univ i))
  have hd (i j : B) := length_eq hf M (hv i) (hv j)
  rcases subsingleton_or_nontrivial B with hh | hh
  · refine ⟨0, .inl rfl, fun i j => ?_⟩
    rw [hd, Subsingleton.elim i j, Tensor.dist_self]
    rfl
  · let Q := Tensor.values 1 M.g
    let x := M.point ∘ z
    have hQ : Q ∈ Tensor.ordinary K M.Site 1 := ⟨1, ⟨zero_le_one, le_rfl⟩, M.g, M.mono, rfl⟩
    have hw (i j) : Q (Tensor.wire K (x i) (x j) 2) = length hf (z i) (z j) := by
      rw [hd]
      exact one_mul _
    refine ⟨Q ∘ Tensor.place x, .inr (Tensor.ordinary_restrict hQ x fun i j => (hw i j).le.trans (h i j)),
      fun i j => ?_⟩
    rw [Function.comp_apply, Tensor.place_wire, hw]

end OAI.LinearAlgebra.MatrixExponent.Routing.TermModel
end

/-!
# Rescaled limits of spectral wire metrics

Take the ultralimit on sequences of bounded rescaled displacement.
Distance zero need not be quotiented out for wire tests or segments.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.WireModels
open Filter Topology

theorem zoom {K X Y : Type} [Field K] [PseudoMetricSpace Y] (h : WireModels K Y)
    (s : Segments Y) (o : Y) (f : ℕ → X → Y)
    (hb : ∀ x, ∃ D : ℝ, ∀ n : ℕ, ((n : ℝ) + 1) * dist (f n x) o ≤ D) (v : Ultrafilter ℕ) :
    ∃ (Z : Type) (_ : PseudoMetricSpace Z) (g : X → Z),
      WireModels K Z ∧ Segments Z ∧ ∀ a b, Tendsto
        (fun n : ℕ => ((n : ℝ) + 1) * dist (f n a) (f n b)) (v : Filter ℕ) (𝓝 (dist (g a) (g b))) := by
  let Z := {z : ℕ → Y // ∃ D : ℝ, ∀ n : ℕ, ((n : ℝ) + 1) * dist (z n) o ≤ D}
  let q (x y : Z) (n : ℕ) := ((n : ℝ) + 1) * dist (x.val n) (y.val n)
  have pos (n : ℕ) : 0 ≤ (n : ℝ) + 1 := by positivity
  have lim (x y : Z) : ∃ d : ℝ, Tendsto (q x y) (v : Filter ℕ) (𝓝 d) := by
    obtain ⟨A, hA⟩ := x.property
    obtain ⟨B, hB⟩ := y.property
    have hh (n : ℕ) : q x y n ∈ Set.Icc 0 (A + B) := by
      refine ⟨mul_nonneg (pos n) dist_nonneg, ?_⟩
      exact (mul_le_mul_of_nonneg_left (dist_triangle_right _ _ o) (pos n)).trans
        ((mul_add _ _ _).le.trans (add_le_add (hA n) (hB n)))
    obtain ⟨d, _, hd⟩ := isCompact_Icc.ultrafilter_le_nhds' (v.map (q x y))
      (Filter.mem_map.mpr (Eventually.of_forall hh))
    exact ⟨d, hd⟩
  choose d hd using lim
  let _ : PseudoMetricSpace Z :=
    { dist := d
      dist_self := fun x => tendsto_nhds_unique (hd x x) (by simp [q])
      dist_comm := fun x y => tendsto_nhds_unique (hd x y)
        ((hd y x).congr' (Eventually.of_forall fun n => by simp [q, dist_comm]))
      dist_triangle := fun x y z => le_of_tendsto_of_tendsto (hd x z) ((hd x y).add (hd y z))
        (Eventually.of_forall fun n =>
          (mul_le_mul_of_nonneg_left (dist_triangle _ _ _) (pos n)).trans_eq (mul_add _ _ _)) }
  let g (x : X) : Z := ⟨fun n => f n x, hb x⟩
  refine ⟨Z, inferInstance, g, h.limit v (fun n z => z.val n) hd, ?_, fun a b => hd (g a) (g b)⟩
  intro t x y
  choose m hm using fun n => s t (x.val n) (y.val n)
  obtain ⟨A, hA⟩ := x.property
  obtain ⟨B, hB⟩ := y.property
  have hm' (n : ℕ) : ((n : ℝ) + 1) * dist (m n) o ≤ (1 - t.val) * A + t.val * B := by
    have e := h.busemann t _ _ _ _ _ _ (hm n) (Divides.same t o)
    linarith only [mul_le_mul_of_nonneg_left e (pos n),
      mul_le_mul_of_nonneg_left (hA n) (sub_nonneg.mpr t.2.2), mul_le_mul_of_nonneg_left (hB n) t.2.1]
  let z : Z := ⟨m, _, hm'⟩
  have aux (a b : Z) (u : ℝ) (hh : ∀ n, dist (a.val n) (b.val n) = u * dist (x.val n) (y.val n)) :
      dist a b = u * dist x y := by
    refine tendsto_nhds_unique (hd a b) ((tendsto_const_nhds.mul (hd x y)).congr' ?_)
    exact Eventually.of_forall fun n => by unfold q; rw [hh, mul_left_comm]
  exact ⟨z, aux x z _ (fun n => (hm n).1), aux z y _ (fun n => (hm n).2)⟩

end OAI.LinearAlgebra.MatrixExponent.Routing.WireModels
end
