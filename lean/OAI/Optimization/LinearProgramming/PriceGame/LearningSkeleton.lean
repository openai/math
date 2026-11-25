import OAI.Optimization.LinearProgramming.PriceGame.Experts
import OAI.Optimization.LinearProgramming.PriceGame.LearningConstraints
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Size

/-! Compact, deterministic coordinate systems for the source indices of an actual
expert skeleton. Zero represents the dummy, and repeated tuple coordinates share a variable. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Learning
namespace Compact

variable {N : ℕ}
abbrev Coord (s : Skeleton N) := Fin (s.sources.card + 1)

def index (s : Skeleton N) (i : Fin N) : Coord s :=
  if hi : i ∈ s.sources then ((s.sources.orderIsoOfFin rfl).symm ⟨i, hi⟩).succ else 0

def pack {K : Type*} [Zero K] (s : Skeleton N) (raw : Fin N → K) : Coord s → K :=
  Fin.cases 0 fun i => raw (s.sources.orderIsoOfFin rfl i)

def unpack {K : Type*} [One K] (s : Skeleton N) (v : Coord s → K) (i : Fin N) : K :=
  if i ∈ s.sources then v (index s i) else 1

@[simp] theorem pack_zero {K : Type*} [Zero K] (s : Skeleton N) (raw : Fin N → K) :
    pack s raw 0 = 0 := rfl

theorem index_ne_zero (s : Skeleton N) {i : Fin N} (hi : i ∈ s.sources) :
    index s i ≠ 0 := by simp [index, hi]

theorem pack_index {K : Type*} [Zero K] (s : Skeleton N) (raw : Fin N → K)
    {i : Fin N} (hi : i ∈ s.sources) : pack s raw (index s i) = raw i := by
  rw [index, dite_eq_left hi]
  change raw ((s.sources.orderIsoOfFin rfl) ((s.sources.orderIsoOfFin rfl).symm ⟨i, hi⟩)).val = _
  rw [OrderIso.apply_symm_apply]

theorem unpack_index {K : Type*} [One K] (s : Skeleton N) (v : Coord s → K)
    {i : Fin N} (hi : i ∈ s.sources) : unpack s v i = v (index s i) := by simp [unpack, hi]

theorem unpack_pack {K : Type*} [Zero K] [One K] (s : Skeleton N) (raw : Fin N → K)
    {i : Fin N} (hi : i ∈ s.sources) : unpack s (pack s raw) i = raw i := by
  rw [unpack_index s _ hi, pack_index s _ hi]

theorem pack_unpack {K : Type*} [Zero K] [One K] (s : Skeleton N) (v : Coord s → K)
    (hz : v 0 = 0) : pack s (unpack s v) = v := by
  funext i
  refine Fin.cases (by simpa only [pack_zero] using hz.symm) (fun j => ?_) i
  let e := s.sources.orderIsoOfFin rfl
  change unpack s v (e j).val = v j.succ
  rw [unpack_index s _ (e j).property, index, dite_eq_left (e j).property]
  change v (e.symm (e j)).succ = v j.succ
  rw [e.symm_apply_apply]

theorem pack_int_box (s : Skeleton N) (R : ℕ) (P : Fin N → ℤ)
    (hP : ∀ i, 1 ≤ P i ∧ P i ≤ (R : ℤ) + 1) (i : Coord s) :
    boxLower 0 i ≤ pack s P i ∧ pack s P i ≤ boxUpper R 0 i := by
  refine Fin.cases (by simp [boxLower, boxUpper]) (fun j => ?_) i
  simpa [boxLower, boxUpper, pack] using hP (s.sources.orderIsoOfFin rfl j)

theorem unpack_box (s : Skeleton N) (R : ℕ) (v : Coord s → ℚ)
    (hv : ∀ i, (boxLower 0 i : ℚ) ≤ v i ∧ v i ≤ (boxUpper R 0 i : ℚ)) (i : Fin N) :
    1 ≤ unpack s v i ∧ unpack s v i ≤ (R : ℚ) + 1 := by
  by_cases hi : i ∈ s.sources
  · rw [unpack_index s _ hi]
    simpa [boxLower, boxUpper, index_ne_zero s hi] using hv (index s i)
  · simp [unpack, hi]

theorem coord_card_le (s : Skeleton N) : Fintype.card (Coord s) ≤ 66 := by
  simpa only [Fintype.card_fin] using Nat.succ_le_succ (s.card_sources_le)

theorem coordinate_bits (s : Skeleton N) (i : Coord s) : i.val.size ≤ 7 := by
  apply Nat.size_le.mpr
  have hc := s.card_sources_le
  have hi := i.isLt
  change i.val < s.sources.card + 1 at hi
  omega

theorem original_bits (i : Fin N) : i.val.size ≤ N.size := Nat.size_le_size i.isLt.le

/-- Two compact variables encode an observed feature, using the dummy for a unary feature. -/
def endpoints (s : Skeleton N) (f : Feature N) : Coord s × Coord s :=
  (index s f.1, (f.2.map (index s)).getD 0)

def Supported (s : Skeleton N) (f : Feature N) : Prop :=
  f.1 ∈ s.sources ∧ ∀ i, f.2 = some i → i ∈ s.sources

private theorem origin_supported (s : Skeleton N) (j : Fin 64) : s.origin j ∈ s.sources := by
  exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))

private theorem pivot_supported (s : Skeleton N) {p : (k : Fin s.level) × States.Mass.Vertex N k}
    (hp : s.pivot = some p) : rootVertex N p.1 p.2 ∈ s.sources := by
  exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (by simp [hp]))

private theorem outside_supported (s : Skeleton N) (history : History N)
    (y : States.Mass.Vertex N s.level → ℚ) (j : Fin 64) :
    Supported s (s.outsideTest history y j).feature := by
  cases hp : s.pivot with
  | none => simp [Skeleton.outsideTest, hp, Supported, origin_supported]
  | some p =>
    obtain ⟨k, v⟩ := p
    simp [Skeleton.outsideTest, hp, Supported, origin_supported, pivot_supported s hp]

private theorem pair_supported (s : Skeleton N) (y : States.Mass.Vertex N s.level → ℚ)
    (j j' : Fin 64) : Supported s (s.pairTest y j j').feature := by
  simp [Skeleton.pairTest, Supported, origin_supported]

theorem test_supported (s : Skeleton N) (probes : List (Probe N)) (t : Test N)
    (ht : t ∈ probes.flatMap s.testsAt) : Supported s t.feature := by
  obtain ⟨p, _, hp⟩ := List.mem_flatMap.mp ht
  unfold Skeleton.testsAt at hp
  split at hp
  · obtain ⟨xs, hxs, ht'⟩ := List.mem_flatten.mp hp
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hxs
    rcases List.mem_cons.mp ht' with rfl | hm
    · exact outside_supported _ _ _ _
    · obtain ⟨j', rfl⟩ := List.mem_ofFn.mp hm
      exact pair_supported _ _ _ _
  · simp at hp

theorem featureValue_unpack (s : Skeleton N) (probes : List (Probe N)) (t : Test N)
    (ht : t ∈ probes.flatMap s.testsAt) (v : Coord s → ℚ) (hz : v 0 = 0) :
    featureValue (unpack s v) t.feature =
      v (endpoints s t.feature).1 - v (endpoints s t.feature).2 := by
  obtain ⟨hi, hj⟩ := test_supported s probes t ht
  cases ho : t.feature.2 with
  | none => simp [featureValue, endpoints, ho, unpack_index s v hi, hz]
  | some j =>
    simp [featureValue, endpoints, ho, unpack_index s v hi, unpack_index s v (hj j ho)]

theorem featureValue_pack (s : Skeleton N) (probes : List (Probe N)) (t : Test N)
    (ht : t ∈ probes.flatMap s.testsAt) (P : Fin N → ℚ) :
    featureValue P t.feature =
      pack s P (endpoints s t.feature).1 - pack s P (endpoints s t.feature).2 := by
  obtain ⟨hi, hj⟩ := test_supported s probes t ht
  cases ho : t.feature.2 with
  | none => simp [featureValue, endpoints, ho, pack_index s P hi]
  | some j => simp [featureValue, endpoints, ho, pack_index s P hi, pack_index s P (hj j ho)]

/-- Group the actual probe thresholds by the pair of compact variables tested. -/
def thresholds (s : Skeleton N) (probes : List (Probe N)) (ij : Coord s × Coord s) : Finset ℚ :=
  (((probes.flatMap s.testsAt).toFinset).filter (fun t => endpoints s t.feature = ij)).image
    Test.threshold

theorem threshold_mem (s : Skeleton N) (probes : List (Probe N)) (t : Test N)
    (ht : t ∈ probes.flatMap s.testsAt) :
    t.threshold ∈ thresholds s probes (endpoints s t.feature) :=
  Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr ht, rfl⟩, rfl⟩

theorem pack_intCast (s : Skeleton N) (v : Fin N → ℤ) :
    (fun i => ((pack (K := ℤ) s v i : ℤ) : ℚ)) = pack s (fun j => (v j : ℚ)) := by
  funext i
  exact Fin.cases (by simp) (fun _ => rfl) i

theorem threshold_mem_iff (s : Skeleton N) (probes : List (Probe N))
    (ij : Coord s × Coord s) (θ : ℚ) :
    θ ∈ thresholds s probes ij ↔
    ∃ t ∈ probes.flatMap s.testsAt, endpoints s t.feature = ij ∧ t.threshold = θ := by
  simp only [thresholds, Finset.mem_image, Finset.mem_filter, List.mem_toFinset]
  aesop

theorem thresholds_mono (s : Skeleton N) {ps qs : List (Probe N)} (h : ps ⊆ qs)
    (ij : Coord s × Coord s) : thresholds s ps ij ⊆ thresholds s qs ij := by
  intro θ hθ
  obtain ⟨t, ht, he, hval⟩ := (threshold_mem_iff s ps ij θ).mp hθ
  obtain ⟨p, hp, ht⟩ := List.mem_flatMap.mp ht
  exact (threshold_mem_iff s qs ij θ).mpr
    ⟨t, List.mem_flatMap.mpr ⟨p, h hp, ht⟩, he, hval⟩

private theorem flatten_length_le {α : Type*} (xs : List (List α)) (q : ℕ)
    (h : ∀ ys ∈ xs, ys.length ≤ q) : xs.flatten.length ≤ xs.length * q := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    have ha := h a (by simp)
    have has := ih (fun ys hym => h ys (by simp [hym]))
    simpa [List.flatten_cons, Nat.add_mul, Nat.add_comm, Nat.add_left_comm] using
      Nat.add_le_add ha has

theorem testsAt_length_le (s : Skeleton N) (p : Probe N) : (s.testsAt p).length ≤ 4160 := by
  unfold Skeleton.testsAt
  split
  · apply (flatten_length_le _ 65 _).trans
    · simp
    · intro ys hys
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hys
      simp
  · simp

theorem recorded_length_le (s : Skeleton N) (ps : List (Probe N)) :
    (ps.flatMap s.testsAt).length ≤ ps.length * 4160 := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    simpa [Nat.add_mul, Nat.add_comm, Nat.add_left_comm] using
      Nat.add_le_add (testsAt_length_le s p) ih

theorem thresholds_card_le (s : Skeleton N) (ps : List (Probe N)) (ij : Coord s × Coord s) :
    (thresholds s ps ij).card ≤ ps.length * 4160 := by
  apply Finset.card_image_le.trans
  apply (Finset.card_filter_le _ _).trans
  exact (List.toFinset_card_le _).trans (recorded_length_le s ps)

end Compact
end Learning
end PriceGame
end LinearProgramming
end Optimization
end OAI
