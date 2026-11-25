import Mathlib.Data.FinEnum
import OAI.Optimization.LinearProgramming.PriceGame.LearningCells
import OAI.Optimization.LinearProgramming.PriceGame.LearningRepresentatives

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Learning
namespace Experts

open Finset

/-- An ordered pair specifies a difference of two coordinates. The dummy
coordinate permits single-variable comparisons in exactly the same format. -/
abbrev Feature (n : ℕ) := Fin n × Fin n

abbrev Code {n : ℕ} (thresholds : Feature n → Finset ℚ) :=
  (f : Feature n) → Cells.Cell (thresholds f)

@[instance_reducible] private def cellEnum (s : Finset ℚ) : FinEnum (Cells.Cell s) :=
  FinEnum.ofList (none :: (s.attach.sort (· ≤ ·)).flatMap fun x =>
    [some (x, false), some (x, true)]) (by
    intro c
    cases c with
    | none => simp
    | some entry =>
      obtain ⟨x, b⟩ := entry
      cases b <;> simp)

@[instance_reducible] private def codeEnum {n : ℕ} (thresholds : Feature n → Finset ℚ) : FinEnum (Code thresholds) := by
  letI (f : Feature n) : FinEnum (Cells.Cell (thresholds f)) := cellEnum (thresholds f)
  exact inferInstanceAs (FinEnum ((f : Feature n) → Cells.Cell (thresholds f)))

/-- Enumerate in a fixed order, using the sorted list of thresholds at each feature. -/
def codes {n : ℕ} (thresholds : Feature n → Finset ℚ) : List (Code thresholds) :=
  @FinEnum.toList (Code thresholds) (codeEnum thresholds)

theorem mem_codes {n : ℕ} (thresholds : Feature n → Finset ℚ) (c : Code thresholds) :
    c ∈ codes thresholds := @FinEnum.mem_toList _ (codeEnum thresholds) c

theorem length_codes {n : ℕ} (thresholds : Feature n → Finset ℚ) :
    (codes thresholds).length = (Cells.enumerate thresholds).card := by
  let _ : FinEnum (Code thresholds) := codeEnum thresholds
  simp only [codes, FinEnum.toList, List.length_map, List.length_finRange]
  exact FinEnum.card_eq_fintypeCard

/-- Decode all historical comparisons of a particular finite cell. -/
def observations {n : ℕ} (thresholds : Feature n → Finset ℚ) (c : Code thresholds) :
    List (Observation n) :=
  (FinEnum.toList (Feature n)).flatMap fun f =>
    ((thresholds f).sort (· ≤ ·)).map fun θ => ⟨f.1, f.2, θ, Cells.decode (c f) θ⟩

theorem realizes_observations_iff {n : ℕ} (thresholds : Feature n → Finset ℚ) (c : Code thresholds)
    (v : Fin n → ℚ) :
    (∀ o ∈ observations thresholds c, realizes o v) ↔
    ∀ f : Feature n, ∀ θ ∈ thresholds f,
      compare (v f.1 - v f.2) θ = Cells.decode (c f) θ := by
  constructor
  · intro h f θ hθ
    apply h ⟨f.1, f.2, θ, Cells.decode (c f) θ⟩
    exact List.mem_flatMap.mpr ⟨f, FinEnum.mem_toList _, List.mem_map.mpr ⟨θ, by simpa using hθ, rfl⟩⟩
  · intro h o ho
    obtain ⟨f, _, hf⟩ := List.mem_flatMap.mp ho
    obtain ⟨θ, hθ, rfl⟩ := List.mem_map.mp hf
    exact h f θ (by simpa using hθ)

/-- Code selected for an actual assignment, whether or not it is known to the algorithm. -/
def trueCode {n} (s : Feature n → Finset ℚ) (v : Fin n → ℚ) : Code s :=
  fun f => Cells.encode (s f) (v f.1 - v f.2)

def trueObservations {n} (s : Feature n → Finset ℚ) (v : Fin n → ℚ) :
    List (Observation n) :=
  observations s (trueCode s v)

theorem mem_observations_iff {n} (s : Feature n → Finset ℚ) (c : Code s) (o : Observation n) :
    o ∈ observations s c ↔ o.threshold ∈ s (o.i, o.j) ∧
      o.side = Cells.decode (c (o.i, o.j)) o.threshold := by
  obtain ⟨i, j, θ, side⟩ := o
  constructor
  · intro h
    obtain ⟨⟨i', j'⟩, _, hf⟩ := List.mem_flatMap.mp h
    obtain ⟨θ', hθ', e⟩ := List.mem_map.mp hf
    cases e
    exact ⟨by simpa using hθ', rfl⟩
  · rintro ⟨hθ, hs⟩
    change θ ∈ s (i, j) at hθ
    change side = Cells.decode (c (i, j)) θ at hs
    subst side
    exact List.mem_flatMap.mpr ⟨(i, j), FinEnum.mem_toList _, List.mem_map.mpr ⟨θ, by simpa using hθ, rfl⟩⟩

theorem mem_trueObservations_iff {n} (s : Feature n → Finset ℚ) (v : Fin n → ℚ) (o : Observation n) :
    o ∈ trueObservations s v ↔ o.threshold ∈ s (o.i, o.j) ∧ realizes o v := by
  rw [trueObservations, mem_observations_iff]
  apply and_congr_right
  intro hθ
  change (o.side = Cells.decode (Cells.encode (s (o.i, o.j)) (v o.i - v o.j)) o.threshold) ↔ _
  rw [Cells.decode_encode _ _ hθ]
  exact eq_comm

theorem trueObservations_mono {n} {s s' : Feature n → Finset ℚ} (v : Fin n → ℚ)
    (h : ∀ f, s f ⊆ s' f) : trueObservations s v ⊆ trueObservations s' v := by
  intro o ho
  obtain ⟨hθ, hs⟩ := (mem_trueObservations_iff _ _ _).mp ho
  exact (mem_trueObservations_iff _ _ _).mpr ⟨h _ hθ, hs⟩

theorem trueTable_exists {n} (R : ℕ) (a : Fin n) (s : Feature n → Finset ℚ)
    (z : Fin n → ℤ) (ha : z a = 0) (hb : ∀ i, boxLower a i ≤ z i ∧ z i ≤ boxUpper R a i) :
    ∃ t, cellTable R a (trueObservations s (fun i => (z i : ℚ))) = some t :=
  (cellTable_iff_integer _ _ _).mpr ⟨z, ha, hb, fun o ho => ((mem_trueObservations_iff _ _ o).mp ho).2⟩

/-- Append one rational expert for each feasible cell. The size of the raw
integer box has no role in this enumeration. -/
def generate {p : ℕ} (R : ℕ) (a : Fin (p+1)) (thresholds : Feature (p+1) → Finset ℚ) :
    List (Fin (p+1) → ℚ) :=
  (codes thresholds).filterMap fun c => cellRepresentative R a (observations thresholds c)

theorem trueTable_selected_mem_generate {p R : ℕ} {a : Fin (p+1)} {s : Feature (p+1) → Finset ℚ}
    {v : Fin (p+1) → ℚ} {t : Paths.Table (p+1)} (ht : cellTable R a (trueObservations s v) = some t) :
    representative (Paths.read t) a ∈ generate R a s := by
  apply List.mem_filterMap.mpr
  refine ⟨trueCode s v, mem_codes _ _, ?_⟩
  change cellRepresentative R a (trueObservations s v) = some _
  simp [cellRepresentative, ht]

/-- Every returned expert obeys the box and its decoded past comparisons. -/
theorem generated_sound {p R : ℕ} {a : Fin (p+1)} {s : Feature (p+1) → Finset ℚ}
    {v : Fin (p+1) → ℚ} (hv : v ∈ generate R a s) :
    v a = 0 ∧ (∀ i, (boxLower a i : ℚ) ≤ v i ∧ v i ≤ (boxUpper R a i : ℚ)) ∧
    ∃ c : Code s, ∀ f : Feature (p+1), ∀ θ ∈ s f,
      compare (v f.1 - v f.2) θ = Cells.decode (c f) θ := by
  obtain ⟨c, _, hc⟩ := List.mem_filterMap.mp hv
  obtain ⟨ha, hb, h⟩ := cellRepresentative_sound hc
  exact ⟨ha, hb, c, (realizes_observations_iff s c v).mp h⟩

/-- Every hidden integral assignment has an actually enumerated representative
with the same full comparison pattern, including ties. -/
theorem generated_complete {p : ℕ} (R : ℕ) (a : Fin (p+1)) (s : Feature (p+1) → Finset ℚ)
    (z : Fin (p+1) → ℤ) (ha : z a = 0)
    (hb : ∀ i, boxLower a i ≤ z i ∧ z i ≤ boxUpper R a i) :
    ∃ v ∈ generate R a s, ∀ f : Feature (p+1), ∀ θ ∈ s f,
      compare (v f.1 - v f.2) θ = compare ((z f.1 : ℚ) - (z f.2 : ℚ)) θ := by
  let q (i : Fin (p+1)) : ℚ := z i
  obtain ⟨t, ht⟩ := trueTable_exists R a s z ha hb
  let v := representative (Paths.read t) a
  have hc := representative_inCell ht
  refine ⟨v, trueTable_selected_mem_generate ht, ?_⟩
  intro f θ hθ
  let o : Observation (p+1) := ⟨f.1, f.2, θ, compare (q f.1 - q f.2) θ⟩
  have ho : o ∈ trueObservations s q := (mem_trueObservations_iff _ _ _).mpr ⟨hθ, rfl⟩
  exact accepts_sound (hc.2.2 o ho)

theorem length_generate_le {p : ℕ} (R : ℕ) (a : Fin (p+1)) (s : Feature (p+1) → Finset ℚ)
    (k : ℕ) (hk : ∀ f, (s f).card ≤ k) :
    (generate R a s).length ≤ (2 * k + 1) ^ ((p+1) * (p+1)) := by
  calc
    (generate R a s).length ≤ (codes s).length := List.length_filterMap_le _ _
    _ = (Cells.enumerate s).card := length_codes s
    _ ≤ _ := by simpa [Feature] using Cells.card_enumerate_le s k hk

/-- Features that were never compared have just one cell and do not contribute
to the exponent. This lets the dummy and repeated features be treated uniformly. -/
theorem length_generate_le_active {p : ℕ} (R : ℕ) (a : Fin (p+1)) (s : Feature (p+1) → Finset ℚ)
    (active : Finset (Feature (p+1))) (k : ℕ) (hk : ∀ f ∈ active, (s f).card ≤ k)
    (hinactive : ∀ f ∉ active, s f = ∅) :
    (generate R a s).length ≤ (2 * k + 1) ^ active.card := by
  calc
    (generate R a s).length ≤ (codes s).length := List.length_filterMap_le _ _
    _ = ∏ f, (2 * (s f).card + 1) := (length_codes s).trans (Cells.card_enumerate s)
    _ = ∏ f ∈ active, (2 * (s f).card + 1) := by
      symm
      apply Finset.prod_subset (subset_univ active)
      intro f _hf hno
      simp [hinactive f hno]
    _ ≤ ∏ _f ∈ active, (2 * k + 1) :=
      Finset.prod_le_prod (fun f hf => by have := hk f hf; omega)
    _ = _ := by simp

end Experts
end Learning
end PriceGame
end LinearProgramming
end Optimization
end OAI
