import OAI.Computability.NearSquareRoot.InterchangeRectangles
import OAI.Computability.NearSquareRoot.InterchangeFarOuter
import Mathlib.InformationTheory.Hamming

/-!
# Rectangles for pairs of inner words at Hamming distance `p`

The rectangle records the differing coordinates, both letters at the first of them,
first-bit rectangle keys at the remaining differing coordinates, and the common
letters elsewhere. Fixing the two letters at the first coordinate ensures that no
two words on the same side can have distance `p`.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FarRectangles

open LetterRectangles
open scoped Classical

abbrev Word (h k : ℕ) := Fin h → Letter k
abbrev Support (h p : ℕ) := {s : Finset (Fin h) // s.card = p}

variable {h p k : ℕ}

/-- The one active coordinate whose two letters are recorded in full. -/
def anchor (hp : 0 < p) (s : Support h p) : s.val :=
  let hs : s.val.Nonempty := Finset.card_pos.mp (show 0 < s.val.card by simpa [s.property] using hp)
  ⟨s.val.min' hs, s.val.min'_mem hs⟩

abbrev Key (h p k : ℕ) (hp : 0 < p) :=
  (s : Support h p) × ((Letter k × Letter k) ×
    (s.val.erase (anchor hp s) → LetterRectangles.Key k) ×
    ({i : Fin h // i ∉ s.val} → Letter k))

/-- The `false` and `true` sides of the open directed rectangle. -/
def Incident {hp : 0 < p} (side : Bool) (r : Key h p k hp) (x : Word h k) : Prop :=
  r.2.1.1 ≠ r.2.1.2 ∧ (if side then r.2.1.2 else r.2.1.1) = x (anchor hp r.1) ∧
    (∀ i : r.1.val.erase (anchor hp r.1), LetterRectangles.Incident side (r.2.2.1 i) (x i)) ∧
    ∀ i : {i : Fin h // i ∉ r.1.val}, r.2.2.2 i = x i

private theorem support_eq {hp : 0 < p} {r : Key h p k hp} {x y : Word h k}
    (hx : Incident false r x) (hy : Incident true r y) :
    r.1.val = Finset.univ.filter (fun i => x i ≠ y i) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hi
    by_cases ha : i = anchor hp r.1
    · subst i
      exact hx.2.1 ▸ hy.2.1 ▸ hx.1
    · let j : r.1.val.erase (anchor hp r.1) := ⟨i, Finset.mem_erase.mpr ⟨ha, hi⟩⟩
      exact LetterRectangles.unequal_of_incident (hx.2.2.1 j) (hy.2.2.1 j)
  · intro hn
    by_contra hi
    exact hn ((hx.2.2.2 ⟨i, hi⟩).symm.trans (hy.2.2.2 ⟨i, hi⟩))

theorem distance_across {hp : 0 < p} {r : Key h p k hp} {x y : Word h k}
    (hx : Incident false r x) (hy : Incident true r y) : hammingDist x y = p :=
  (congrArg Finset.card (support_eq hx hy)).symm.trans r.1.property

theorem distance_same_side {hp : 0 < p} {r : Key h p k hp} {side : Bool} {x y : Word h k}
    (hx : Incident side r x) (hy : Incident side r y) : hammingDist x y < p := by
  have hsub : Finset.univ.filter (fun i => x i ≠ y i) ⊆ r.1.val.erase (anchor hp r.1) := by
    intro i hi
    have hn := (Finset.mem_filter.mp hi).2
    apply Finset.mem_erase.mpr
    constructor
    · rintro rfl
      exact hn (hx.2.1.symm.trans hy.2.1)
    · by_contra hi
      exact hn ((hx.2.2.2 ⟨i, hi⟩).symm.trans (hy.2.2.2 ⟨i, hi⟩))
  exact (Finset.card_le_card hsub).trans_lt
    ((Finset.card_erase_lt_of_mem (anchor hp r.1).property).trans_eq r.1.property)

/-- Every ordered pair of far words lies in exactly one directed rectangle. -/
theorem distance_iff_unique (hp : 0 < p) (x y : Word h k) :
    hammingDist x y = p ↔ ∃! r : Key h p k hp, Incident false r x ∧ Incident true r y := by
  classical
  constructor
  · intro hdist
    let s : Support h p := ⟨Finset.univ.filter (fun i => x i ≠ y i), hdist⟩
    let a := anchor hp s
    have unequal (i : s.val) : x i ≠ y i := (Finset.mem_filter.mp i.2).2
    have each (i : s.val.erase a) :
        ∃! z, LetterRectangles.Incident false z (x i) ∧ LetterRectangles.Incident true z (y i) :=
      (LetterRectangles.unequal_iff_unique _ _).mp (unequal ⟨i, (Finset.mem_erase.mp i.2).2⟩)
    let keys := fun i : s.val.erase a => (each i).choose
    have hk (i : s.val.erase a) := (each i).choose_spec
    have heq (i : {i : Fin h // i ∉ s.val}) : x i = y i := by
      by_contra hn
      exact i.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩)
    refine ⟨⟨s, (x a, y a), keys, fun i => x i⟩,
      ⟨⟨unequal a, rfl, fun i => (hk i).1.1, fun _ => rfl⟩,
        ⟨unequal a, rfl, fun i => (hk i).1.2, heq⟩⟩, ?_⟩
    rintro ⟨s', ⟨xa, ya⟩, f, g⟩ ⟨hx, hy⟩
    have hs : s' = s := Subtype.ext (support_eq hx hy)
    subst s'
    obtain rfl : xa = x a := hx.2.1
    obtain rfl : ya = y a := hy.2.1
    obtain rfl : f = keys := funext fun i => (hk i).2 _ ⟨hx.2.2.1 i, hy.2.2.1 i⟩
    obtain rfl : g = fun i : {i : Fin h // i ∉ s.val} => x i := funext hx.2.2.2
    rfl
  · rintro ⟨r, ⟨hx, hy⟩, _⟩
    exact distance_across hx hy

private theorem natCard_le {α : Type} (a : Fintype α) {n : ℕ} (ha : @Fintype.card α a ≤ n) :
    Nat.card α ≤ n := (@Nat.card_eq_fintype_card α a).trans_le ha

/-- A word lies on each side of at most one alphabet factor per anchor, and one
bit-position factor per other active coordinate, for every possible support. -/
theorem card_incident_le (hp : 0 < p) (side : Bool) (x : Word h k) :
    Fintype.card {r : Key h p k hp // Incident side r x} ≤
      h.choose p * (2 ^ k * k ^ (p - 1)) := by
  have hcard (i : Fin h) : Fintype.card {r : LetterRectangles.Key k //
      LetterRectangles.Incident side r (x i)} ≤ k := (LetterRectangles.card_incident _ _).le
  have bound := Rectangles.card_incident_anchor_complement p (LetterRectangles.Key k) (Letter k)
    (anchor hp) side (fun i r => LetterRectangles.Incident side r (x i)) x (B := k)
    (fun i => by simpa only [← Nat.card_eq_fintype_card] using hcard i)
  have hq : Fintype.card (Letter k) = 2 ^ k := by simp [Letter]
  rw [Fintype.card_fin, hq] at bound
  exact Nat.card_eq_fintype_card.symm.trans_le (natCard_le _ bound)

abbrev Label (h k : ℕ) := Fin h → Word h k
abbrev LabelKey (h p k : ℕ) (hp : 0 < p) := OuterRectangles.Key (Fin h) (Word h k) (Key h p k hp) p
noncomputable instance labelKeyFintype (h p k : ℕ) (hp : 0 < p) : Fintype (LabelKey h p k hp) := by
  letI : Fintype (Key h p k hp) := inferInstance
  letI : Fintype (Word h k) := inferInstance
  unfold LabelKey OuterRectangles.Key
  infer_instance

abbrev LabelIncident {hp : 0 < p} (side : Bool) (r : LabelKey h p k hp) (x : Label h k) :=
  OuterRectangles.Incident (@Incident h p k hp) side r x

private theorem not_far_self (hp : 0 < p) (x : Word h k) : ¬ hammingDist x x = p := by
  simpa using hp.ne

/-- The full off-diagonal support of the label matrix is a disjoint union of
rectangles. -/
theorem label_supported_iff_unique (hp : 0 < p) (x y : Label h k) :
    (hammingDist x y = p ∧ ∀ i, x i ≠ y i → hammingDist (x i) (y i) = p) ↔
      ∃! r : LabelKey h p k hp, LabelIncident false r x ∧ LabelIncident true r y :=
  OuterRectangles.supported_iff_unique (not_far_self hp) (fun hx hy => distance_across hx hy)
    (fun x y => (distance_iff_unique hp x y).mp) x y

theorem label_supported_of_incident {hp : 0 < p} {r : LabelKey h p k hp} {x y : Label h k}
    (hx : LabelIncident false r x) (hy : LabelIncident true r y) :
    hammingDist x y = p ∧ ∀ i, x i ≠ y i → hammingDist (x i) (y i) = p :=
  OuterRectangles.supported_of_incident (not_far_self hp) (fun hx hy => distance_across hx hy) hx hy

theorem count_far_across {hp : 0 < p} {r : LabelKey h p k hp} {x y : Label h k}
    (hx : LabelIncident false r x) (hy : LabelIncident true r y) :
    (Finset.univ.filter fun i => hammingDist (x i) (y i) = p).card = p :=
  OuterRectangles.count_far_cross (not_far_self hp) (fun hx hy => distance_across hx hy) hx hy

theorem count_far_same_side {hp : 0 < p} {side : Bool} {r : LabelKey h p k hp} {x y : Label h k}
    (hx : LabelIncident side r x) (hy : LabelIncident side r y) :
    (Finset.univ.filter fun i => hammingDist (x i) (y i) = p).card = 0 :=
  OuterRectangles.count_far_same (I := @Incident h p k hp) (far := fun a b => hammingDist a b = p) (not_far_self hp) (fun hx hy => (distance_same_side hx hy).ne) hx hy

/-- Per-endpoint incidence of the full outer rectangles, with the constants
in the fixed word length and distance made explicit. -/
theorem card_label_incident_le (hp : 0 < p) (side : Bool) (x : Label h k) :
    Fintype.card {r : LabelKey h p k hp // LabelIncident side r x} ≤
      h.choose p * (h.choose p * (2 ^ k * k ^ (p - 1))) ^ p := by
  have bound := OuterRectangles.card_incident_le (p := p) side x
    (fun i => card_incident_le hp side (x i))
  rw [Fintype.card_fin] at bound
  exact Nat.card_eq_fintype_card.symm.trans_le (natCard_le _ bound)

/-- For `q = 2^k` the incidence estimate has the form
`C(h,p) * q^p * (1 + log₂ q)^(p²)` of the interchange lemma. -/
theorem card_label_incident_polylog (hp : 0 < p) (side : Bool) (x : Label h k) :
    Fintype.card {r : LabelKey h p k hp // LabelIncident side r x} ≤
      (h.choose p) ^ (p + 1) * (2 ^ k) ^ p * (k + 1) ^ (p * p) := by
  refine (card_label_incident_le hp side x).trans ?_
  calc
    _ = (h.choose p) ^ (p + 1) * (2 ^ k) ^ p * k ^ ((p - 1) * p) := by
      simp only [mul_pow, pow_succ, pow_mul]
      ac_rfl
    _ ≤ _ := Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (Nat.le_succ _) _).trans
      (Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.mul_le_mul_right p (Nat.sub_le _ _))))

end FarRectangles

end NearSquareRoot
end Computability
end OAI
