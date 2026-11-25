import OAI.LinearAlgebra.MatrixExponent.Sphere.Block
import OAI.LinearAlgebra.MatrixExponent.Sphere.Seam


/-!
# Fusion width

At fixed input and output energies, a bounded-energy combination of
states at the first site realizes each matrix unit. The proof works
over the integers and over every field.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere

variable (R : Type*) [CommRing R]

/-- Twice the single-species cutoff at doubled energies `e,g`. -/
def width (e g : ℕ) : ℝ := (Real.sqrt e + Real.sqrt g) ^ 2 + (Real.sqrt e + Real.sqrt g)

namespace Width

variable (w : Bool → ℝ)

private abbrev Label := Slot ⊕ Mark 1

private def K : Label → Label → R
  | .inl _, .inl _ => 0
  | .inl x, .inr y => test R (start w x) (order w x) y
  | .inr x, .inl y => -test R (start w y) (order w y) x
  | .inr x, .inr y => pairing R x y

private theorem skew (x y : Label) : K R w y x = -K R w x y := by
  cases x <;> cases y <;> simp only [K, neg_zero, neg_neg]
  exact pairing_skew R _ _

private theorem diag (x : Label) : K R w x x = 0 := by
  cases x <;> simp [K, pairing_self]

private def source (i : Mode 1) : Label := .inr (.origin, i)

private def dest (i : Slot) : Label := .inr (mark i)

private theorem evaluate (c a b : Wedge 1) :
    wick (K R w) (c.val.map source ++ (slots a b).map dest) =
      fusion R c.val a.val b.val := by
  have he : c.val.map source ++ (slots a b).map dest =
      (marks .origin c.val ++ marks .middle a.val ++ marks .infinity b.val.reverse).map Sum.inr := by
    simp [slots, source, dest, mark, marks, Function.comp_def]
  rw [he, wick_map]
  rfl

private theorem tests (xs : List Slot) :
    ∃ v : Wedge 1 →₀ R, (∀ y ∈ v.support, energy y.val ≤ (xs.map (cost w)).sum ∧
      y.val.length = xs.length) ∧
      ∀ a b : Wedge 1,
        Finsupp.linearCombination R (fun t => fusion R t.val a.val b.val) v =
          wick (K R w) (xs.map Sum.inl ++ (slots a b).map dest) := by
  obtain ⟨v, hv, he⟩ := substitute_modes (skew R w) (diag R w) Sum.inl source (cost w) (by
    intro x
    refine ⟨Finset.range (order w x + 1), fun i => (-1) ^ i * (order w x).choose i,
      fun i => (0, start w x + i), ?_, ?_⟩
    · simp only [Finset.mem_range, cost]
      omega
    · rintro (y | y)
      · simp [K, source, test_origin]
      · rfl) xs []
  refine ⟨v, fun y hy => ?_, fun a b => ?_⟩
  · simpa [energy] using hv y hy
  · simpa only [List.nil_append, List.map_nil, evaluate] using
      (he [] ((slots a b).map dest)).symm

end Width

open Width Classical

/-- Matrix units can be realized keeping the total number of generators. -/
theorem fusion_width_length (a b : Wedge 1) :
    ∃ v : Wedge 1 →₀ R,
      (∀ t ∈ v.support, (energy t.val : ℝ) ≤ width (energy a.val) (energy b.val) ∧
        t.val.length = a.val.length + b.val.length) ∧
      ∀ a' b' : Wedge 1, energy a'.val = energy a.val → energy b'.val = energy b.val →
        Finsupp.linearCombination R (fun t => fusion R t.val a'.val b'.val) v =
          if a = a' ∧ b = b' then 1 else 0 := by
  let w (s : Bool) := if s then Real.sqrt (energy b.val) else Real.sqrt (energy a.val)
  obtain ⟨v, hv, he⟩ := tests R w (slots a b).reverse
  refine ⟨v, ?_, ?_⟩
  · intro t ht
    obtain ⟨h, hlen⟩ := hv t ht
    rw [List.map_reverse, List.sum_reverse] at h
    exact ⟨(Nat.cast_le.mpr h).trans (slots_cost w a b rfl rfl), by simpa [slots, Nat.add_comm] using hlen⟩
  · intro a' b' ha hb
    have wa : w false = Real.sqrt (energy a'.val) := by rw [ha]; rfl
    have wb : w true = Real.sqrt (energy b'.val) := by rw [hb]; rfl
    have hp (h : (slots a b).Perm (slots a' b')) := slots_inj h
    have hc : slots a b = slots a' b' ↔ a = a' ∧ b = b' :=
      ⟨fun h => hp (by rw [h]), fun ⟨h, i⟩ => by rw [h, i]⟩
    rw [he]
    have h := wick_pivot (K R w) Sum.inl dest (Width.weight w) (fun x => 0 < w x.1)
      (fun _ hx => weight_pos w hx) (fun _ _ => rfl) (test_pivot R w)
      (slots a b) (slots a' b') (slots_valid w a b rfl rfl) (slots_valid w a' b' wa wb)
      (slots_nodup a b) (fun h => hc.mpr (hp h))
      (by rw [slots_weight w a b rfl rfl, slots_weight w a' b' wa wb])
    simpa only [hc] using h

/-- The input and output basis indices of the desired matrix unit are
`a,b`. A single state realizes it on the entire pair of levels. -/
theorem fusion_width (a b : Wedge 1) :
    ∃ v : Wedge 1 →₀ R,
      (∀ t ∈ v.support, (energy t.val : ℝ) ≤ width (energy a.val) (energy b.val)) ∧
      ∀ a' b' : Wedge 1, energy a'.val = energy a.val → energy b'.val = energy b.val →
        Finsupp.linearCombination R (fun t => fusion R t.val a'.val b'.val) v =
          if a = a' ∧ b = b' then 1 else 0 := by
  obtain ⟨v, hv, he⟩ := fusion_width_length R a b
  exact ⟨v, fun t ht => (hv t ht).1, he⟩

end OAI.LinearAlgebra.MatrixExponent.Sphere
