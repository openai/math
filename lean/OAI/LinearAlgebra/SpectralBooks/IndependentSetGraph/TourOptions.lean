import OAI.LinearAlgebra.SpectralBooks.IndependentSetGraph.IndependentSetPolynomial
import Mathlib.GroupTheory.Perm.Fin

/-! # The option rows of the Hamiltonian tour graph

A row records a position, a tail, and a distinct head. At position zero only
tail zero is allowed. Lexicographically orienting conflicting triples
gives each forbidden pair a single edge.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace IndependentSetGraph

open scoped Classical BigOperators
noncomputable section

abbrev TourOption (m : ℕ) :=
  {v : Fin m × Fin m × Fin m // v.2.1 ≠ v.2.2 ∧ ((v.1 : ℕ) = 0 → (v.2.1 : ℕ) = 0)}

namespace TourOption

variable {m : ℕ}
abbrev pos (a : TourOption m) := a.val.1
abbrev src (a : TourOption m) := a.val.2.1
abbrev dst (a : TourOption m) := a.val.2.2

@[ext] theorem ext {a b : TourOption m} (hp : pos a = pos b) (hs : src a = src b)
    (hd : dst a = dst b) : a = b := Subtype.ext (Prod.ext hp (Prod.ext hs hd))

def conflict (a b : TourOption m) : Prop :=
  a ≠ b ∧ (pos a = pos b ∨ src a = src b ∨
    (finRotate m (pos a) = pos b ∧ dst a ≠ src b) ∨
    (finRotate m (pos b) = pos a ∧ dst b ≠ src a))

theorem conflict_symm {a b : TourOption m} (hc : conflict a b) : conflict b a := by
  unfold conflict at *
  grind

/-- The lexicographic index of a position, tail, and head. -/
def code (a : TourOption m) : Fin (m * (m * m)) :=
  finProdFinEquiv (pos a, finProdFinEquiv (src a, dst a))

theorem code_injective : Function.Injective (code : TourOption m → _) := by
  intro a b h
  have he := finProdFinEquiv.injective h
  have hsd := finProdFinEquiv.injective (Prod.mk.inj he).2
  exact TourOption.ext (Prod.mk.inj he).1 (Prod.mk.inj hsd).1 (Prod.mk.inj hsd).2

abbrev Edge (m : ℕ) := {e : TourOption m × TourOption m //
  code e.1 < code e.2 ∧ conflict e.1 e.2}

abbrev left (e : Edge m) := e.val.1
abbrev right (e : Edge m) := e.val.2

theorem independent_iff (x : TourOption m → Bool) :
    independent left right x ↔
      ∀ a b, x a = true → x b = true → ¬ conflict a b := by
  constructor
  · intro hi a b ha hb hc
    have hne := code_injective.ne hc.1
    rcases lt_or_gt_of_ne hne with h | h
    · exact hi ⟨(a,b), h, hc⟩ ha hb
    · exact hi ⟨(b,a), h, conflict_symm hc⟩ hb ha
  · intro h e ha hb
    exact h _ _ ha hb e.property.2

end TourOption

variable {m : ℕ} [NeZero m]

/-- Rooted tours list their successive vertices, beginning at zero. -/
abbrev RootedTour (m : ℕ) [NeZero m] := {π : Equiv.Perm (Fin m) // π 0 = 0}

omit [NeZero m] in
private theorem next_ne (hm : 2 ≤ m) (t : Fin m) : finRotate m t ≠ t :=
  Equiv.Perm.mem_support.mp ((support_finRotate_of_le hm).symm ▸ Finset.mem_univ t)

open TourOption

/-- The arc at a position in a rooted enumeration. -/
def tourArc (hm : 2 ≤ m) (π : RootedTour m) (t : Fin m) : TourOption m :=
  ⟨(t, π.val t, π.val (finRotate m t)), π.val.injective.ne (Ne.symm (next_ne hm t)),
    fun ht => by have ht' : t = 0 := Fin.ext ht; simp [ht', π.property]⟩

def tourBits (π : RootedTour m) (a : TourOption m) : Bool :=
  decide (src a = π.val (pos a) ∧ dst a = π.val (finRotate m (pos a)))

private theorem bits_on_iff (π : RootedTour m) (a : TourOption m) :
    tourBits π a = true ↔ src a = π.val (pos a) ∧ dst a = π.val (finRotate m (pos a)) := by
  simp [tourBits]

private theorem bits_at (hm : 2 ≤ m) (π : RootedTour m) (t : Fin m) :
    tourBits π (tourArc hm π t) = true := (bits_on_iff ..).2 ⟨rfl, rfl⟩

private theorem bits_injective (hm : 2 ≤ m) :
    Function.Injective (tourBits : RootedTour m → TourOption m → Bool) := by
  intro π ρ h
  apply Subtype.ext
  apply Equiv.ext
  intro t
  have hbit := bits_at hm π t
  rw [h] at hbit
  exact ((bits_on_iff ..).1 hbit).1

def coveringOptions (x : TourOption m → Bool) : Prop :=
  ∀ t, ∃ a, pos a = t ∧ x a = true

private theorem bits_valid (hm : 2 ≤ m) (π : RootedTour m) :
    independent left right (tourBits π) ∧ coveringOptions (tourBits π) := by
  refine ⟨(independent_iff _).2 ?_, fun t => ⟨tourArc hm π t, rfl, bits_at hm π t⟩⟩
  intro a b ha hb hconf
  obtain ⟨has,had⟩ := (bits_on_iff ..).1 ha
  obtain ⟨hbs,hbd⟩ := (bits_on_iff ..).1 hb
  have heq (hp : pos a = pos b) : a = b := TourOption.ext hp (by rw [has,hbs,hp]) (by rw [had,hbd,hp])
  obtain ⟨hne, hc | hc | ⟨hp, he⟩ | ⟨hp, he⟩⟩ := hconf
  · exact hne (heq hc)
  · exact hne (heq (π.val.injective (has.symm.trans (hc.trans hbs))))
  · exact he (by rw [had,hbs,hp])
  · exact he (by rw [hbd,has,hp])

private theorem bits_surject_onto_valid (hm : 2 ≤ m) (x : TourOption m → Bool)
    (hi : independent left right x) (hc : coveringOptions x) :
    ∃ π : RootedTour m, tourBits π = x := by
  choose s hs hsx using hc
  have hconf := (independent_iff x).1 hi
  have huniq {t : Fin m} {a : TourOption m} (ht : pos a = t) (ha : x a = true) : a = s t := by
    by_contra hne
    exact hconf a (s t) ha (hsx t) ⟨hne, Or.inl (ht.trans (hs t).symm)⟩
  have hinj : Function.Injective (fun t => src (s t)) := by
    intro t u h
    by_contra hne
    have hsu : s t ≠ s u := fun he => hne ((hs t).symm.trans ((congrArg pos he).trans (hs u)))
    exact hconf (s t) (s u) (hsx t) (hsx u) ⟨hsu, Or.inr (Or.inl h)⟩
  let π := Equiv.ofBijective (fun t => src (s t)) ⟨hinj, Finite.surjective_of_injective hinj⟩
  have hroot : π 0 = 0 := Fin.ext ((s 0).property.2 (by rw [show (s 0).val.1 = 0 from hs 0]; rfl))
  have hhead (t : Fin m) : dst (s t) = src (s (finRotate m t)) := by
    by_contra hbad
    have hne : s t ≠ s (finRotate m t) := fun he =>
      next_ne hm t ((hs _).symm.trans ((congrArg pos he.symm).trans (hs t)))
    exact hconf _ _ (hsx t) (hsx _) ⟨hne, Or.inr (Or.inr (Or.inl ⟨by rw [hs,hs],hbad⟩))⟩
  refine ⟨⟨π,hroot⟩, ?_⟩
  funext a
  apply Bool.eq_iff_iff.mpr
  rw [bits_on_iff]
  constructor
  · rintro ⟨hs',hd'⟩
    have he := TourOption.ext (hs (pos a)).symm hs' (hd'.trans (hhead _).symm)
    exact he ▸ hsx (pos a)
  · intro ha
    have he := huniq (t := pos a) rfl ha
    exact ⟨congrArg src he, (congrArg dst he).trans (hhead _)⟩

/-- The occupied options contribute exactly the product of the tour's arc weights. -/
private theorem bits_weight {R : Type*} [CommMonoid R] (hm : 2 ≤ m) (π : RootedTour m)
    (w : Fin m → Fin m → R) :
    (∏ a : TourOption m, if tourBits π a then w (src a) (dst a) else 1) =
      ∏ t, w (π.val t) (π.val (finRotate m t)) := by
  symm
  apply Fintype.prod_of_injective (tourArc hm π)
  · exact fun _ _ he => congrArg pos he
  · intro a ha
    have hbits : tourBits π a ≠ true := by
      intro h
      obtain ⟨hs,hd⟩ := (bits_on_iff ..).1 h
      exact ha ⟨pos a, TourOption.ext rfl hs.symm hd.symm⟩
    simp [hbits]
  · intro t
    rw [bits_at hm π t]
    rfl

/-- Summing the independent choices that cover all positions gives the rooted
tour enumerator, with no factorial or characteristic-dependent multiplicity. -/
theorem sum_coveringOptions {R : Type*} [CommSemiring R] (hm : 2 ≤ m) (w : Fin m → Fin m → R) :
    (∑ x : TourOption m → Bool, if independent left right x ∧ coveringOptions x then
      ∏ a, (if x a then w (src a) (dst a) else 1) else 0) =
      ∑ π : RootedTour m, ∏ t, w (π.val t) (π.val (finRotate m t)) := by
  symm
  apply Fintype.sum_of_injective tourBits (bits_injective hm)
  · intro x hx
    split_ifs with h
    · exact (hx (bits_surject_onto_valid hm x h.1 h.2)).elim
    · rfl
  · intro π
    rw [ite_eq_left (bits_valid hm π), bits_weight hm]

end
end IndependentSetGraph

end SpectralBooks
end LinearAlgebra
end OAI
