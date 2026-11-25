import OAI.Hierarchy.FlatPrices
import Mathlib.Data.Fintype.Option

namespace OAI
/-! # The coefficient identity and strict price contradiction for the diagonal grid

A selector touches each external wire exactly once. On either side of the
touch the local equality factors force every bit from the external endpoint.
The simulation and identity selectors can therefore be counted in any
characteristic, before applying the strict Euclidean price inequality.
-/

namespace Hierarchy.GridDiagonal

open LinearAlgebra.SpectralBooks
open scoped BigOperators Classical

variable {E : Type} [Fintype E]

abbrev Ends (E : Type) := E × Bool
abbrev Pins (E : Type) := Ends E → Bool

/-- The equality tensor with one exterior bit at each end of every rail. -/
noncomputable def identity (F : Type*) [Field F] (x : Pins E) : F :=
  if ∀ i, x (i,false) = x (i,true) then 1 else 0

theorem identity_ne_zero (F : Type*) [Field F] : (identity F : Pins E → F) ≠ 0 := by
  intro h
  have a := congrFun h (fun _ => false)
  simp [identity] at a

/-- A half-rail has a boundary slot and a last slot incident with its unique touch.
The lengths are allowed to differ from one end and one rail to the next. -/
abbrev RailBits (length : Ends E → ℕ) := (i : Ends E) → Fin (length i + 1) → Bool

def follows (length : Ends E → ℕ) (x : Pins E) (rail : RailBits length) : Prop :=
  ∀ i, rail i 0 = x i ∧ ∀ a : Fin (length i), rail i a.succ = rail i a.castSucc

omit [Fintype E] in
theorem follows_iff (length : Ends E → ℕ) (x : Pins E) (rail : RailBits length) :
    follows length x rail ↔ rail = (fun i _ => x i) := by
  refine ⟨fun h => ?_, fun h => by subst rail; exact fun _ => ⟨rfl, fun _ => rfl⟩⟩
  funext i a
  exact Fin.induction (h i).1 (fun j ih => ((h i).2 j).trans ih) a

/-- Sum of local-selector weights through the actual independently summed interior
rail bits. A half-rail of length zero uses the external bit directly at its touch. -/
theorem sum_rails {F : Type*} [Field F] (length : Ends E → ℕ) (x : Pins E)
    (f : Pins E → F) [∀ r : RailBits length, Decidable (follows length x r)] :
    (∑ r : RailBits length,
      if follows length x r then f (fun i => r i (Fin.last _)) else 0) = f x := by
  classical
  simp_rw [follows_iff]
  simp

/-- Grouping all the primitive factors by the tick evaluating them preserves their
joint scalar, including ticks with no assigned factors. -/
theorem group_factors {F T A : Type*} [CommMonoid F] [Fintype T] [Fintype A]
    (tick : A → T) (factor : A → F) :
    (∏ t, ∏ a : {a // tick a = t}, factor a.1) = ∏ a, factor a := by
  classical
  exact Fintype.prod_fiberwise _ _

/-- Classifying a physical selector as identity, simulation, or invalid. The
honest controller has exactly one valid selector encoding each of its transcripts
and exactly one distinguished identity selector. -/
theorem sum_selectors {F S Tr : Type*} [Field F] [Fintype S] [Fintype Tr]
    (valid : S → Prop) [DecidablePred valid] (decode : {s // valid s} ≃ Option Tr)
    (row : S → F) (ident : F) (weight : Tr → F)
    (invalid : ∀ s, ¬valid s → row s = 0)
    (agrees : ∀ s : {s // valid s}, row s.1 = (decode s).elim ident weight) :
    ∑ s, row s = ident + ∑ z, weight z := by
  classical
  calc
    ∑ s, row s = ∑ s : {s // valid s}, row s.1 := by
      have zero : (∑ s : {s : S // ¬valid s}, row s.val) = 0 :=
        Finset.sum_eq_zero (fun s _ => invalid s.val s.property)
      rw [← Fintype.sum_subtype_add_sum_subtype valid row, zero, add_zero]
    _ = ∑ z : Option Tr, z.elim ident weight := Fintype.sum_equiv decode _ _ agrees
    _ = _ := by simp [Fintype.sum_option]

def raw {F : Type*} (c : Pins E → F) : SiteTensor.Raw.{0} (Ends E) F :=
  ⟨fun _ => Bool, fun _ => inferInstance, c⟩

/-- The grid-lens inequality on all description strings is incompatible with the exact
weighted controller on its own description. The zero-error branch implements the
paper's price convention for the zero tensor. -/
theorem impossible {F : Type*} [Field F] {k n : ℕ}
    (P : SpectralPlacementPrices F (EuclideanSpace ℝ (Fin k)))
    (ends : Ends E → EuclideanSpace ℝ (Fin k))
    (exactGrid approx : (Fin n → Bool) → Pins E → F)
    (strict : ∀ a, exactGrid a - approx a = 0 ∨
      P.price (raw (exactGrid a - approx a)) ends < P.price (raw (identity F)) ends)
    (controller : Fin n → Bool) (S Tr : Type) [Fintype S] [Fintype Tr]
    (valid : S → Prop) [DecidablePred valid] (decode : {s // valid s} ≃ Option Tr)
    (row : S → Pins E → F) (weight : Tr → Pins E → F)
    (grid : ∀ x, exactGrid controller x = ∑ s, row s x)
    (trace : ∀ x, approx controller x = ∑ z, weight z x)
    (invalid : ∀ s, ¬valid s → ∀ x, row s x = 0)
    (selector : ∀ s : {s // valid s}, ∀ x,
      row s.val x = (decode s).elim (identity F x) (fun z => weight z x)) : False := by
  have key : exactGrid controller - approx controller = identity F := by
    funext x
    simp only [Pi.sub_apply, grid, trace]
    rw [sum_selectors valid decode (fun s => row s x) (identity F x) (fun z => weight z x)
      (fun s h => invalid s h x) (fun s => selector s x)]
    exact add_sub_cancel_right _ _
  rcases (strict controller) with hz | lt
  · exact identity_ne_zero F (key.symm.trans hz)
  · rw [key] at lt
    exact (lt_irrefl _ lt)

end Hierarchy.GridDiagonal

end OAI
