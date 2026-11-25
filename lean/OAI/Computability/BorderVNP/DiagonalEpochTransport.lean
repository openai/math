import OAI.Computability.BorderVNP.DiagonalTaggedStep
import OAI.Computability.BorderVNP.ShortenAdaptiveFlatten

/-! # Tagged initial wire subdivision and the flat batch numbering between epochs -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries

open Crossing Shortening Adaptive Packing
open scoped BigOperators Classical

variable {D k b : ℕ} {P Team Team' Param Gadget : Type} [Fintype Team] [Fintype Team']
    [Fintype Param] {bits : P → ℕ} {N : Network D P bits}
    {tags : N.Tables (Entry Param Gadget)}

namespace PowerWords

/-- Renumbering the batch labels does not change a single polynomial factor. -/
noncomputable def relabel (w : PowerWords Team Param Gadget b N tags) (batch : Team' ≃ Team) :
    PowerWords Team' Param Gadget b N tags where
  site s := w.site (batch s.1, s.2)
  selected v z x s := w.selected v z x (batch s.1,s.2)
  located v z x s h := w.located v z x (batch s.1,s.2) h
  exact v z x := by
    refine (w.exact v z x).trans ?_
    exact Fintype.sum_equiv (batch.symm.prodCongr (Equiv.refl (Param × Fin b))) _ _
      (fun s => by simp [slotPower])

/-- At a subdivision vertex, only the retained original sites read a
power word. Every new site is an equality check with zero exponents. -/
noncomputable def subdivide (w : PowerWords Team Param Gadget b N tags) (routes : Network.WireRoutes N) :
    PowerWords Team Param Gadget b (N.subdivide routes) (N.subdivideTables routes tags) where
  site s := Sum.inl (w.site s)
  selected := by
    rintro (old | new) z x s
    · exact decide (N.subdivideTables routes
        (fun v a y => if w.selected v a y s then (1 : ℕ) else 0) (.inl old) z x ≠ 0)
    · exact false
  located v z x s h := by
    rcases v with old | new
    · change decide ((if w.selected old _ _ s then (1:ℕ) else 0) ≠ 0) = true at h
      have pass (bit : Bool) : decide ((if bit then (1:ℕ) else 0) ≠ 0) = true → bit = true := by
        cases bit <;> simp
      exact congrArg Sum.inl (w.located old _ _ s (pass _ h))
    · contradiction
  exact v z x := by
    rcases v with old | new
    · refine (w.exact old _ _).trans ?_
      apply Finset.sum_congr rfl
      intro s _
      change slotPower s (w.selected old _ _ s) =
        slotPower s (decide ((if w.selected old _ _ s then (1:ℕ) else 0) ≠ 0))
      cases w.selected old _ _ s <;> rfl
    · change (counters (if _ then (1 : Entry Param Gadget) else 0)).1 = ∑ s, slotPower s false
      rw [guard_noPower]
      simp

end PowerWords

namespace Tracked

/-- Install the actual initial subdivision used by the physical epoch. -/
noncomputable def subdivide (t : Tracked Team Param Gadget b N) (routes : Network.WireRoutes N) :
    Tracked Team Param Gadget b (N.subdivide routes) :=
  ⟨N.subdivideTables routes t.tags, t.words.subdivide routes⟩

/-- Subdivision commutes with interpretation, including at all added Boolean guards. -/
theorem subdivide_tensor {E : Type*} [CommSemiring E]
    (t : Tracked Team Param Gadget b N) (routes : Network.WireRoutes N)
    (values : Gadget → E) (x : Ports bits) :
    ((t.subdivide routes).valued values).tensor x = (t.valued values).tensor x := by
  refine Eq.trans ?_ (N.value_subdivide routes (t.valued values).table x)
  apply congrArg (fun T : (N.subdivide routes).Tables (MvPolynomial Param E) => (N.subdivide routes).value T x)
  funext v z y
  rcases v with old | new
  · rfl
  · change interpret values (if _ then 1 else 0) = (if _ then 1 else 0)
    split <;> simp_all

variable {steps : ℕ} {M : Network D (Port k P steps) (width bits k steps)}

/-- The flat child numbering of the public input and output fields. Sites
and internal wires are identical, so only the external slot reads change. -/
noncomputable def flat (t : Tracked Team Param Gadget b M) :
    Tracked Team Param Gadget b (flattenPack steps (⟨M,t.tags⟩ : Pack D _ _ (Entry Param Gadget))).layout := by
  let selected := (flattenPack steps (⟨M,t.words.selected⟩ : Pack D _ _ (PowerSlot Team Param b → Bool))).table
  exact ⟨(flattenPack steps (⟨M,t.tags⟩ : Pack D _ _ (Entry Param Gadget))).table,
    ⟨t.words.site, selected, fun v _ _ w h => t.words.located v _ _ w h, fun v _ _ => t.words.exact v _ _⟩⟩

/-- Every free slot still names its own original copy after flattening the pack. -/
theorem flat_tensor {E : Type*} [CommSemiring E] (t : Tracked Team Param Gadget b M)
    (values : Gadget → E) (x : Ports (fun q : Fin (k^steps) × P => bits q.2)) :
    (t.flat.valued values).tensor x = (t.valued values).tensor (nestedPorts bits k steps x) := rfl

end Tracked
end Diagonal.CellEntries

end BorderVNP
end Computability
end OAI
