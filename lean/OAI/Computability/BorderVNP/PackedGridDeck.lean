import OAI.Computability.BorderVNP.PackedGridPaths
import OAI.Computability.BorderVNP.CoverDeckProductRoute

/-! # Simple private paths in the actual product of congruence covers -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.DeckGrid

open BorderVNP.Cover

/-- The public channel alphabet is fixed by the number of surface factors and the finite
symmetric list of quaternion routing generators, independently of the cover level. -/
abbrev Direction (q : ℕ) := Fin q × {a : Orderˣ // a ∈ routingGenerators}

/-- Right multiplication by one fixed letter in one coordinate of the product host. -/
noncomputable def step (q l : ℕ) (a : Direction q) : Fin q → Deck l :=
  productStep q l (a.1, ⟨a.2.val,routingGenerators_mem _ a.2.property⟩)

/-- The same public alphabet supplies the reverse of every step. -/
theorem inverse_letter (q l : ℕ) (j : Direction q) :
    ∃ k, step q l k = (step q l j)⁻¹ := by
  refine ⟨(j.1,⟨j.2.val⁻¹,routingGenerators_inv _ j.2.property⟩),?_⟩
  funext i
  by_cases hi : i = j.1 <;> simp [step,productStep,hi]
  exact QuotientGroup.mk_inv ((gamma l).subgroupOf (gamma 1)) (⟨j.2.val,routingGenerators_mem _ j.2.property⟩ : gamma 1)

/-- The actual cubic diameter bound holds over the public finite alphabet. -/
theorem short_words (q d : ℕ) (u : Fin q → Deck (d+2)) :
    ∃ w : List (Direction q), w.length ≤ q*(1+3*d^3) ∧ (w.map (step q (d+2))).prod = u := by
  obtain ⟨w,hg,hl,hp⟩ := product_deck_diameter q d 1 u
  let encode (x : {a // a ∈ w}) : Direction q := (x.val.1,⟨x.val.2.val,hg _ x.property⟩)
  refine ⟨w.attach.map encode,by simpa using hl,?_⟩
  have he : (w.attach.map encode).map (step q (d+2)) = w.map (productStep q (d+2)) := by
    rw [List.map_map]
    change w.attach.map (fun x => productStep q (d+2) x.val) = _
    exact List.attach_map_val
  simpa [he] using hp

end Packing.DeckGrid

end BorderVNP
end Computability
end OAI
