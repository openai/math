import OAI.Computability.BorderVNP.CoverDeckRouting
import OAI.Computability.BorderVNP.CoverDeckTower

/-!
# Paths in the product tile graph

The single-factor cubic word bound of Lemma 5.1 gives a path in the product
host by using one coordinate at a time, as required by §5.3.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover

/-- A generator in one surface factor, acting trivially on all others. -/
def productStep (q l : ℕ) (letter : Fin q × gamma 1) : Fin q → Deck l :=
  fun i => if i = letter.1 then (letter.2 : Deck l) else 1

private theorem block_value (q l : ℕ) (i j : Fin q) (w : List (gamma 1)) :
    ((w.map (fun s => productStep q l (j,s))).prod) i =
      if i = j then (w.prod : Deck l) else 1 := by
  induction w with
  | nil => simp
  | cons a w ih =>
    simp only [List.map_cons, List.prod_cons, Pi.mul_apply, productStep, ih]
    by_cases h : i = j <;> simp [h]

private theorem blocks_value (q l : ℕ) (ws : Fin q → List (gamma 1))
    (factors : List (Fin q)) (hd : factors.Nodup) (i : Fin q) :
    (((factors.flatMap fun j => (ws j).map fun s => (j,s)).map (productStep q l)).prod) i =
      if i ∈ factors then ((ws i).prod : Deck l) else 1 := by
  induction factors with
  | nil => simp
  | cons j js ih =>
    simp only [List.flatMap_cons, List.map_append, List.prod_append, Pi.mul_apply,
      List.map_map,Function.comp_def, block_value, ih hd.of_cons]
    by_cases h : i = j
    · subst i
      simp [(List.nodup_cons.mp hd).1]
    · simp [h]

/-- In the product of `q` covers at level `d+2`, a path of at most
`q*(1+3*d³)` fixed one-coordinate generators joins any two tiles. -/
theorem product_deck_diameter (q d : ℕ) (start target : Fin q → Deck (d+2)) :
    ∃ w : List (Fin q × gamma 1), (∀ s ∈ w, s.2.val ∈ routingGenerators) ∧
      w.length ≤ q*(1+3*d^3) ∧ start * (w.map (productStep q (d+2))).prod = target := by
  classical
  choose ws hgen hlen hprod using (fun i => deck_diameter d (start i) (target i))
  let factors := (Finset.univ : Finset (Fin q)).toList
  refine ⟨factors.flatMap (fun j => (ws j).map fun s => (j,s)), ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨j,_,hh⟩ := List.mem_flatMap.mp ha
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hh
    exact hgen _ _ hs
  · rw [List.length_flatMap]
    simp only [List.length_map]
    have hh := List.sum_le_sum (l := factors) (g := Function.const _ (1+3*d^3))
      (fun i _ => hlen i)
    simpa only [List.map_const,List.sum_replicate,factors,Finset.length_toList,Finset.card_univ,
      Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] using hh
  · funext i
    rw [Pi.mul_apply, blocks_value q (d+2) ws factors Finset.univ.nodup_toList]
    simpa [factors] using hprod i

end Cover

end BorderVNP
end Computability
end OAI
