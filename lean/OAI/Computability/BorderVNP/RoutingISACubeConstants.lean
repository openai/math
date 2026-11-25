import OAI.Computability.BorderVNP.RoutingISAConstants
import OAI.Computability.BorderVNP.DiagonalTallyPacketEvidence

/-! # The cube recipe and table-position literals used by the signed evaluator

The finite identity fixes the order of summands, vertices and input digits.
The two arrays below contain only relative addresses and integer position
numbers. Their contents can be synthesized by a finite sequence of ordinary
word instructions independently of the input length.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CubeConstants

open VPVNP.BurstRAM VPVNP.MotifBase Cube Cube.Tally
open DiagonalTallyPacketEmit

variable {n b h K s : ℕ}

/-- Number of words in the flattened selector, vertex and digit recipe table. -/
noncomputable def recipeCount (n b h K s : ℕ) : ℕ :=
  Fintype.card (Selector n K h)*Fintype.card (Vertex (n+1))*argumentWidth n b h K s

/-- The row-major address of a fixed recipe digit. -/
noncomputable def recipeIndex (u : Selector n K h) (v : Vertex (n+1))
    (i : Fin (argumentWidth n b h K s)) : Fin (recipeCount n b h K s) :=
  finProdFinEquiv (finProdFinEquiv (selectorOrder n K h u,vertexOrder (n+1) v),i)

/-- The numeric address agrees with the addressing of the native recipe emitter. -/
theorem recipeIndex_val (u : Selector n K h) (v : Vertex (n+1)) (i : Fin (argumentWidth n b h K s)) :
    (recipeIndex u v i).val =
      ((selectorOrder n K h u).val * Fintype.card (Vertex (n+1))+(vertexOrder _ v).val)*
        argumentWidth n b h K s+i.val := by
  change i.val+argumentWidth n b h K s*((vertexOrder _ v).val+
    Fintype.card (Vertex (n+1))*(selectorOrder n K h u).val) = _
  ring

/-- Decode the static row number and emit the relative reference used in this digit. -/
noncomputable def recipeWord (n b h K s : ℕ) (i : Fin (recipeCount n b h K s)) : ℕ :=
  let (uv,j) := (finProdFinEquiv : _ × Fin (argumentWidth n b h K s) ≃ _).symm i
  let (a,c) := (finProdFinEquiv : Fin (Fintype.card (Selector n K h)) × Fin (Fintype.card (Vertex (n+1))) ≃ _).symm uv
  let u := (selectorOrder n K h).symm a
  let v := (vertexOrder (n+1)).symm c
  ((recipe u v b s)[j.val]'(by rw [recipe_length]; exact j.isLt)).code

/-- The full fixed address recipes, in the exact packed order of the ISA. -/
noncomputable def recipes (n b h K s : ℕ) : List ℕ := List.ofFn (recipeWord n b h K s)

/-- Each fixed native lookup retrieves the specified relative address code. -/
theorem recipeWord_at (u : Selector n K h) (v : Vertex (n+1))
    (i : Fin (argumentWidth n b h K s)) :
    recipeWord n b h K s (recipeIndex u v i) =
      ((recipe u v b s)[i.val]'(by rw [recipe_length]; exact i.isLt)).code := by
  simp [recipeWord,recipeIndex]

/-- Integer table-position number at every possible encoded Boolean input. -/
noncomputable def ids (id : TableEntry n b h K s → ℕ) : List ℕ :=
  List.ofFn fun k : Fin (2^argumentWidth n b h K s) ↦
    idTable (selectorOrder n K h) (vertexOrder (n+1)) id k.val

/-- The fixed code installs the literal zero and one and both complete finite
cube tables into the arrays addressed by the true primary frame. -/
noncomputable def install (id : TableEntry n b h K s → ℕ) : Code := .block [
  Constants.atField 81 [0],Constants.atField 82 [1],
  Constants.atField 79 (recipes n b h K s),Constants.atField 47 (ids id)]

/-- Memory following the four finite tables, without any preloaded value assumptions. -/
noncomputable def image (f : Frame) (idBase : ℕ) (id : TableEntry n b h K s → ℕ)
    (old : ℕ → ℕ) : ℕ → ℕ :=
  Constants.image idBase (ids id) (Constants.image f.recipes (recipes n b h K s)
    (Constants.image f.oneAddr [1] (Constants.image f.zeroAddr [0] old)))

/-- Consecutive disjoint placement after all primary frame words. -/
structure Fits (f : Frame) (w base idBase : ℕ) (id : TableEntry n b h K s → ℕ) : Prop where
  /-- The immutable frame precedes both literal words. -/
  frame : base+112 ≤ f.zeroAddr
  /-- Separate Boolean constants. -/
  zero : f.zeroAddr < f.oneAddr
  /-- Recipes begin after the literal one. -/
  one : f.oneAddr < f.recipes
  /-- Table numbers begin after the fixed recipes. -/
  recipesRoom : f.recipes+(recipes n b h K s).length ≤ idBase
  /-- Last cursor fits. -/
  idsRoom : idBase+(ids id).length < 2^w
  /-- Each fixed recipe code is representable at this word width. -/
  recipeWords : ∀ x ∈ recipes n b h K s, x < 2^w
  /-- Each fixed scalar position number is representable. -/
  idWords : ∀ x ∈ ids id, x < 2^w

/-- The four fixed data arrays satisfy exactly the requirements of the native
lookup on a cube vertex. -/
theorem image_values (f : Frame) {w base idBase : ℕ} (id : TableEntry n b h K s → ℕ)
    (old : ℕ → ℕ) (fit : Fits f w base idBase id)
    (width : f.width=argumentWidth n b h K s) (verts : f.vertices=Fintype.card (Vertex (n+1))) :
    f.recipeAt (image f idBase id old) n b h K s ∧
    (∀ j<2^argumentWidth n b h K s, image f idBase id old (idBase+j) =
      idTable (selectorOrder n K h) (vertexOrder (n+1)) id j) ∧
    image f idBase id old f.zeroAddr=0 ∧ image f idBase id old f.oneAddr=1 := by
  let m₀ := Constants.image f.zeroAddr [0] old
  let m₁ := Constants.image f.oneAddr [1] m₀
  let mr := Constants.image f.recipes (recipes n b h K s) m₁
  have before (a : ℕ) (ha : a < f.recipes) : image f idBase id old a = m₁ a := by
    have hr := fit.recipesRoom
    exact (Constants.image_outside _ _ mr _ (Or.inl (by omega))).trans
      (Constants.image_outside _ _ m₁ _ (Or.inl ha))
  refine ⟨⟨width,verts,?_⟩,?_,?_,?_⟩
  · intro u v j hj
    let k := recipeIndex u v (b := b) (s := s) ⟨j,(recipe_length u v b s) ▸ hj⟩
    have hi : k.val < (recipes n b h K s).length := by simpa only [recipes,List.length_ofFn] using k.isLt
    have eq := Constants.image_at f.recipes (recipes n b h K s) m₁ ⟨k.val,hi⟩
    change mr (f.recipes+k.val) = _ at eq
    have keep := Constants.image_outside idBase (ids id) mr (f.recipes+k.val)
      (Or.inl (by have := fit.recipesRoom; omega))
    rw [verts,width,Nat.add_assoc f.recipes _ j,← recipeIndex_val u v (b := b) (s := s) ⟨j,(recipe_length u v b s) ▸ hj⟩]
    exact keep.trans (eq.trans (by simpa only [recipes,List.getElem_ofFn] using recipeWord_at u v ⟨j,_⟩))
  · intro j hj
    have hi : j < (ids id).length := by simpa only [ids,List.length_ofFn] using hj
    exact (Constants.image_at idBase (ids id) mr ⟨j,hi⟩).trans (by simp only [ids,List.getElem_ofFn])
  · rw [before _ (fit.zero.trans fit.one),show m₁ f.zeroAddr=m₀ f.zeroAddr from
      Constants.image_outside _ _ _ _ (.inl fit.zero)]
    exact Function.update_self ..
  · rw [before _ fit.one]
    exact Function.update_self ..

end RoutingISA.CubeConstants

end BorderVNP
end Computability
end OAI
