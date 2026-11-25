import OAI.Computability.BorderVNP.RoutingISACubeConstantRun

/-! # Placing the fixed cube lookup tables outside all routed input banks -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CubeConstants

open VPVNP.BurstRAM BorderVNP.Cube BorderVNP.Cube.Tally DiagonalTallyPacketEmit

variable {n b h K s w : ℕ}

/-- Installing the fixed tables leaves every other input or scratch address intact. -/
theorem image_outside (f : Frame) (idBase : ℕ) (id : TableEntry n b h K s → ℕ) (old : ℕ → ℕ)
    (a : ℕ) (zero : a≠f.zeroAddr) (one : a≠f.oneAddr)
    (recipe : a<f.recipes ∨ f.recipes+(recipes n b h K s).length ≤ a)
    (numbers : a < idBase ∨ idBase+(ids id).length ≤ a) : image f idBase id old a = old a := by
  unfold image
  rw [Constants.image_outside _ _ _ _ numbers,Constants.image_outside _ _ _ _ recipe,
    Constants.image_outside _ _ _ _ (show a<f.oneAddr ∨ f.oneAddr+[1].length ≤ a by simp; omega),
    Constants.image_outside _ _ _ _ (show a<f.zeroAddr ∨ f.zeroAddr+[0].length ≤ a by simp; omega)]

/-- A routed bit held below the cube-constant arena survives the constant
initializer between transmission and the owned-group traversal. -/
theorem image_before (f : Frame) (idBase : ℕ) (id : TableEntry n b h K s → ℕ)
    (old : ℕ → ℕ) {base : ℕ} (fit : Fits f w base idBase id) (a : ℕ) (ha : a<f.zeroAddr) :
    image f idBase id old a = old a := by
  have h₁ := fit.zero
  have h₂ := fit.one
  have h₃ := fit.recipesRoom
  exact image_outside f idBase id old a (by omega) (by omega) (.inl (by omega)) (.inl (by omega))

/-- Four contiguous banks, followed by the first free word, with no padding
proportional to the processor length. -/
noncomputable def idBase (fresh n b h K s : ℕ) := fresh+2+(recipes n b h K s).length

/-- One-past address of all immutable finite cube tables. -/
noncomputable def arenaEnd (fresh : ℕ) (id : TableEntry n b h K s → ℕ) :=
  idBase fresh n b h K s+(ids id).length

/-- Preserve the dynamic descriptors and triples and set the fixed operands
to the actual chosen contiguous ranges. -/
noncomputable def inArena (f : Frame) (fresh n b h K s : ℕ) : Frame :=
  { f with
    zeroAddr := fresh
    oneAddr := fresh+1
    recipes := fresh+2
    width := argumentWidth n b h K s
    vertices := Fintype.card (Vertex (n+1)) }

/-- An input-length-independent bound on every immediate table value. -/
noncomputable def valueBound (id : TableEntry n b h K s → ℕ) :=
  (recipes n b h K s).sum+(ids id).sum

private theorem le_sum {x : ℕ} {xs : List ℕ} (hx : x ∈ xs) : x ≤ xs.sum := by
  induction xs with
  | nil => cases hx
  | cons y ys ih =>
    rw [List.mem_cons] at hx
    rw [List.sum_cons]
    rcases hx with rfl | hx
    · omega
    · exact (ih hx).trans (Nat.le_add_left _ _)

/-- The whole native installer fits once its end address and its fixed finite
maximum fit. The threshold on values is independent of processor length. -/
theorem inArena_fits (f : Frame) (fresh base : ℕ) (id : TableEntry n b h K s → ℕ)
    (frame : base+112 ≤ fresh) (address : arenaEnd fresh id < 2^w)
    (values : valueBound id < 2^w) :
    Fits (inArena f fresh n b h K s) w base (idBase fresh n b h K s) id := by
  refine ⟨frame,by simp [inArena],by simp [inArena],le_rfl,address,?_,?_⟩
  · intro x hx
    exact ((le_sum hx).trans (Nat.le_add_right _ _)).trans_lt values
  · intro x hx
    exact ((le_sum hx).trans (Nat.le_add_left _ _)).trans_lt values

end RoutingISA.CubeConstants

end BorderVNP
end Computability
end OAI
