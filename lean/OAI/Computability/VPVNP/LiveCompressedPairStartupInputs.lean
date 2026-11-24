import OAI.Computability.VPVNP.LiveProgramCompressedPair
import OAI.Computability.VPVNP.LiveLayoutWordFit

/-!
# Cursor startup inputs in the live pair ABI

The pair gets its workspace, input length and address width from public slots
two, six and seven. Its dispatch tag is the first old-state word, below the
auxiliary shadow and the cursor workspace. For a polynomially bounded bucket
size all four addresses or values fit the paper's word width eventually.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.CompressedPair

open BurstRAM Filter

/-- The old-state tag precedes the entire cursor workspace, for every layout. -/
theorem tag_before_workspace (c : Constants) (g : Geometry) :
    (Layout.oldState c).eval g < (Layout.pairWorkspace c).eval g := by
  change (Layout.oldState c).eval g <
    (((((((Layout.oldState c).eval g + c.configWords.eval g) + c.configWords.eval g) + 5) + 24) +
      c.prefixCapacity.eval g) + c.labels.eval g) + 2^(Layout.virtualSiteBits.eval g)
  apply lt_of_lt_of_le _ (Nat.le_add_right ..)
  omega

/-- Read the three startup words and the address computed by the actual tag prologue.
Their values are independent of the literal-prefix operands in slots zero and one. -/
theorem startup_inputs (c : Constants) (g : Geometry) (lit : LiteralPrefix)
    (workspace : (Layout.pairWorkspace c).eval g < 2^g.w) (length : g.n < 2^g.w)
    (address : g.d < 2^g.w) :
    let pub := Pieces.word g lit ∘ StageOperands.pair c
    (pub 2).val = (Layout.pairWorkspace c).eval g ∧ (pub 6).val = g.n ∧
      (pub 7).val = g.d ∧ (PairTag.address pub).val < (pub 2).val := by
  intro pub
  have hw : (pub 2).val = (Layout.pairWorkspace c).eval g := Nat.mod_eq_of_lt workspace
  refine ⟨hw, Nat.mod_eq_of_lt length, Nat.mod_eq_of_lt address, ?_⟩
  have lower := tag_before_workspace c g
  have old : (Pieces.word g lit (.geometry (Layout.oldState c))).val = (Layout.oldState c).eval g :=
    Nat.mod_eq_of_lt (lower.trans workspace)
  change (PairTag.address (Pieces.word g lit ∘ StageOperands.pair c)).val < (pub 2).val
  rw [hw, tag_address, old]
  exact lower

/-- The workspace addresses form a polynomially bounded sequence even though
their offset includes every site of the virtual auxiliary RAM. -/
theorem startup_workspace_polynomial (c : Constants) {B : ℕ} {H : ℕ → ℕ}
    (hB : 1 ≤ B) (hH : PolynomiallyBounded H) :
    PolynomiallyBounded (fun n => (Layout.pairWorkspace c).eval (paperGeometry B H n)) :=
  ((Layout.pairWorkspace_sitePowers c).fits hB hH).1

/-- One length threshold works for every literal program prefix. -/
theorem eventually_startup_inputs (c : Constants) {B : ℕ} {H : ℕ → ℕ}
    (hB : 1 ≤ B) (hH : PolynomiallyBounded H) :
    ∀ᶠ n : ℕ in atTop, ∀ lit : LiteralPrefix,
      let g := paperGeometry B H n
      let pub := Pieces.word g lit ∘ StageOperands.pair c
      (pub 2).val = (Layout.pairWorkspace c).eval g ∧ (pub 6).val = n ∧
        (pub 7).val = CursorBounds.addressBits B n ∧ (PairTag.address pub).val < (pub 2).val := by
  filter_upwards [((Layout.pairWorkspace_sitePowers c).fits hB hH).2,
    (PublicExpr.SitePowers.fits hB hH (e := .n) trivial).2,
    (PublicExpr.SitePowers.fits hB hH (e := .d) trivial).2] with n space length address
  exact fun lit => startup_inputs c (paperGeometry B H n) lit space.1 length.1 address.1

end LiveProgram.CompressedPair

end VPVNP
end Computability
end OAI
