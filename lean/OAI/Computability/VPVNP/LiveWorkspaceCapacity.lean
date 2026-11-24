import OAI.Computability.VPVNP.LiveLayoutWordFit

/-!
# Word space for the live buffers and the auxiliary workspace

All live and auxiliary scratch addresses, including a final workspace of
R² words after the virtual header, fit in one word for every sufficiently
large length once B is fixed. The threshold works simultaneously for all
groups, nominations and compressor term choices.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram

open Filter

theorem eventually_workspace (c : Constants) {B : ℕ} (hB : 1 ≤ B)
    {H : ℕ → ℕ} (hH : PolynomiallyBounded H) :
    ∀ᶠ n in atTop, let g := paperGeometry B H n
      (Layout.pairWorkspace c).eval g + (CursorBounds.processorCount B n)^2 < 2^g.w ∧
      (Layout.shadow c).eval g < 2^g.w ∧ (Layout.oldState c).eval g < 2^g.w ∧
      Layout.stageTag.eval g < 2^g.w := by
  have safe : ((Layout.pairWorkspace c) + Layout.stageTag.natPow 2).SitePowers :=
    ⟨Layout.pairWorkspace_sitePowers c, Layout.stageTag_sitePowers.natPow 2⟩
  filter_upwards [(safe.fits hB hH).2, ((Layout.shadow_sitePowers c).fits hB hH).2,
    ((Layout.oldState_sitePowers c).fits hB hH).2, (Layout.stageTag_sitePowers.fits hB hH).2]
    with n hw hs ho ht
  have hR : Layout.stageTag.eval (paperGeometry B H n) = CursorBounds.processorCount B n := rfl
  change (Layout.pairWorkspace c).eval (paperGeometry B H n) + (CursorBounds.processorCount B n)^2 < 2^CursorBounds.wordBits B n ∧ _
  exact ⟨by simpa only [eval_add, PublicExpr.eval_natPow, hR] using hw.1, hs.1,ho.1,ht.1⟩

/-- The same heap bound applies to every descriptor offset below R². -/
theorem eventually_offset_fits (c : Constants) {B : ℕ} (hB : 1 ≤ B)
    {H : ℕ → ℕ} (hH : PolynomiallyBounded H) :
    ∀ᶠ n in atTop, ∀ i ≤ (CursorBounds.processorCount B n)^2,
      (Layout.pairWorkspace c).eval (paperGeometry B H n) + i < 2^CursorBounds.wordBits B n := by
  filter_upwards [eventually_workspace c hB hH] with n h i hi
  exact (Nat.add_le_add_left hi _).trans_lt h.1

end LiveProgram

end VPVNP
end Computability
end OAI
