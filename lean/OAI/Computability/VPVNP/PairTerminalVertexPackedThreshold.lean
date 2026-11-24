import OAI.Computability.VPVNP.PairTerminalVertexFramePacked
import OAI.Computability.VPVNP.PairTerminalPrefixBudget
import OAI.Computability.VPVNP.CompressorBlockCapacity

/-!
# Selected vertex arenas in the chronological block allocation

The public header bounds hold at one length threshold before the coordinate
split, coefficient specialization and compressor choices. The chronological
directory used by the native calendar lies inside the reserved rectangle.
The terminal state's incidence and prefix tables fit even at zero blocks.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.PairStages.Group.Auxiliary

open BurstRAM PairSimulation Compression CompressorRecords DescriptorSpace
open CursorBounds CursorNetwork Filter TraversalRoles TraversalRows
open scoped Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)

theorem selected_table_capacity {A : Type*} [CommRing A] (f : B.Entry → A) (hf : B.IsSolution f)
    {l : ℕ} (T : ℕ) (hT : T*S.laneBits ≤ l) (X : State (S.degreeExponent 0) l)
    (z : (B.execute f hf T hT X).Choices) (workspace : ℕ) :
    let D := BlockProgram.layout B workspace X.positions T
    let Y := (B.execute f hf T hT X).finalState z
    TerminalPrefix.arcCount Y ≤ slotCapacity D ∧ TerminalPrefix.arcCount Y ≤ tableWords D := by
  intro D Y
  have positions : Y.positions ≤ X.positions :=
    (Nat.le_mul_of_pos_left _ (Nat.pow_pos (by have := S.positionFactor_gt_two; omega))).trans_eq
      (B.branch_bounds f hf T hT X z).1.symm
  have degree : 2^S.degreeExponent 0 ≤ slotDegree S :=
    (Finset.le_sup (f := fun j : Fin (S.steps+1) => 2^S.degreeExponent j) (Finset.mem_univ 0)).trans
      (le_max_right _ _)
  have slots : TerminalPrefix.arcCount Y ≤ slotCapacity D := by
    rw [TerminalPrefix.Segment.arc_count_positions]
    exact Nat.mul_le_mul positions degree
  exact ⟨slots,slots.trans (Nat.le_mul_of_pos_right _ (by change 0 < max _ _+3; omega))⟩

/-- The actual terminal header and all external arrays of a selected branch
in the live group. The site ordinal plays no role in the threshold. -/
theorem eventually_vertexPacked (u : PairExponents B.growthConstant) (b : ℕ) (hb : max S.laneBits 5 ≤ b)
    {start : ℕ → ℕ} (hstart : PolynomiallyBounded start) :
    ∀ᶠ n : ℕ in atTop, ∀ (G : Group) (_ : G.w = wordBits b n)
      (_ : (LiveProgram.Layout.pairWorkspace G.constants).eval G.g = start n)
      (_ : (terminalOperands G 7).val = addressBits b n)
      {base lanes : ℕ} (labels : Fin (virtualBits b n) ≃ Fin base ⊕ Fin lanes)
      (hD : 1 < virtualBits b n) (hT : blockCount (u.θ : ℝ) n*S.laneBits ≤ lanes)
      (A : Type*) [CommRing A] (f : B.Entry → A) (hf : B.IsSolution f),
      let X := pairInput S labels hD
      let T := blockCount (u.θ : ℝ) n
      let E := B.execute f hf T hT X
      let D := BlockProgram.layout B (start n) X.positions T
      ∀ z : E.Choices, VertexPacked G D B.recordLimit (selected B f hf T hT X z) (E.finalState z).totalWidth := by
  filter_upwards [TerminalLayout.eventually_fit B u (BlockProgram.allocationShape B) b hb hstart 0,
    CursorRAM.eventual_word_room b ((by decide : 1 ≤ 5).trans ((le_max_right _ _).trans hb)) hstart]
    with n full startFit
  intro G hw workspace exp base lanes labels hD hT A _ f hf X T E D z
  let r := addressBits b n
  let Y := E.finalState z
  let rows := words B.recordLimit (selectedLayers B f hf T hT X z)
  let bound := cursorLayout (BlockProgram.allocationShape B) b S.steps u.θ (start n) n
  have whole := full labels hD hT A f hf z
  change endAddress bound + 2*rows + Y.totalWidth < (start n + (2^r)^2 - 32) ∧
    start n + (2^r)^2 - 32 + 32 ≤ 2^(wordBits b n) ∧ _ at whole
  have count := pairInput_positions S labels hD
  change X.positions = initialPositions b n at count
  have actual : endAddress D ≤ endAddress bound := by
    change endAddress (BlockProgram.layout B (start n) X.positions T) ≤ _
    rw [count]
    exact BlockProgram.allocation_end B (start n) (initialPositions b n) T
  have wsFit : (LiveProgram.Layout.pairWorkspace G.constants).eval G.g < 2^G.w := by
    rwa [workspace,hw]
  have ws : (terminalOperands G 2).val = D.base := by
    change (LiveProgram.Layout.pairWorkspace G.constants).eval G.g % (2^G.w) = start n
    rw [Nat.mod_eq_of_lt wsFit, workspace]
  have rwFit : r < G.w := hw ▸ ((by omega : r < r+10).trans_le
    (Nat.le_self_pow (by decide : 4 ≠ 0) _))
  have high := whole.1
  have room := whole.2.1
  rw [pow_two] at high room
  have reserve : 32 ≤ D.base + 2^r*2^r := by change 32 ≤ start n + 2^r*2^r; omega
  have word : D.base+2^r*2^r ≤ 2^G.w := by change start n+2^r*2^r ≤ 2^G.w; rw [hw]; omega
  have head : (vertexHeader G).val = start n+2^r*2^r-32 :=
    TerminalPrefix.header_val D (terminalOperands G) r ws exp rwFit reserve word
  have size : tagWords B.recordLimit (selected B f hf T hT X z) = rows :=
    congrArg (words B.recordLimit) (selected_layers B f hf T hT X z)
  refine ⟨wsFit,ws.symm,by rw [head,hw]; exact room,?_⟩
  rw [head,size]
  exact (Nat.add_le_add_right (Nat.add_le_add_right actual (2*rows)) Y.totalWidth).trans high.le

end LiveProgram.PairStages.Group.Auxiliary

end VPVNP
end Computability
end OAI
