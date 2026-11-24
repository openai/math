import OAI.Computability.VPVNP.CompressorBlockGroups
import OAI.Computability.VPVNP.CompressorDescriptorBranchSpace
import OAI.Computability.VPVNP.CompressorDescriptorSquare

/-!
# Capacity of the concrete online program

The dimensions used by the static phase compiler cover all of the selected
substeps. The exact chronological directory and its six tables fit within
the polynomial word bound and within the square pair workspace. Both length
thresholds are independent of the coefficient specialization and branch.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.BlockProgram

open BurstRAM Compression DescriptorSpace CursorBounds CursorNetwork Filter

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)

theorem refresh_length :
    let s := RefreshBlockPlan.shape B
    (refresh B).length = 24 + s.ties + s.ports*s.dH + s.degree := by
  intro s
  unfold refresh
  simp only [List.length_append, BlockHeaderPlan.substep_length, List.length_cons, List.length_nil,
    termPointers_length, BlockMetadata.visits]
  rw [RefreshBlockPlan.visits_length B (geometry B) S.steps (0 : Fin 6)]
  dsimp only [s]
  omega

theorem slots_pos : 0 < (geometry B).slots :=
  (Nat.two_pow_pos S.portExponent).trans_le (le_max_left _ _)

theorem field_rates (base positions blocks : ℕ) :
    let L := layout B base positions blocks
    let n := L.shape.slots*L.shape.fields
    ShrinkLevelSpace.tableFactor S ≤ n ∧ refreshRate B ≤ n ∧ residentRate S ≤ n ∧ 3 ≤ n := by
  let g := geometry B
  have h := Nat.le_mul_of_pos_left g.fields (slots_pos B)
  have h₁ := le_max_left (ShrinkLevelSpace.tableFactor S) (max (refreshRate B) (residentRate S))
  have h₂ := le_max_right (ShrinkLevelSpace.tableFactor S) (max (refreshRate B) (residentRate S))
  have h₃ := le_max_left (refreshRate B) (residentRate S)
  have h₄ := le_max_right (refreshRate B) (residentRate S)
  change max _ _+3 ≤ g.slots*g.fields at h
  change _ ≤ g.slots*g.fields ∧ _ ≤ g.slots*g.fields ∧ _ ≤ g.slots*g.fields ∧ _ ≤ g.slots*g.fields
  omega

theorem selected_capacity {R : Type*} [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f)
    {l : ℕ} (T : ℕ) (h : T * S.laneBits ≤ l) (X : State (S.degreeExponent 0) l) (base : ℕ)
    (z : (B.execute f hf T h X).Choices) :
    let L := layout B base X.positions T
    (executeLevels B f hf T h X z).length < L.levels ∧
      ∀ v ∈ executeLevels B f hf T h X z, v.input.positions ≤ L.positions ∧
        v.outputSites ≤ L.positions ∧ v.oldSlots ≤ slotCapacity L ∧ v.outputSlots ≤ slotCapacity L ∧
        v.origin.motifCount ≤ slotCapacity L := by
  apply selected_level_capacity
  · change (S.steps+1)*T < 1+(S.steps+1)*T; omega
  · exact le_rfl
  · exact le_rfl

/-- Runtime-sized addresses with a polynomial suffix fit under a single
threshold. The suffix can include the saved field data of the enclosing
diagonal machine. -/
theorem eventually_end (b : ℕ) (hb : 1 ≤ b) {θ : ℝ} (hθ : θ ≤ 1)
    {start suffix : ℕ → ℕ} (hs : PolynomiallyBounded start) (hf : PolynomiallyBounded suffix) :
    ∀ᶠ n : ℕ in atTop,
      endAddress (layout B (start n) (initialPositions b n) (blockCount θ n))
        + suffix n < 2^wordBits b n := by
  filter_upwards [eventually_cursor_room (allocationShape B) b (S.degreeExponent 0)
    S.steps hb hθ hs hf]
    with n h
  exact (Nat.add_le_add_right (allocation_end B (start n) (initialPositions b n) (blockCount θ n))
    _).trans_lt h.1

/-- The square-workspace threshold comes before the coordinate split, the
coefficient solution, and the selected chronological path. -/
theorem eventually_square (u : PairExponents B.growthConstant) (b : ℕ) (hb : max S.laneBits 5 ≤ b)
    (K : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (start : ℕ) {base lanes : ℕ} (labels : Fin (virtualBits b n)
      ≃ Fin base ⊕ Fin lanes)
      (hD : 1 < virtualBits b n) (hT : blockCount (u.θ : ℝ) n * S.laneBits ≤ lanes)
      (R : Type*) [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f),
      let X := pairInput S labels hD
      let T := blockCount (u.θ : ℝ) n
      ∀ z : (B.execute f hf T hT X).Choices,
        let Y := (B.execute f hf T hT X).finalState z
        endAddress (layout B start (initialPositions b n) T) +
          K*(X.positions+processorCount b n+Y.positions*B.growthConstant^T+Y.totalWidth)+1 <
            start+(processorCount b n)^2 := by
  filter_upwards [eventually_selected_square (allocationShape B) B u b hb K] with n h
  intro start base lanes labels hD hT R _ f hf X T z Y
  have upper := h start labels hD hT R f hf z
  exact (Nat.add_le_add_right (Nat.add_le_add_right (allocation_end B start (initialPositions b n)
    T) _) 1).trans_lt upper

end CompressorRecords.BlockProgram

end

end VPVNP
end Computability
end OAI
