import OAI.ThreeFlat.Diagonal.TraceInitialArity

namespace OAI
/-! # Actual physical trivalent trace cursor as an initial compression state -/

namespace ThreeFlat.Diagonal.PhysicalStage.Block
open LaneCursor Computability.VPVNP.Compression
open scoped BigOperators Classical
noncomputable section
variable {F : Type} [Field F] (B : Block F) {k : ℕ}

def cursorState (hk : 2≤k) (low offsets slots : ℕ) : State (2^(B.exponent 0)) k := by
  letI : NeZero k := ⟨by omega⟩
  exact {
    Base := Fin k
    order := finCongr (Fintype.card_fin k).symm
    Site := Fin k × BitWord k
    chart := Equiv.refl _
    graph := B.cursor_degree ▸ LaneCursor.graph hk (B.cursorCopies+1)
    width := fun _ => 2^low*(offsets*slots*3) }

theorem cursorState_positions (hk : 2≤k) (low offsets slots : ℕ) :
    (B.cursorState hk low offsets slots).positions=k*2^k := by
  change Fintype.card (Fin k × (Fin k → Fin 2))=_
  simp [Fintype.card_prod]

theorem cursorState_width (hk : 2≤k) (low offsets slots : ℕ) (e) :
    (B.cursorState hk low offsets slots).width e=2^low*(offsets*slots*3) := rfl

theorem cursorState_chart (hk : 2≤k) (low offsets slots : ℕ) :
    (B.cursorState hk low offsets slots).chart=Equiv.refl _ := rfl

theorem cursorState_graph (hk : 2≤k) (low offsets slots : ℕ) :
    (B.cursorState hk low offsets slots).graph =
      (B.cursor_degree ▸ LaneCursor.graph hk (B.cursorCopies+1) :
        LiftedSlots (Fin k) (2^(B.exponent 0)) (BitWord k)) := rfl

theorem cursorState_energy (hk : 2≤k) (low offsets slots : ℕ) :
    Real.sqrt (B.cursorState hk low offsets slots).energy ≤
      ((k*2^k : ℕ):ℝ)*(2^(B.exponent 0):ℕ)*(2^low*(offsets*slots*3) : ℕ) := by
  unfold State.energy
  rw [cursorState_positions]
  exact B.cursor_energy k low offsets slots

end
end ThreeFlat.Diagonal.PhysicalStage.Block

end OAI
