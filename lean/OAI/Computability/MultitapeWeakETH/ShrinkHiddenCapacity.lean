import OAI.Computability.MultitapeWeakETH.HistoryCapacity
import OAI.Computability.VPVNP.PairShrinkRolePackedHidden
import OAI.Computability.VPVNP.PairShrinkHiddenSeedBudget

/-! # Capacity of the shrinking hidden-field directory on the sparse grid -/

namespace OAI.Computability.MultitapeWeakETH.ShrinkHidden

open VPVNP Compression Compression.ShrinkMotif CompressorRecords DescriptorSpace
open PairSimulation ShrinkRole ShrinkHistoryRows ShrinkBlockInputs BurstRAM Filter
open private shrinkMotif_count from OAI.Computability.VPVNP.PairSimulationSelectorBounds
noncomputable section

variable {k : Type} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)

/-- The tape reader only needs the public rows. Use an empty node arena in the
native certificate that also supplies those rows' IDs and widths. -/
def regions : LeafArena.Regions := ⟨⟨0,0⟩,0,0,0⟩

private def limit (n : ℕ) :=
  ShrinkCallABI.hiddenBase regions n + 4 * (n * slotDegree S) * (n*n)

private theorem limit_poly : PolynomiallyBounded (limit (S:=S)) := by
  exact ((PolynomiallyBounded.const regions.stackBase).add
    ((PolynomiallyBounded.const (Fintype.card LeafStartup.ScalarPort)).mul (PolynomiallyBounded.id.pow 40))).add
    (((PolynomiallyBounded.const 4).mul (PolynomiallyBounded.id.mul (.const (slotDegree S)))).mul
      (PolynomiallyBounded.id.mul PolynomiallyBounded.id))

set_option maxHeartbeats 1500000 in
theorem eventually_facts :
    ∀ᶠ n : ℕ in atTop, ∀ (i : Fin S.steps) {g : ℕ} (X : State (a i) (packingLaneBits (a i) g))
      (sel : SelectedScore.Selection B X) (positions blocks cur : ℕ),
      let w := CursorBounds.wordBits 1 n
      ∀ (base : Word w) (m : Memory w), CompiledResident.ShrinkPayload B base positions blocks n cur i X sel m →
      X.positions ≤ n → X.maxWireWidth ≤ n → 2^(a i) ≤ slotDegree S →
      ∀ v : MapResidentRows.Site X,
        PackedHidden.Facts B i X sel base positions blocks cur n regions v m ∧
          ∀ row ∈ PackedHidden.zeroRows B i X sel v, row.2.length ≤ n*n := by
  classical
  filter_upwards [CursorRAM.eventual_word_room 1 le_rfl (limit_poly (S:=S)),
    CursorRAM.eventual_word_room 1 le_rfl (.const B.shrink.selectorBits),
    eventually_ge_atTop (2*fieldFactor B.shrink), eventually_ge_atTop 1] with n room selector factor hn
  intro i g X sel positions blocks cur w base m stored pos maxW degree v
  let side := SelectedFinish.chosen B X sel
  have slots (motif : X.packingData.Motif) (t : Fin 4) :
      ShrinkHiddenRows.widths X B.shrink sel motif (!side,t) ≤ n*n := by
    have h := X.packingData.shrinkTerm_bounds (State.two_le_packingColors _) (Nat.two_pow_pos _)
      X.shrinkNumber X.packingWidth (fun _ => X.width_le_maxWireWidth _) B.shrink motif (sel motif)
    calc
      _ ≤ fieldFactor B.shrink * (X.maxWireWidth+1) := (h.2 _).2
      _ ≤ fieldFactor B.shrink * (2*n) := Nat.mul_le_mul_left _ (by omega)
      _ = (2*fieldFactor B.shrink)*n := by ring
      _ ≤ n*n := Nat.mul_le_mul_right n factor
  constructor
  · apply PackedHidden.of_payload B i X sel base positions blocks cur n regions v m stored selector slots
    have count := (shrinkMotif_count X).trans (Nat.mul_le_mul pos degree)
    apply lt_of_le_of_lt (b:=limit (S:=S) n) _ room
    apply Nat.add_le_add_left
    change (ShrinkTermInputs.motifCount X * 4) * (n*n) ≤ 4*(n*slotDegree S)*(n*n)
    rw [Nat.mul_comm (ShrinkTermInputs.motifCount X) 4]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 count)
  · intro row hr
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr
    simpa only [List.length_ofFn] using slots _ _

end
end OAI.Computability.MultitapeWeakETH.ShrinkHidden
