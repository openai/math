import OAI.Computability.MultitapeWeakETH.HistoryIncidence
import OAI.Computability.VPVNP.CompressorRefreshMapWorkspace

/-! # The output states and private packets of retained descriptor passes -/

namespace OAI.Computability.MultitapeWeakETH.NativeGrid

open VPVNP Compression CompressorRecords DyadicBudget PairSimulation LocalHistory
open private collectLevels from OAI.Computability.VPVNP.CompressorExecutionLevels
noncomputable section

variable {k R : Type} [Field k] [CommRing R] {S : BlockSchedule k} {B : S.Templates}
  {f : B.Entry → R} {hf : B.IsSolution f}

private theorem outputs_within {a g b l P M : ℕ} {X : State a g} (E : StateExecution R b l X)
    (W : E.MapWitnesses f) (r : ExecutionReaders E W) (o : PassOrigins B f hf E) (z : E.Choices)
    (h : PrefixLevelScale.Within P M E) :
    ∀ v ∈ collectLevels B f hf E W r o z, (v.pass.next v.term).positions ≤ P ∧
      (v.pass.next v.term).maxWireWidth ≤ M := by
  induction E with
  | done => simp [collectLevels]
  | more p next ih =>
    intro v member
    rcases List.mem_cons.mp member with rfl | tail
    · exact (h.2.2 z.1).current
    · exact ih z.1 (W.2 z.1) (r.2 z.1) (o.2 z.1) z.2 (h.2.2 z.1) v tail

theorem history_output_size {s : ℕ} (hs : 1 ≤ s)
    (z : (B.execute f hf s (lanes_fit B s) (source B s)).Choices)
    (v : SelectedLevel B f hf) (member : v ∈ executeLevels B f hf s (lanes_fit B s) (source B s) z) :
    (v.pass.next v.term).positions ≤ (source B s).positions ∧ (v.pass.next v.term).maxWireWidth ≤ scale B s :=
  outputs_within _ _ _ _ z (within B f hf hs) v member

/-- A maximal-size independent packet for one site fits in the native address space
at the grid's word width. -/
theorem packet_fits {a g n : ℕ} (X : State a g) (v : X.network.Site) (h : X.network.Half v)
    (degree : 2^a ≤ n) (width : X.maxWireWidth ≤ n) :
    (NodeArguments.packed X v h).length < 2^(CursorBounds.wordBits 1 n) := by
  let l := Nat.clog 2 n
  have size : n ≤ 2^l := Nat.le_pow_clog (by decide) _
  have exp : 1+l+l < CursorBounds.wordBits 1 n := by
    change 1+l+l < (1*l+10)^4
    simp only [one_mul]
    calc
      1+l+l < (l+10)^2 := by nlinarith [Nat.zero_le (l^2)]
      _ ≤ (l+10)^4 := Nat.pow_le_pow_right (by omega) (by decide)
  calc
    _ ≤ 2 * n * n := (NodeArguments.packed_length_le X v h).trans (Nat.mul_le_mul (Nat.mul_le_mul_left _ degree) width)
    _ ≤ 2 * 2^l * 2^l := Nat.mul_le_mul (Nat.mul_le_mul_left _ size) size
    _ = 2^(1+l+l) := by simp only [pow_add,pow_one]
    _ < _ := Nat.pow_lt_pow_right (by decide) exp

end
end OAI.Computability.MultitapeWeakETH.NativeGrid
