import OAI.LinearAlgebra.SpectralBooks.SignedProgram.SignedFrameCircuit
import OAI.LinearAlgebra.SpectralBooks.SignedProgram.SignedFrameRun
import OAI.LinearAlgebra.SpectralBooks.SignedProgram.SignedProgramHotLookup

/-! # A signed-machine tick on the packed verifier registers

The immutable input and encoded program precede one branch bit and the old
tableau row. The circuit reads the table directly from this prefix and the
state and head symbols directly from the encoded row.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

namespace SignedProgram

open SignedMachine ExactQuantumFactoring ExactQuantumFactoring.BooleanNetwork

abbrev packedStepWidth (n r : ℕ) :=
  ((n + Hot.decodeGuessWidth n) + 1) + Fintype.card (FrameWire n (r+1))

private def prefixWire (n r : ℕ) (i : Fin (n + Hot.decodeGuessWidth n)) : Fin (packedStepWidth n r) :=
  i.castSucc.castAdd _

def packedStepReader (n r : ℕ) : Hot.CellReader n (packedStepWidth n r) :=
  Hot.packedReader n (prefixWire n r)

def packedStepPrev (n r : ℕ) (w : FrameWire n (r+1)) : BooleanNetwork (packedStepWidth n r) 1 :=
  bit ((Fintype.equivFin _ w).natAdd ((n + Hot.decodeGuessWidth n) + 1))

def packedStepChoice (n r : ℕ) : BooleanNetwork (packedStepWidth n r) 1 :=
  bit ((Fin.natAdd (n + Hot.decodeGuessWidth n) (0 : Fin 1)).castAdd _)

def packedStepKey (n r : ℕ) : KeyInputs n (packedStepWidth n r) :=
  Hot.keyInputs (packedStepReader n r)
    (fun q => packedStepPrev n r (.inl (.inr q)))
    (fun s => packedStepPrev n r (.inr (none, Cell.center (r+1), s)))
    (fun j s => packedStepPrev n r (.inr (some j, Cell.center (r+1), s)))

/-- One complete tick with the immutable table, choice bit, and one-hot frame
in the layout used by the tableau unrolling circuit. -/
def packedStep (n r : ℕ) : BooleanNetwork (packedStepWidth n r) (Fintype.card (FrameWire n r)) :=
  frameStepNet (packedStepPrev n r) (keySignalsOfOneHot (packedStepKey n r))
    (Hot.actionSignals (packedStepReader n r)) (packedStepChoice n r)

/-- The packed tick computes the next row for every valid table encoding and
every frame whose live state belongs to the bounded state range. -/
theorem packedStep_eval {n r : ℕ} (x : Basis n) (g : Basis (Hot.decodeGuessWidth n))
    (b : Bool) (f : Frame n (r+1)) (hg : Hot.WellCoded g) (hf : f.bounded) :
    (packedStep n r).eval (Fin.append (Fin.append (Fin.append x g) (fun _ : Fin 1 => b)) f.encodeBits) =
      (f.tick (Hot.tableOfBits g) b).encodeBits := by
  let input := Fin.append (Fin.append (Fin.append x g) (fun _ : Fin 1 => b)) f.encodeBits
  have ht : (packedStepReader n r).Agrees input (Hot.tableOfBits g) := by
    apply Hot.packedReader_agrees _ _ x g hg
    funext i
    change input ((i.castAdd 1).castAdd _) = _
    simp [input]
  have hp (w : FrameWire n (r+1)) : (packedStepPrev n r w).eval input 0 = f.encode w := by
    simp [packedStepPrev, input]
  have hb : (packedStepChoice n r).eval input 0 = b := by
    simp [packedStepChoice, input]
  have hw : f.lookupAgrees (Hot.tableOfBits g) input (keySignalsOfOneHot (packedStepKey n r)) := by
    intro q hq
    have hqn : q ≤ n := by simpa [Frame.bounded, hq] using hf
    refine ⟨Nat.lt_succ_of_le hqn, ?_⟩
    apply KeyInputs.Agrees.keySignals
    apply Hot.keyInputs_agrees ht
    · intro p
      rw [hp]
      simp [Frame.encode, hq, Fin.ext_iff]
    · intro s
      exact hp _
    · intro j s
      exact hp _
  exact (frameStepNet_eval_encodeBits _ _ _ _ input _ f (Hot.actionSignals_agrees ht) hp hw).trans
    (congrArg (fun v => (f.tick (Hot.tableOfBits g) v).encodeBits) hb)

/-- Cost bound for the table lookup signals supplied to one tick. -/
def packedStepSignalBudget (n : ℕ) := (n+3)*(2*((n+1)*5+1)+5)+1

theorem packedStep_count_budget (n r : ℕ) :
    (packedStep n r).net.count ≤ Fintype.card (FrameWire n r) *
      frameTickBitBudget n (packedStepSignalBudget n) := by
  have hr : (packedStepReader n r).Bounded 1 := Hot.packedReader_bounded _
  have h1 : 1 ≤ packedStepSignalBudget n := Nat.le_add_left 1 _
  apply frameStepNet_count
  · intro w
    simp [packedStepPrev]
  · exact (Hot.keyInputs_bounded hr _ _ _
      (fun _ => by simp [packedStepPrev]) (fun _ => by simp [packedStepPrev])
      (fun _ _ => by simp [packedStepPrev])).keySignals
  · exact Hot.actionSignals_bounded (fun c v => (hr c v).trans h1)
  · simp [packedStepChoice]

end SignedProgram

end

end SpectralBooks
end LinearAlgebra
end OAI
