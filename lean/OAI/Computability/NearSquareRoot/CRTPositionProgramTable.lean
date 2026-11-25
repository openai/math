import OAI.Computability.NearSquareRoot.CRTPositionProgramNative
import OAI.Computability.NearSquareRoot.CRTPositionProgramTableHeader
import OAI.Computability.NearSquareRoot.CRTControlledDispatch
import OAI.Computability.NearSquareRoot.CRTPositionOpcodeStage

/-! # The uniform table regime for a flat position-permutation sweep -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionProgram

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip IntegerMultiplication.Adic IntegerMultiplication.Loom Reflections

/-- This family ranges over all record widths before the opcode program or its
polynomial degree is selected. -/
structure TableShape where
  k : ℕ
  p : Equiv.Perm (Fin k)
  width : ℕ

namespace TableShape

abbrev Data (s : TableShape) := Block 2 s.k → Fin s.width → Bead
def stream (s : TableShape) := assemble (tally (guardWidth s.k),table s.p)
def key (s : TableShape) (q : Op) := send (tally s.k,q)
noncomputable def packet (s : TableShape) (f : s.Data) := stripe (line 2 s.k) (fun a => stripe (Series.natural s.width) (send ∘ f a))

noncomputable def rowStep (s : TableShape) (q : Op) (f : s.Data) := f ∘ nativeOp s.k (guardWidth s.k) q

noncomputable def rowPerm (s : TableShape) (q : Op) : Equiv.Perm s.Data :=
  (show Function.Involutive (rowStep s q) from by
    intro f; funext a; exact congrArg f (nativeOp_twice _ _ q a)).toPerm (rowStep s q)

end TableShape

abbrev StageCase := (s : TableShape) × {q // q ∈ s.stream} × s.Data

def tableRegime : Regime StageCase where
  scale := fun i => i.1.k
  header := fun i => i.1.key i.2.1
  gauge := tableHeader_key_dom (fun i : StageCase => i.1.k) (fun i => i.1.p) (fun i => i.2.1.val) (fun i => i.2.1.property)

theorem table_width : tableRegime.Has (fun i : StageCase => tally i.1.k) := by
  have h : tableRegime.Has (fun i : StageCase => (tally i.1.k,i.2.1.val)) := Regime.self
  exact h.ez Easy.fst

theorem table_opcode : tableRegime.Has (fun i : StageCase => i.2.1.val) := by
  have h : tableRegime.Has (fun i : StageCase => (tally i.1.k,i.2.1.val)) := Regime.self
  exact h.ez Easy.snd

theorem table_wf (i : StageCase) : WellFormed i.1.k (guardWidth i.1.k) i.2.1.val :=
  assemble_valid i.1.p _ i.2.1.property

/-- One uniform instance of physical opcode execution on all image tables,
legal emitted stages, record widths and intermediate arrays. -/
abbrev TableDispatcher (ρ : ℝ) :=
  Breeze (Spindle.modes (fun i : StageCase => i.1.k) (τ := ρ)) tableRegime (fun i => (line 2 i.1.k).count)
    (fun i => i.1.width) (fun i => Tree.fork (i.1.key i.2.1) (i.1.packet i.2.2))
    (fun i => i.1.packet (i.1.rowStep i.2.1 i.2.2))

theorem tableDispatcher {ρ : ℝ} (hρ : 1/2 < ρ) : TableDispatcher ρ :=
  opcodeStage hρ (fun i : StageCase => i.1.k) (fun i => i.2.1.val) table_width table_opcode
    table_wf (fun i => Series.natural i.1.width) (by intro i; simp) (fun i => i.2.2)

noncomputable def tableMass (ρ : ℝ) (s : TableShape) (d : ℕ) : ℝ :=
  ((2^s.k : ℕ):ℝ)*((s.width : ℝ)+((s.k+1 : ℕ):ℝ)^d)*((s.k+1 : ℕ):ℝ)^ρ

/-- A single finite P192 driver executes all serialized calls. Its degree
and the key-transport constant are independent of the payload width. -/
theorem table_sweep {ρ : ℝ} (dispatch : TableDispatcher ρ) :
    ∃ d C : ℕ, Task (fun i : (s : TableShape) × s.Data =>
      i.1.stream.length * ((C+2)*⌈tableMass ρ i.1 d⌉₊) + 1)
      (fun i => .fork (Task.forest i.1.key i.1.stream) (i.1.packet i.2))
      (fun i => i.1.packet (i.2 ∘ (permuteNative i.1.p).symm)) := by
  obtain ⟨_,d,carry⟩ := dispatch
  have hmass (i : StageCase) : runrate (Spindle.modes (fun i : StageCase => i.1.k) (τ := ρ)) tableRegime
      (fun i => (line 2 i.1.k).count) (fun i => i.1.width) d i = tableMass ρ i.1 d := by
    simp only [mass,runrate,lineSize,tableRegime,Spindle.modes,tableMass,Nat.cast_add,Nat.cast_one]
  obtain ⟨C,hC⟩ := carry.small.left
  let amt (s : TableShape) := ⌈tableMass ρ s d⌉₊
  have prog : Task (fun i : StageCase => amt i.1) (fun i => .fork (i.1.key i.2.1) (i.1.packet i.2.2))
      (fun i => i.1.packet (i.1.rowPerm i.2.1 i.2.2)) := by
    exact carry.runs.release.conform (fun i => congrArg Nat.ceil (hmass i)) (fun _ => rfl) (fun _ => rfl)
  have cost (s : TableShape) (q : Op) (hq : q ∈ s.stream) :
      amt s + (s.key q).count + 1 ≤ (C+2)*amt s := by
    let i : StageCase := ⟨s,⟨q,hq⟩,fun _ _ => 0⟩
    have cap : ((s.key q).count:ℝ) ≤ C * tableMass ρ s d := (hmass i) ▸ (hC i)
    have one : (1:ℝ) ≤ tableMass ρ s d := (hmass i) ▸ carry.budget i
    have big : 1 ≤ amt s := by exact_mod_cast one.trans (Nat.le_ceil _)
    have keycap : (s.key q).count ≤ C*amt s := by
      exact_mod_cast cap.trans (mul_le_mul_of_nonneg_left (Nat.le_ceil _) (Nat.cast_nonneg _))
    rw [Nat.add_mul]
    omega
  have t := physicalSchedule TableShape.stream TableShape.key TableShape.packet TableShape.rowPerm
    (fun s _ => amt s) (fun s => (C+2)*amt s) prog cost
  refine ⟨d,C,t.conform (fun _ => rfl) (fun _ => rfl) ?_⟩
  intro i
  apply congrArg i.1.packet
  exact assemble_native_rows (G := guardWidth i.1.k) (by simp [guardWidth]) i.1.p i.2

end Controlled.PositionProgram

end NearSquareRoot
end Computability
end OAI
