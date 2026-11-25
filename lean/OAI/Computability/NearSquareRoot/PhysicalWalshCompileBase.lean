import OAI.Computability.NearSquareRoot.PhysicalWalshNodeBase
import OAI.Computability.NearSquareRoot.ScheduleRegisterSelect
import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntax

/-! # One terminal command for all selected-bit templates

At level zero every arity has exactly two active bits. The descriptor, record
order and four-point transformation therefore agree with those for arity one.
The command below is selected once from a single family of all guarded terminal
inputs. Its compiler file and data-register bound are uniform across templates.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompile

open IntegerMultiplication Code Space Filter PhysicalWalshNode KernelPass
open GeneratorSyntax CommonRegisters

/-- A terminal command and its common time and space bounds over all arities. -/
structure TerminalProgram where
  command : Cmd
  degree : ℕ
  factor : ℕ
  run : ∀ A s (x : Data s), s.level = 0 → baseGuard s x → ∀ env parked b,
    DeckCap b parked →
    BoundedFits env command (pile 0 (buffer A s x) parked) (pile 0 (buffer A s (base s x)) parked)
      (factor*(allowance A degree s+1)) (b+factor*(allowance A degree s+1))
      (factor*(allowance A degree s+1))

private structure Input where
  s : Shape
  row : Data s
  zero : s.level = 0
  room : baseGuard s row

private theorem terminal_exists : Nonempty TerminalProgram := by
  obtain ⟨d,c,C,program⟩ := baseBounded 1 Input.s Input.row Input.zero Input.room
  refine ⟨⟨c,d,C,?_⟩⟩
  intro A s x hz room env parked b hb
  have sameCount : count 1 s = count A s := (base_count 1 s hz).trans (base_count A s hz).symm
  have sameWire : Header.wire 1 s = Header.wire A s := by simp [Header.wire,grow,hz]
  have sameFlat (y : Data s) : flat 1 s y = flat A s y := by simp only [flat,sameCount]
  have sameScale : Header.scale 1 s = Header.scale A s := congrArg size sameWire
  have h := program ⟨s,x,hz,room⟩ env parked b hb
  dsimp only at h
  rw [sameCount,sameWire,sameFlat,sameFlat,sameScale] at h
  have cost : (count A s+1)*(s.w+1) + (Header.scale A s+1)^d ≤ allowance A d s := by
    apply Nat.add_le_add_right
    apply Nat.mul_le_mul_left
    omega
  have mono := Nat.mul_le_mul_left C (Nat.succ_le_succ cost)
  exact h.mono mono (Nat.add_le_add_left mono _) mono

/-- The fixed four-point terminal used by every compiled recursive program. -/
noncomputable def terminal : TerminalProgram := Classical.choice terminal_exists

theorem terminal_effective {I : Type} [Primcodable I] :
    Effective ltr (fun _ : I => terminal.command) := effective_const ltr _

theorem terminal_registers : ∀ᶠ R in atTop, Within R terminal.command :=
  RegisterSelect.within_eventually _

/-- The terminal transition of the recursive command with the precise layout
and invocation type used by `RecSpec`. -/
theorem terminal_closed {a W : ℕ} (hW : 0 < W) (p : Plan (a+1) W W) (scan arena : Shape → ℕ)
    (cost : ∀ s, arena s ≤ scan s) (capacity : ∀ s, allowance (a+1) terminal.degree s ≤ arena s) :
    let d := spec hW p scan arena cost
    PhysicalWalsh.ClosedRuns terminal.command (fun t : d.Base => scan t.val.shape)
      (fun t => arena t.val.shape) (fun t => d.payload t.val) (fun t => d.reply t.val) := by
  intro d
  refine ⟨terminal.factor,fun t env parked b hb => ?_⟩
  have hz : t.val.shape.level = 0 := t.property
  have h := terminal.run (a+1) t.val.shape t.val.row hz (good_base hW p hz t.val.representable) env parked b hb
  have ar := Nat.mul_le_mul_left terminal.factor (Nat.succ_le_succ (capacity t.val.shape))
  have tm := ar.trans (Nat.mul_le_mul_left _ (Nat.succ_le_succ (cost _)))
  change BoundedFits env terminal.command (pile 0 (buffer (a+1) t.val.shape t.val.row) parked)
    (pile 0 (buffer (a+1) t.val.shape (run hW p t.val.shape t.val.row)) parked) _ _ _
  rw [run_base hW p _ hz]
  exact h.mono tm (Nat.add_le_add_left ar _) ar

end PhysicalWalshCompile

end NearSquareRoot
end Computability
end OAI
