import OAI.Computability.NearSquareRoot.CRTPositionOpcodeCall
import OAI.Computability.NearSquareRoot.CRTPositionEffectiveSweep
import OAI.Computability.NearSquareRoot.CRTPositionProgramTableRun
import OAI.Computability.NearSquareRoot.CRTPositionRowCommandClock

/-! # A generated P192 command for the complete position-table sweep -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionProgram

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Adic IntegerMultiplication.Strip
open IntegerMultiplication.Loom CommonRegisters GeneratorSyntax Reflections Filter
open EffectiveTask NamedPacked

private def HeaderRuns (c : Cmd) : Prop :=
  ∃ a B : ℕ, Runs c (fun i : (s : TableShape) × s.Data => B*(i.1.k+1)^a)
    (fun i => Tree.fork (send (table i.1.p)) (i.1.packet i.2))
    (fun i => Tree.fork (Task.forest i.1.key i.1.stream) (i.1.packet i.2))

private theorem header_exists : ∃ c : Cmd, HeaderRuns c := by
  obtain ⟨b,⟨a,B,cap⟩,h⟩ := tableHeader_setup TableShape.k TableShape.p
  obtain ⟨c,run⟩ := ((h.mono cap).on (fun i : (s : TableShape) × s.Data => i.1)).left (fun i => i.1.packet i.2)
  exact ⟨c,a,B,run⟩

private noncomputable def tablePrepCmd : Cmd := header_exists.choose

/-- The image-table compiler is a fixed command. Only the opcode callback
changes with the outer parameter. -/
noncomputable def tableCmd (c : Cmd) : Cmd := tablePrepCmd.join (sweepCmd c)

theorem tableCmd_effective {P : Type} [Primcodable P] {f : P → Cmd} (h : Effective ltr f) :
    Effective ltr (fun j => tableCmd (f j)) := (effective_const _ _).join (effective_sweepCmd h)

theorem tableCmd_within (R : ℕ) : ∃ S : ℕ, 0 < S ∧ ∀ c, Within R c → Within S (tableCmd c) := by
  obtain ⟨S,room,fixed⟩ := ((eventually_ge_atTop (max 3 R)).and (RegisterSelect.within_eventually tablePrepCmd)).exists
  have three : 3 ≤ S := (le_max_left ..).trans room
  have keep : R ≤ S := (le_max_right ..).trans room
  exact ⟨S,by omega,fun c hc => ⟨fixed,within_sweepCmd three (RegisterSelect.within_mono keep c hc)⟩⟩

private theorem sweep_runs {c : Cmd} {ρ : ℝ} (dispatch : OpAt c ρ id) :
    ∃ d C : ℕ, Runs (sweepCmd c) (fun i : (s : TableShape) × s.Data =>
      i.1.stream.length * ((C+2)*⌈tableMass ρ i.1 d⌉₊) + 1)
      (fun i => .fork (Task.forest i.1.key i.1.stream) (i.1.packet i.2))
      (fun i => i.1.packet (i.2 ∘ (permuteNative i.1.p).symm)) := by
  obtain ⟨_,d,carry⟩ := opAt_table dispatch
  have hmass (i : StageCase) : runrate (Spindle.modes (fun i : StageCase => i.1.k) (τ := ρ)) tableRegime
      (fun i => (line 2 i.1.k).count) (fun i => i.1.width) d i = tableMass ρ i.1 d := by
    simp only [mass,runrate,lineSize,tableRegime,Spindle.modes,tableMass,Nat.cast_add,Nat.cast_one]
  obtain ⟨C,hC⟩ := carry.small.left
  let amt (s : TableShape) := ⌈tableMass ρ s d⌉₊
  have prog : Runs c (fun i : StageCase => amt i.1) (fun i => .fork (i.1.key i.2.1) (i.1.packet i.2.2))
      (fun i => i.1.packet (i.1.rowPerm i.2.1 i.2.2)) :=
    carry.release.conform (fun i => congrArg Nat.ceil (hmass i)) (fun _ => rfl) (fun _ => rfl)
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
  have run := physicalScheduleRuns TableShape.stream TableShape.key TableShape.packet TableShape.rowPerm
    (fun s _ => amt s) (fun s => (C+2)*amt s) c prog cost
  refine ⟨d,C,run.conform (fun _ => rfl) (fun _ => rfl) ?_⟩
  intro i
  exact congrArg i.1.packet (assemble_native_rows (G := guardWidth i.1.k) (by simp [guardWidth]) i.1.p i.2)

/-- One slack exponent works for all word widths, image tables, real payload
widths, and contents. The same named program runs at every one of them. -/
theorem tableCmd_runs {c : Cmd} {ρ : ℝ} (positive : 0 ≤ ρ) (dispatch : OpAt c ρ id) :
    ∃ D : ℕ, ∀ {X : Type} (k : X → ℕ) (p : (x : X) → Equiv.Perm (Fin (k x)))
      {U : X → Type} (u : (x : X) → Series (U x)) (f : (x : X) → Block 2 (k x) → U x → Bead),
      Runs (tableCmd c) (fun x => ⌈tableRate ρ (k x) ((u x).count+(k x+1)^D)⌉₊)
        (together (fun x => send (table (p x))) (cloth (fun x => line 2 (k x)) u f))
        (cloth (fun x => line 2 (k x)) u (fun x a => f x ((permuteNative (p x)).symm a))) := by
  obtain ⟨d,C,sweep⟩ := sweep_runs dispatch
  obtain ⟨a,B,setup⟩ : HeaderRuns tablePrepCmd := header_exists.choose_spec
  let D := max a d
  refine ⟨D,?_⟩
  intro X k p U u f
  let s (x : X) : TableShape := ⟨k x,p x,(u x).count⟩
  let forward (x : X) (v : Block 2 (k x) → U x → Bead) : (s x).Data :=
    fun b i => v b ((u x).follow i)
  let row (x : X) : (s : TableShape) × s.Data := ⟨s x,forward x (f x)⟩
  have packed (x : X) (v : Block 2 (k x) → U x → Bead) :
      (s x).packet (forward x v) = stripe (line 2 (k x)) (fun y => stripe (u x) (fun t => send (v y t))) := by
    apply congrArg (stripe _)
    funext t
    exact stripe_natural_follow (u x) (fun i => send (v t i))
  have r := (setup.comp sweep).on row
  have t := r.conform (fun _ => rfl)
    (show ∀ x : X, _ = together (fun x => send (table (p x))) (cloth (fun x => line 2 (k x)) u f) x from
      fun x => congrArg (Tree.fork (send (table (p x)))) (packed x (f x)))
    (show ∀ x : X, _ = cloth (fun x => line 2 (k x)) u (fun x y => f x ((permuteNative (p x)).symm y)) x from
      fun x => packed x (fun y => f x ((permuteNative (p x)).symm y)))
  apply t.bound (B + 5412*(C+2) + 2)
  intro x
  let K := B + 5412*(C+2) + 2
  let rate := tableRate ρ (k x) ((u x).count+(k x+1)^D)
  have le := table_raw_clock_le positive (s x) a d D B C (le_max_left ..) (le_max_right ..)
  have cl : B*((s x).k+1)^a + (s x).stream.length*((C+2)*⌈tableMass ρ (s x) d⌉₊) + 2 ≤ K*⌈rate⌉₊ := by
    exact_mod_cast le.trans (mul_le_mul_of_nonneg_left (Nat.le_ceil rate) (Nat.cast_nonneg K))
  exact (by simpa only [Function.comp_apply,row,Nat.add_assoc] using cl : _ ≤ K*⌈rate⌉₊) |>.trans
    (Nat.mul_le_mul_left K (Nat.le_succ _))

theorem tableCmd_grouped {c : Cmd} {ρ : ℝ} (positive : 0 ≤ ρ) (dispatch : OpAt c ρ id) :
    PositionRows.RowCommand.GroupedRuns (tableCmd c) ρ := by
  obtain ⟨D,run⟩ := tableCmd_runs positive dispatch
  exact PositionRows.RowCommand.groupedRunsOfClock positive D
    (run _ _ PositionRows.RowCommandLow.wide PositionRows.RowCommandLow.data)

end Controlled.PositionProgram

end NearSquareRoot
end Computability
end OAI
