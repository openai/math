import OAI.Computability.NearSquareRoot.CRTControlledReservePrepare
import OAI.Computability.NearSquareRoot.PhysicalWalshParamLiterals
import OAI.Computability.NearSquareRoot.ScheduleRegisterSelectLink

/-! # Specializing the two reserve widths from the runtime position table -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionCmd

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Staff
open IntegerMultiplication.Carry IntegerMultiplication.Strip
open NearSquareRoot.GeneratorSyntax NearSquareRoot.CommonRegisters NearSquareRoot.KernelEffectiveFamily
open NearSquareRoot.EffectiveBoundedTask
open Reflections (Table table)

noncomputable section

private abbrev WidthInput := (Tally × Tally) × Table

/-- The two unary multipliers are decoded from the literal, and the logarithm is
computed from the length of the physical permutation table. -/
private def widthHeader (s : WidthInput) : Tally × Tally × Table :=
  (tally (payloadBits s.1.1.length s.2.length), tally (payloadBits s.1.2.length s.2.length), s.2)

private theorem widthHeader_poly : Poly widthHeader := by
  let r : Regime WidthInput := ⟨size,send,Dom.base _⟩
  have data : r.Has (id : WidthInput → WidthInput) := Poly.identity
  have tab : r.Has (fun z => z.2) := data.ez Easy.snd
  have decode {s : WidthInput → Tally} (h : r.Has s) : Realizes r (fun z => (s z).length) := by
    simpa only [Realizes, Function.comp_def, recover_tally] using h
  have a := decode ((data.ez Easy.fst).ez Easy.fst)
  have b := decode ((data.ez Easy.fst).ez Easy.snd)
  have n : Realizes r (fun z => z.2.length) := by
    have h := decode (tab.ez (Easy.ruler Easy.identity))
    simpa only [id_eq, ruler_length] using h
  have log := (Figure.of_spoken (n.plus (Realizes.fix 1))).short_log
  exact (a.times log).pair ((b.times log).pair tab)

private theorem widthHeader_value (a b : ℕ) {k : ℕ} (p : Equiv.Perm (Fin k)) :
    widthHeader ((tally a, tally b), table p) = (tally (payloadBits a k), tally (payloadBits b k), table p) := by
  simp [widthHeader, Reflections.table]

private theorem coreProgram : ∃ c : Cmd, ∃ t : WidthInput → ℕ, Dom size t ∧
    EffectiveScale.TimedAt c t send (send ∘ widthHeader) := by
  obtain ⟨t, poly, c, exec⟩ := widthHeader_poly
  exact ⟨c,t,poly,exec⟩

/-- The program first emits its two unary degrees, then runs the same table scan
for all parameters. The right sibling contains the uninterpreted payload. -/
def widthCmd (a b : ℕ) : Cmd := leftCmd (PhysicalWalsh.ParamLiterals.command a b coreProgram.choose)

theorem width_effective : Effective ltr (fun p : ℕ × ℕ => widthCmd p.1 p.2) :=
  effective_left (PhysicalWalsh.ParamLiterals.effective _)

theorem width_within : ∃ R : ℕ, 0 < R ∧ ∀ a b, Within R (widthCmd a b) := by
  obtain ⟨R, pos, h⟩ := ((Filter.eventually_gt_atTop 0).and (RegisterSelect.within_eventually coreProgram.choose)).exists
  exact ⟨R,pos,fun a b => within_left pos (PhysicalWalsh.ParamLiterals.within pos h a b)⟩

private theorem composedFile {J P : Type} [Primcodable J] [Primcodable P]
    (emit : J → Cmd) (he : Effective ltr emit) (q : P → J) (hq : Computable q) :
    Effective ltr (fun p => emit (q p)) :=
  Computable.comp (f := fun j => file ltr (emit j)) (g := q) he hq

theorem width_effective_on {P : Type} [Primcodable P] {a b : P → ℕ}
    (ha : Computable a) (hb : Computable b) :
    Effective ltr (fun p => widthCmd (a p) (b p)) :=
  composedFile (fun q : ℕ × ℕ => widthCmd q.1 q.2) width_effective (fun p => (a p,b p)) (ha.pair hb)

theorem width_within_eventually : ∀ᶠ R : ℕ in Filter.atTop, ∀ a b, Within R (widthCmd a b) := by
  obtain ⟨r, _, hr⟩ := width_within
  filter_upwards [Filter.eventually_ge_atTop r] with R hR a b
  exact RegisterSelect.within_mono hR _ (hr a b)

private theorem chargeHeader {I : Type} {k V t : I → ℕ} (area : ∀ i, 2^(k i) ≤ V i)
    (h : Dom k t) : ∃ A : ℕ, ∀ i, t i ≤ A*V i := by
  obtain ⟨d,C,hr⟩ := h
  obtain ⟨B, hB⟩ := polynomial_le_multiple_array_length d
  exact ⟨C*B,fun i => by
    rw [Nat.mul_assoc]
    exact (hr i).trans (Nat.mul_le_mul_left C ((hB (k i)).trans (Nat.mul_le_mul_left B (area i))))⟩

/-- Reserve preparation runs at linear cost in the array volume. It also computes
both widths when their sum exceeds the address width. -/
theorem width_runs {I : Type} (a b : ℕ) (k V : I → ℕ) (p : ∀ i, Equiv.Perm (Fin (k i)))
    (area : ∀ i, 2^(k i) ≤ V i) (data : I → Tree) (C : ℕ) (cap : ∀ i, (data i).count ≤ C*V i) :
    EffectiveBoundedTask.Runs (widthCmd a b) V V
      (fun i => .fork (send (table (p i))) (data i))
      (fun i => .fork (send (tally (payloadBits a (k i)),tally (payloadBits b (k i)), table (p i))) (data i)) := by
  obtain ⟨t, poly, run⟩ := coreProgram.choose_spec
  let input (i : I) : WidthInput := ((tally a,tally b),table (p i))
  have sizeTab : Dom k (fun i => size (table (p i))) := ⟨2,2,fun i => Reflections.table_size (p i)⟩
  have sizeInput : Dom k (fun i => size (input i)) := by
    simpa only [input, size_prod] using
      (((Dom.const k (size (tally a,tally b))).add sizeTab).add (Dom.const k 1))
  obtain ⟨A,hA⟩ := chargeHeader area ((poly.map input).sub sizeInput)
  obtain ⟨B,hB⟩ := chargeHeader area sizeTab
  let literal := PhysicalWalsh.ParamLiterals.literal a b
  have tag : EffectiveScale.TimedAt ((Task.prepare 0 literal).join (pack 0)) (fun _ : I => 0)
      (fun i => send (table (p i))) (fun i => send (input i)) :=
    command_contract ((Task.prepare 0 literal).join (pack 0)) from Task.supply literal (fun i => send (table (p i)))
  have head : EffectiveScale.TimedAt (PhysicalWalsh.ParamLiterals.command a b coreProgram.choose) V
      (fun i => send (table (p i)))
      (fun i => send (tally (payloadBits a (k i)),tally (payloadBits b (k i)),table (p i))) := by
    have h := EffectiveScale.TimedAt.join tag (EffectiveScale.TimedAt.on run input)
    have cut := EffectiveScale.TimedAt.bound (b := V) h (A+1) (fun i => by
      change 0 + t (input i) + 1 ≤ (A+1)*(V i+1)
      have := hA i
      change t (input i) ≤ A*V i at this
      simp only [Nat.add_mul, Nat.mul_add, one_mul, mul_one, zero_add]
      omega)
    have output : (send ∘ widthHeader) ∘ input =
        fun i => send (tally (payloadBits a (k i)), tally (payloadBits b (k i)), table (p i)) :=
      funext (fun i => congrArg send (widthHeader_value a b (p i)))
    rw [output] at cut
    exact cut
  have timed := EffectiveScale.TimedAt.left head data
  have result := EffectiveBoundedTask.Runs.of_time timed
  apply result.bound 1 (B+C+3)
  · intro i; simp
  · intro i
    change (send (table (p i))).count+(data i).count+1+V i+1 ≤ (B+C+3)*(V i+1)
    have sizeB : (send (table (p i))).count ≤ B*V i := hB i
    have hd := cap i
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
    omega

end
end Controlled.PositionCmd

end NearSquareRoot
end Computability
end OAI
