import OAI.Computability.BorderVNP.TeamTapeInputEmitWord
import Mathlib.Tactic.FinCases

/-! # Staging and appending one physical half of a team memory probe -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamProbeEmit

open VPVNP BurstRAM RAMTape RAMSerialization

/-- The four words carried by a logical memory probe. -/
inductive Operand where
  | address | tick | before | after
  deriving DecidableEq

instance : Fintype Operand where
  elems := {.address, .tick, .before, .after}
  complete k := by cases k <;> decide

/-- Original inputs, widened copies, the record buffer and a scratch port. -/
inductive Port where
  | operand (k : Operand)
  | lifted (k : Operand)
  | buffer (p : RecordBuffer.Port)
  | temp
  deriving DecidableEq, Fintype

/-- A single read or write half of the probe in the sorting word format. -/
def half {W : ℕ} (z : Operand → Word W) (phase : Bool) : WordRecord W :=
  ⟨if phase then .write else .read, z .address, if phase then z .after else z .before,
   z .tick, Fin.ofNat (2^W) (2*(z .address).val+phase.toNat)⟩

/-- The staged fields have bounded widths, and the widened operands remain available. -/
structure Ready {W : ℕ} (hw : 2 ≤ W) (H : ℕ) (z : Operand → Word W)
    (rs : List (WordRecord W)) (s : Stacks Port) : Prop where
  lifted : ∀ k, s (.lifted k) = BurstRAM.wordBits (z k)
  buffer : RecordBuffer.Holds hw H rs (s ∘ Port.buffer)
  fields : ∀ j, (s (.buffer (.field j))).length ≤ W

private def source (phase : Bool) : Fin 5 → Operand :=
  ![.address, .address, if phase then .after else .before, .tick, .address]

private def operation (phase : Bool) : Fin 5 → TeamTapeInputEmit.Op :=
  ![.literal (if phase then 3 else 2), .copy, .copy, .copy, .double phase]

private def ports (k : Operand) : TeamTapeInputEmit.Port → Port
  | .bits => .temp
  | .cursor => .lifted k
  | .buffer p => .buffer p

private theorem ports_inj (k : Operand) : Function.Injective (ports k) := by
  intro a b he
  cases a <;> cases b <;> simp_all [ports]

variable {W H : ℕ} {hw : 2 ≤ W} {z : Operand → Word W}
variable {rs : List (WordRecord W)} {s : Stacks Port} {phase : Bool}

private theorem field_value (ha : 2*(z .address).val+phase.toNat < 2^W) (j : Fin 5) :
    Fin.ofNat (2^W) ((operation phase j).eval (z (source phase j)).val) =
      (recordFormat hw).words (some (half z phase)) j := by
  have small : 4 ≤ 2^W := Nat.pow_le_pow_right (by decide : 0 < 2) hw
  have hz (k : Operand) : (z k).val < 2^W := (z k).isLt
  have haddr : (z .address).val < 2^W := by omega
  fin_cases j <;> cases phase <;> apply Fin.ext <;>
    first | rfl | (change (_ % (2^W)) = _; simp [operation, source, TeamTapeInputEmit.Op.eval,
      half, recordFormat, Nat.mod_eq_of_lt (show 2 < 2^W by omega),
      Nat.mod_eq_of_lt (show 3 < 2^W by omega)]; first | rfl | exact Nat.mod_eq_of_lt haddr | exact Nat.mod_eq_of_lt (hz _))

private def load (phase : Bool) (j : Fin 5) : FiniteRoutine Port :=
  (TeamTapeInputEmit.load (.stage j) (operation phase j)).onPorts (ports (source phase j))

private theorem load_runs (ready : Ready hw H z rs s) (ha : 2*(z .address).val+phase.toNat < 2^W)
    (j : Fin 5) :
    (load phase j).Runs ((s (.buffer (.field j))).length+7*W+3) s
      (Function.update s (.buffer (.field j)) (BurstRAM.wordBits ((recordFormat hw).words (some (half z phase)) j))) := by
  let p := ports (source phase j)
  have h := TeamTapeInputEmit.load_runs (.stage j) (operation phase j) (s ∘ p)
    (z (source phase j)) (ready.lifted _) ready.buffer.scratch ready.buffer.output
  simp only [TeamTapeInputEmit.Move.dst] at h
  rw [field_value (hw := hw) ha j] at h
  apply FiniteRoutine.runs_onPorts_framed _ (ports_inj _) h (fun _ => rfl)
  · intro k
    cases k with
    | bits | cursor => simp [ports, p]
    | buffer i =>
      by_cases hi : i = .field j <;> simp [ports, p, hi]
  · intro k hk
    exact Function.update_of_ne (Ne.symm (hk (.buffer (.field j)))) ..

private theorem updateField (ready : Ready hw H z rs s) (j : Fin 5) (v : Word W) :
    Ready hw H z rs (Function.update s (.buffer (.field j)) (BurstRAM.wordBits v)) := by
  refine ⟨fun k => by simpa using ready.lifted k, ?_, ?_⟩
  · obtain ⟨h1,h2,h3,h4,h5,h6⟩ := ready.buffer
    exact ⟨h1, by simpa using h2, by simpa using h3, by simpa using h4,
      by simpa using h5, by simpa using h6⟩
  · intro i
    by_cases hij : i = j
    · subst i; simp
    · simpa [hij] using ready.fields i

private def stage (phase : Bool) : List (Fin 5) → FiniteRoutine Port
  | [] => .ret
  | j :: js => (load phase j).followedBy (stage phase js)

private theorem stage_runs (ready : Ready hw H z rs s) (ha : 2*(z .address).val+phase.toNat < 2^W)
    (js : List (Fin 5)) :
    ∃ t out, t ≤ js.length*(8*W+3)+1 ∧ (stage phase js).Runs t s out ∧
      Ready hw H z rs out ∧ (∀ k, out (.operand k) = s (.operand k)) ∧ out .temp = s .temp ∧
      ∀ j, out (.buffer (.field j)) =
        if j ∈ js then BurstRAM.wordBits ((recordFormat hw).words (some (half z phase)) j)
        else s (.buffer (.field j)) := by
  induction js generalizing s with
  | nil => exact ⟨1,s,by simp,Routine.runs_ret s,ready,fun _ => rfl,rfl,by simp⟩
  | cons j js ih =>
    let v := (recordFormat hw).words (some (half z phase)) j
    let mid := Function.update s (.buffer (.field j)) (BurstRAM.wordBits v)
    obtain ⟨t,out,ht,hr,hs,hk,htmp,hf⟩ := ih (s := mid) (updateField ready j v)
    refine ⟨_,out,?_,(load_runs ready ha j).followedBy hr, hs,
      fun k => by simpa [mid] using hk k, by simpa [mid] using htmp, ?_⟩
    · rw [List.length_cons, Nat.succ_mul js.length (8*W+3)]; have := ready.fields j; omega
    · intro i
      rw [hf]
      by_cases hi : i ∈ js <;> by_cases hj : i = j <;> simp_all [mid, v]

/-- Stage the five fields of one probe half and append their serialized slot. -/
def emitHalf (phase : Bool) : FiniteRoutine Port :=
  (stage phase (List.finRange 5)).followedBy (RecordBuffer.appendRecord.onPorts Port.buffer)

/-- Emitting a physical probe half uses one free slot and preserves the input operands
and scratch port. The tick and phase ordinal are the ones used by the physical sorter. -/
theorem emitHalf_runs (ready : Ready hw H z rs s) (ha : 2*(z .address).val+phase.toNat < 2^W)
    (free : rs.length < 4*H) :
    ∃ t out, t ≤ 65*W+28 ∧ (emitHalf phase).Runs t s out ∧
      Ready hw H z (rs ++ [half z phase]) out ∧
      (∀ k, out (.operand k) = s (.operand k)) ∧ out .temp = s .temp := by
  obtain ⟨t,mid,ht,hr,hm,hk,htmp,hfields⟩ := stage_runs ready ha (List.finRange 5)
  let r := half z phase
  have hf (j : Fin 5) : mid (.buffer (.field j)) = BurstRAM.wordBits ((recordFormat hw).words (some r) j) :=
    by simpa only [List.mem_finRange, ite_true] using hfields j
  obtain ⟨em, holds⟩ := hm.buffer.emit free r hf
  let small := RecordBuffer.emitted (mid ∘ Port.buffer) (List.replicate (4*H-(rs.length+1)) true)
    (List.ofFn ((recordFormat hw).encode (some r)))
  let out := installStacks Port.buffer mid small
  have hu (k : RecordBuffer.Port) : out (.buffer k) = small k :=
    installStacks_at (fun _ _ he => Port.buffer.inj he) ..
  have ho {k : Port} (hk' : ∀ p, Port.buffer p ≠ k) : out k = mid k := installStacks_outside _ _ hk'
  have he : (RecordBuffer.appendRecord.onPorts Port.buffer).Runs (25*W+12) mid out :=
    RecordBuffer.appendRecord.runs_onPorts_framed (fun _ _ hh => Port.buffer.inj hh) em
      (fun _ => rfl) hu (fun _ h => ho h)
  refine ⟨_,out,?_,hr.followedBy he,?_,fun k => (ho (by simp)).trans (hk k), (ho (by simp)).trans htmp⟩
  · rw [List.length_finRange] at ht; omega
  · refine ⟨fun k => (ho (by simp)).trans (hm.lifted k), ?_, ?_⟩
    · have eq : out ∘ Port.buffer = small := funext hu
      rw [eq]; exact holds
    · intro j
      rw [hu]
      simpa [small, RecordBuffer.emitted] using hm.fields j

end TeamProbeEmit

end BorderVNP
end Computability
end OAI
