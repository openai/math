import OAI.Computability.NearSquareRoot.ScheduleInterpreterSlotPreparation
import OAI.Computability.NearSquareRoot.ScheduleInterpreterSlotCost
import OAI.Computability.NearSquareRoot.ScheduleInterpreterSpace

/-!
# Running a published attempt on the scheduler's physical tapes

The two cursor heads remain parked throughout the middle phase. The other
heads run the trial under an immutable tally track, including the published
output at the untagged output port.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Uniform.SlotLift

open IntegerMultiplication TM SlotLayout

variable {I D Q : Type}

def bankPort : Bank I ↪ Axis I := ⟨Sum.inr, Sum.inr_injective⟩

noncomputable def trial (m : Rule D Q (Bank I)) : Rule (Option Bool × D) Q (Axis I) :=
  CommonTapes.rule bankPort (SlotTracks.dataRule m)

noncomputable def mount (frame : Axis I → Tape (Option Bool × D)) (tag : Bank I → ℤ → Option Bool)
    (x : Config D Q (Bank I)) : Config (Option Bool × D) Q (Axis I) :=
  CommonTapes.config bankPort frame (SlotTracks.dataCfg tag x)

variable (m : Rule D Q (Bank I)) (frame : Axis I → Tape (Option Bool × D))
    (tag : Bank I → ℤ → Option Bool)

@[simp] theorem mount_pc (x : Config D Q (Bank I)) : (mount frame tag x).pc = x.pc := rfl

@[simp] theorem mount_bank (x : Config D Q (Bank I)) (j : Bank I) :
    (mount frame tag x).tape (.inr j) = SlotTracks.dataTape (tag j) (x.tape j) := by
  apply CommonTapes.extend_apply

@[simp] theorem mount_cursor (x : Config D Q (Bank I)) (b : Bool) :
    (mount frame tag x).tape (.inl b) = frame (.inl b) := by
  apply CommonTapes.extend_off
  simp [bankPort]

theorem mount_output {x : Config D Q (Bank I)} (blank : D) (bit : Bool → D) (z : List Bool)
    (outputTag : ∀ p, tag none p = none) (out : whole blank (z.map bit) (x.tape none)) :
    whole (none,blank) (z.map fun b => (none,bit b)) ((mount frame tag x).tape (.inr none)) := by
  rw [mount_bank]
  funext p
  change (tag none _,(x.tape none).absolute p) = _
  rw [outputTag,congrFun out p]
  cases p with
  | negSucc => rfl
  | ofNat k =>
    simp only [Tape.absolute,Tape.loaded,Int.sub_zero,List.getElem?_map]
    cases z[k]? <;> rfl

theorem fenced_run {x y : Config D Q (Bank I)} {t U R : ℕ}
    (run : Trace (advance m) x t y) (halt : advance m y = none)
    (space : VisitsAtMost m x t U) (hU : U ≤ R) (origin : ∀ j, (x.tape j).pos = 0)
    (parked : ∀ b : Bool, -(R : ℤ) ≤ (frame (.inl b)).pos ∧ (frame (.inl b)).pos ≤ R) :
    FencedRun (trial m) (fun _ => -(R : ℤ)) (fun _ => (R : ℤ)) (mount frame tag x) t (mount frame tag y) ∧
      advance (trial m) (mount frame tag y) = none := by
  have hist {x' : Config D Q (Bank I)} {k} (h : Trace (advance m) x k x') :
      Trace (advance (trial m)) (mount frame tag x) k (mount frame tag x') :=
    CommonTapes.trace _ _ _ (SlotTracks.data_trace _ _ h)
  refine ⟨⟨hist run, ?_⟩, ?_⟩
  · intro k hk c hc j
    obtain ⟨v,hv,_⟩ := trace_split run hk
    rw [trace_endpoint_unique hc (hist hv)]
    cases j with
    | inl b => simpa only [mount_cursor] using parked b
    | inr j =>
      rw [mount_bank]
      have hh := radius_of_visits space hk hv j
      rw [origin j] at hh
      change -(R : ℤ) ≤ (v.tape j).pos ∧ (v.tape j).pos ≤ R
      omega
  · unfold trial mount
    rw [CommonTapes.advance_config,SlotTracks.advance_data,halt]
    rfl

section

variable {A U : Type} [DecidableEq I]
variable (start : U) (input : I → Tape A) (idx : I) (blank mark : A)
    (lit : PublishedAttempt.Symbol A) (lo hi : I → ℤ) (i a : ℕ)
local notation "F" => SlotLayout.frame start input idx blank mark lit lo hi i a i a
local notation "X" => published start input idx blank mark lit lo hi i a

theorem mount_start : mount F (tags idx i a) X = ⟨(X).pc,F⟩ := by
  apply congrArg (Config.mk (X).pc)
  funext j
  cases j with
  | inl b => exact mount_cursor _ _ _ b
  | inr j => exact mount_bank _ _ _ j

theorem mount_reject {V : Type} (y : Config (PublishedAttempt.Symbol A) V (Bank I))
    (restore : y.tape = (X).tape) : (mount F (tags idx i a) y).tape = F := by
  funext j
  cases j with
  | inl b => exact mount_cursor _ _ _ b
  | inr j => rw [mount_bank,restore]; rfl

theorem cursor_range (R : ℕ) (hi' : i ≤ R) (ha : a ≤ R) (b : Bool) :
    -(R : ℤ) ≤ (F (.inl b)).pos ∧ (F (.inl b)).pos ≤ R := by
  rw [cursor_eq]
  cases b
  · change -(R : ℤ) ≤ (i : ℤ) ∧ (i : ℤ) ≤ R
    omega
  · change -(R : ℤ) ≤ (a : ℤ) ∧ (a : ℤ) ≤ R
    omega

theorem published_origin (inputOrigin : ∀ j, (input j).pos = 0)
    (j : Bank I) : ((X).tape j).pos = 0 := by
  cases j with
  | none => rfl
  | some j =>
    cases j with
    | inr b => rfl
    | inl k =>
      change ((raw start input idx blank mark i).tape k).pos = 0
      by_cases h : k=idx <;> simp [raw,h,inputOrigin]

end

end Uniform.SlotLift

end NearSquareRoot
end Computability
end OAI
