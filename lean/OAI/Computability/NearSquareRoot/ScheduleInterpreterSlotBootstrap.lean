import OAI.Computability.NearSquareRoot.ScheduleInterpreterSlotBackground

/-! # Installing an initial scheduler frame from a fenced-tape computation

The raw computation synchronously writes a working symbol and its rollback
snapshot. Once it halts, one stationary step places cursor and frontier marks
under the heads. When the raw computation returns its heads to zero, all these
marks lie at the absolute origin.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Uniform.SlotBoot

open IntegerMultiplication TM SlotLayout
variable {A G I : Type}

/-- The two copies of a payload and its three frontier marks. -/
def cell (o : Bool) (v : PublishedAttempt.Payload A) : Letter A :=
  (none, ⟨v, v, o, o, o⟩)

def park (v : Fence.Symbol A) : Letter A := cell false (.inl v)

private def readWork (rawBlank : A) (v : Letter A) : Fence.Symbol A :=
  v.2.val.elim id (fun _ => (rawBlank, false, false))

def staged (lit : PublishedAttempt.Symbol A) (raw : I → Tape (Fence.Symbol A)) :
    Axis I → Tape (Letter A)
  | .inr (some (.inl k)) => ⟨(raw k).pos, fun p => park ((raw k).view p)⟩
  | .inr (some (.inr _)) => ⟨0, fun _ => cell false (.inr none)⟩
  | .inl _ | .inr none => ⟨0, fun _ => (none, lit)⟩

def ready (lit : PublishedAttempt.Symbol A) (raw : I → Tape (Fence.Symbol A)) :
    Axis I → Tape (Letter A)
  | .inr (some (.inl k)) => ⟨(raw k).pos, fun p => cell (decide (p=0)) (.inl ((raw k).view p))⟩
  | .inr (some (.inr _)) => ⟨0, fun p => cell (decide (p=0)) (.inr none)⟩
  | .inl _ => ⟨0, fun p => (if p=0 then some true else none, lit)⟩
  | .inr none => ⟨0, fun _ => (none, lit)⟩

private def writeWork (r : Axis I → Letter A) (op : I → Fence.Symbol A × Move)
    (j : Axis I) : Letter A × Move :=
  match j with
  | .inr (some (.inl k)) => (park (op k).1, (op k).2)
  | _ => (r j, .stay)

private def install (j : Axis I) (v : Letter A) : Letter A :=
  match j with
  | .inl _ => (some true, v.2)
  | .inr none => v
  | .inr (some _) => (v.1, {v.2 with origin := true, leftEnd := true, rightEnd := true})

def rule (rawBlank : A) (m : Rule (Fence.Symbol A) G I) : Rule (Letter A) (Option G) (Axis I)
  | none, _ => none
  | some q, r =>
    match m q (fun k => readWork rawBlank (r (.inr (some (.inl k))))) with
    | some (q', op) => some (some q', writeWork r op)
    | none => some (none, fun j => (install j (r j), .stay))

variable (rawBlank : A) (m : Rule (Fence.Symbol A) G I) (lit : PublishedAttempt.Symbol A)

private theorem write_staged (raw : I → Tape (Fence.Symbol A)) (op : I → Fence.Symbol A × Move)
    (j : Axis I) :
    (staged lit raw j).apply (writeWork (fun i => (staged lit raw i).view 0) op j) =
      staged lit (fun k => (raw k).apply (op k)) j := by
  obtain b | (_ | (k | b)) := j
  · simp [staged, writeWork, Tape.apply, Move.shift]
  · simp [staged, writeWork, Tape.apply, Move.shift]
  · simp only [staged, writeWork, Tape.apply, Tape.mk.injEq, true_and]
    funext p
    by_cases h : p + (op k).2.shift = 0 <;> simp [h]
  · simp [staged, writeWork, Tape.apply, Move.shift]

private theorem read_staged (raw : I → Tape (Fence.Symbol A)) (k : I) :
    readWork rawBlank ((staged lit raw (.inr (some (.inl k)))).view 0) = (raw k).view 0 := rfl

private theorem step {x y : Config (Fence.Symbol A) G I} (h : advance m x = some y) :
    advance (rule rawBlank m) ⟨some x.pc, staged lit x.tape⟩ =
      some ⟨some y.pc, staged lit y.tape⟩ := by
  cases e : m x.pc (fun k => (x.tape k).view 0) with
  | none => simp [advance, e] at h
  | some a =>
    obtain ⟨q, op⟩ := a
    simp only [advance, e, Option.map_some, Option.some.injEq] at h
    subst y
    simp only [advance, rule, read_staged, e, Option.map_some, Option.some.injEq,
      Config.mk.injEq, true_and]
    exact funext (write_staged lit x.tape op)

theorem trace {x y : Config (Fence.Symbol A) G I} {k : ℕ} (h : Trace (advance m) x k y) :
    Trace (advance (rule rawBlank m)) ⟨some x.pc, staged lit x.tape⟩ k
      ⟨some y.pc, staged lit y.tape⟩ := by
  induction h with
  | nil => exact .nil _
  | cons h _ ih => exact .cons (step rawBlank m lit h) ih

private theorem install_staged (raw : I → Tape (Fence.Symbol A)) (j : Axis I) :
    (staged lit raw j).apply (install j ((staged lit raw j).view 0), .stay) = ready lit raw j := by
  obtain b | (_ | (k | b)) := j <;>
    simp only [staged, ready, install, Tape.apply, Move.shift, add_zero, Tape.mk.injEq, true_and] <;>
    funext p <;> by_cases h : p = 0 <;> simp [h, park, cell]

theorem finish {y : Config (Fence.Symbol A) G I} (stop : advance m y = none) :
    advance (rule rawBlank m) ⟨some y.pc, staged lit y.tape⟩ = some ⟨none, ready lit y.tape⟩ := by
  have h : m y.pc (fun k => (y.tape k).view 0) = none := by simpa [advance] using stop
  simp only [advance, rule, read_staged, h, Option.map_some, Option.some.injEq,
    Config.mk.injEq, true_and]
  exact funext (install_staged lit y.tape)

@[simp] theorem halt (tapes : Axis I → Tape (Letter A)) :
    advance (rule rawBlank m) ⟨none, tapes⟩ = none := rfl

theorem bootstrap {x y : Config (Fence.Symbol A) G I} {k : ℕ}
    (run : Trace (advance m) x k y) (stop : advance m y = none) :
    Trace (advance (rule rawBlank m)) ⟨some x.pc, staged lit x.tape⟩ (k+1) ⟨none, ready lit y.tape⟩ :=
  (trace rawBlank m lit run).trans (.single (finish rawBlank m lit stop))

end Uniform.SlotBoot

end NearSquareRoot
end Computability
end OAI
