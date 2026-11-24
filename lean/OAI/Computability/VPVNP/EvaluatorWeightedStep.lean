import OAI.Computability.VPVNP.EvaluatorIndexRegisters
import OAI.Computability.VPVNP.EvaluatorRoutineFrame
import OAI.Computability.VPVNP.SliceArithmeticEncoding
import OAI.Computability.VPVNP.SliceArithmeticMultiplyCall

/-!
# The weighted matrix-step callback

After a legal next index has been chosen, the deterministic query writes its
field entry onto the multiplication input. The actual Horner bit-stack code
multiplies that entry by the running field product and clears its workspace.
Committing the ordinal leaves exactly the payload expected by the next call.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Evaluator.WeightedStep

open RAMTape SliceArithmetic
open SliceArithmeticRound (packed)

/-- The basis-index registers, field multiplication registers, limb-width tally and auxiliary
ports of a weighted matrix step. -/
inductive Port (P : Type) where
  | indices (i : IndexRegisters.Port)
  | arithmetic (i : MultiplyCall.Port)
  | width
  | aux (i : P)
  deriving DecidableEq, Fintype

variable {P : Type} {p e v w : ℕ} [Fact p.Prime]
    {K : Type} [Field K] [Algebra (ZMod p) K] {c : Vector p e}
    (φ : AdjoinRoot (modulus c) ≃ₐ[ZMod p] K)

/-- Physical coefficient representation used by the entry-query and
multiplication routines. -/
noncomputable def bits (w : ℕ) (x : K) := packed w (List.ofFn (scalarEncoding φ x))

/-- Call boundary, with an optional pending ordinal and a possibly occupied
query result port. The unary width register serves the terminal residue test. -/
noncomputable def bank (w : ℕ) (dim : BurstRAM.Word v) (i : Fin dim.val) (next query : List Bool)
    (acc : K) (extra : Stacks P) : Stacks (Port P)
  | .indices k => IndexRegisters.bank (BurstRAM.wordBits dim)
      (BurstRAM.wordBits (Fin.castLE dim.isLt.le i : BurstRAM.Word v)) next k
  | .arithmetic k => MultiplyCall.clean (MultiplyCall.external p e w
      (packed w (List.ofFn c)) query (bits φ w acc)) k
  | .width => List.replicate w true
  | .aux k => extra k

/-- The query may use additional disjoint ports of the enclosing caller.
The selection, field multiplication and commit instructions are fixed. -/
def callback {Q : Type} (ports : Port P → Q) (read : FiniteRoutine Q) : FiniteRoutine Q :=
  (((IndexRegisters.select.onPorts (ports ∘ Port.indices)).followedBy read).followedBy
    (MultiplyCall.machine.onPorts (ports ∘ Port.arithmetic))).followedBy
    (IndexRegisters.commit.onPorts (ports ∘ Port.indices))

variable {Q : Type} [DecidableEq Q] (ports : Port P → Q) (hports : Function.Injective ports)
    (ambient : Stacks Q) (extra : Stacks P) (dim : BurstRAM.Word v)

local notation "frame" => installStacks ports ambient
local notation "word" j => BurstRAM.wordBits (Fin.castLE dim.isLt.le j : BurstRAM.Word v)

include hports in
private theorem select_framed (i : Fin dim.val) (a : K) (cont : ℕ → Stacks Q → ℕ) (fuel : ℕ) :
    (IndexRegisters.select.onPorts (ports ∘ Port.indices)).body.count cont (fuel+(10*v+5))
      (frame (bank φ w dim i [] [] a extra)) =
      ∑ j : Fin dim.val, cont fuel (frame (bank φ w dim i (word j) [] a extra)) := by
  have hp : Function.Injective (ports ∘ Port.indices) :=
    hports.comp (fun _ _ h ↦ Port.indices.inj h)
  rw [FiniteRoutine.count_onPorts _ _ hp]
  have hs : frame (bank φ w dim i [] [] a extra) ∘ (ports ∘ Port.indices) =
      IndexRegisters.bank (BurstRAM.wordBits dim) (word i) [] := by
    funext k
    exact installStacks_at hports ..
  rw [hs, IndexRegisters.select_count]
  apply Finset.sum_congr rfl
  intro j _
  apply congrArg (cont fuel)
  apply installStacks_frame hp
  · intro k
    exact installStacks_at hports ..
  · intro k hk
    by_cases h : ∃ t, ports t = k
    · obtain ⟨t, rfl⟩ := h
      rw [installStacks_at hports, installStacks_at hports]
      cases t with
      | indices x => exact (hk x rfl).elim
      | arithmetic | width | aux => rfl
    · rw [installStacks_outside _ _ (not_exists.mp h), installStacks_outside _ _ (not_exists.mp h)]

include hports in
theorem multiply_framed (he : 0 < e) (hw : Word.workingWidth p ≤ w)
    (i j : Fin dim.val) (a m : K) : ∃ time ≤ MultiplyCall.callCap e w,
    (MultiplyCall.machine.onPorts (ports ∘ Port.arithmetic)).Runs time
      (frame (bank φ w dim i (word j) (bits φ w m) a extra))
      (frame (bank φ w dim i (word j) [] (a*m) extra)) := by
  have hp := hports.comp (fun _ _ h ↦ Port.arithmetic.inj h)
  obtain ⟨time, htime, h⟩ := MultiplyCall.machine_runs he hw c (scalarEncoding φ m) (scalarEncoding φ a)
  rw [mul_scalarEncoding φ, mul_comm m a] at h
  refine ⟨time, htime, MultiplyCall.machine.runs_onPorts_framed (ports := ports ∘ Port.arithmetic) hp h
    (fun _ ↦ installStacks_at hports ..) (fun _ ↦ installStacks_at hports ..) ?_⟩
  intro k hk
  by_cases h : ∃ t, ports t = k
  · obtain ⟨t, rfl⟩ := h
    rw [installStacks_at hports, installStacks_at hports]
    cases t with
    | arithmetic x => exact (hk x rfl).elim
    | indices | width | aux => rfl
  · rw [installStacks_outside _ _ (not_exists.mp h), installStacks_outside _ _ (not_exists.mp h)]

include hports in
theorem commit_framed (i j : Fin dim.val) (a : K) :
    (IndexRegisters.commit.onPorts (ports ∘ Port.indices)).Runs (5*v+3)
      (frame (bank φ w dim i (word j) [] a extra)) (frame (bank φ w dim j [] [] a extra)) := by
  have h := IndexRegisters.commit_runs (BurstRAM.wordBits dim) (word i) (word j)
  simp only [BurstRAM.length_wordBits] at h
  rw [show v+4*v+3 = 5*v+3 by omega] at h
  apply IndexRegisters.commit.runs_onPorts_framed (ports := ports ∘ Port.indices)
    (hports.comp (fun _ _ h ↦ Port.indices.inj h)) h (fun _ ↦ installStacks_at hports ..)
    (fun _ ↦ installStacks_at hports ..)
  intro k hk
  by_cases h : ∃ t, ports t = k
  · obtain ⟨t, rfl⟩ := h
    rw [installStacks_at hports, installStacks_at hports]
    cases t with
    | indices x => exact (hk x rfl).elim
    | arithmetic | width | aux => rfl
  · rw [installStacks_outside _ _ (not_exists.mp h), installStacks_outside _ _ (not_exists.mp h)]

/-- Per-step bound, with the advised coordinate query as its only
singly-exponential operation. This bound does not involve the exponent width. -/
def ticks (v e w queryTicks : ℕ) := (10*v+5) + queryTicks + MultiplyCall.callCap e w + (5*v+3)

include hports in
/-- Each distinct next ordinal is presented to the scalar query exactly once.
The branch leaves the product of the chosen entry and the previous accumulator
in the canonical representation, with a bounded index-dependent delay. -/
theorem callback_count (he : 0 < e) (hw : Word.workingWidth p ≤ w) (read : FiniteRoutine Q)
    (matrix : Matrix (Fin dim.val) (Fin dim.val) K) (i : Fin dim.val) (a : K)
    (queryTicks : ℕ) (query : ∀ j : Fin dim.val, ∃ d ≤ queryTicks, read.Runs d
      (frame (bank φ w dim i (word j) [] a extra))
      (frame (bank φ w dim i (word j) (bits φ w (matrix i j)) a extra)))
    (fuel : ℕ) (hfuel : ticks v e w queryTicks ≤ fuel) :
    ∃ delay : Fin dim.val → ℕ, (∀ j, delay j ≤ ticks v e w queryTicks) ∧
      ∀ cont, (callback ports read).body.count cont fuel (frame (bank φ w dim i [] [] a extra)) =
        ∑ j, cont (fuel-delay j) (frame (bank φ w dim j [] [] (a*matrix i j) extra)) := by
  choose q hq qr using query
  choose m hm mr using fun j ↦ multiply_framed φ ports hports ambient extra dim he hw i j a (matrix i j)
  let delay (j : Fin dim.val) := (10*v+5) + q j + m j + (5*v+3)
  have hdelay (j : Fin dim.val) : delay j ≤ ticks v e w queryTicks := by
    dsimp [delay, ticks]
    have := hq j
    have := hm j
    omega
  refine ⟨delay, hdelay, fun cont ↦ ?_⟩
  have enough : 10*v+5 ≤ fuel := by unfold ticks at hfuel; omega
  rw [show fuel = fuel - (10*v+5) + (10*v+5) by omega, callback]
  simp only [FiniteRoutine.followedBy, FiniteRoutine.ofRoutine, Routine.count_followedBy]
  rw [select_framed φ ports hports ambient extra dim]
  apply Finset.sum_congr rfl
  intro j _
  have hd := (hdelay j).trans hfuel
  dsimp only [delay] at hd ⊢
  have h₁ := (qr j).count_eq ((MultiplyCall.machine.onPorts (ports ∘ Port.arithmetic)).body.count
    ((IndexRegisters.commit.onPorts (ports ∘ Port.indices)).body.count cont)) (fuel-(10*v+5)-q j)
  rw [Nat.sub_add_cancel (by omega)] at h₁
  have h₂ := (mr j).count_eq ((IndexRegisters.commit.onPorts (ports ∘ Port.indices)).body.count cont)
    (fuel-(10*v+5)-q j-m j)
  rw [Nat.sub_add_cancel (by omega)] at h₂
  have h₃ := (commit_framed (w := w) φ ports hports ambient extra dim i j (a*matrix i j)).count_eq cont
    (fuel-(10*v+5)-q j-m j-(5*v+3))
  rw [Nat.sub_add_cancel (by omega)] at h₃
  simp only [Nat.sub_sub] at h₁ h₂ h₃
  rw [Nat.sub_add_cancel enough]
  exact (h₁.trans h₂).trans h₃

end Evaluator.WeightedStep

end VPVNP
end Computability
end OAI
