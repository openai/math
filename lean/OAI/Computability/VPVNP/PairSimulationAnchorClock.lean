import OAI.Computability.VPVNP.PairSimulationAnchorDecode

/-!
# Exact native clock of a successful anchor scan

The descending loop visits each validated selector once. For each copy
the cost includes its preparation, padded field read, lookup and store.
The terminating cursor comparison takes one more instruction.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.AnchorDecode.Program

open BurstRAM BurstRAM.PrivateRAM PrimedCounter.GuessWord PrimedInputRAM MotifEntry
open scoped Fin.CommRing
open private iteration step_at from OAI.Computability.VPVNP.PairSimulationAnchorDecode

variable {X : Type*} {w p r k b payload u : ℕ} (P : Program X p r k)

/-- Exact cost of a single successful copy, including its ordinal store. -/
def visitTicks (code : X ↪ Word b) (x : X) :=
  5 + ((6 * b + 1) + MapLookup.selectorTicks code (code x) P.xs)

/-- All copy clocks and the final empty-loop guard. -/
def successTicks (code : X ↪ Word b) (θ : Fin u → X) :=
  (∑ i, P.visitTicks code (θ i)) + 1

theorem successTicks_le (code : X ↪ Word b) (θ : Fin u → X) :
    P.successTicks code θ ≤ P.visitCap b * u + 1 := by
  unfold successTicks
  apply Nat.add_le_add_right
  calc
    ∑ i, P.visitTicks code (θ i) ≤ ∑ _ : Fin u, P.visitCap b := by
      apply Finset.sum_le_sum
      intro i _
      have bound := MapLookup.selectorTicks_le code (code (θ i)) P.xs
      unfold visitTicks visitCap
      omega
    _ = _ := by simp [Nat.mul_comm]

variable {P} {M : Machine w p r k}

private theorem partial_success (link : P.Linked M) (fits : b ≤ w) (code : X ↪ Word b)
    (hk : ∀ x, M.publicData (P.key x) = MapLookup.widen fits (code x))
    (bits : Fin (payload + u * b) → Bool) (base dest n : ℕ) (hn : n ≤ u)
    (c : Config w p r) (ready : P.Ready bits base dest n c)
    (hi : base + (payload + u * b) < 2 ^ w) (hd : dest + u < 2 ^ w)
    (sep : base + (payload + u * b) ≤ dest ∨ dest + u ≤ base)
    (θ : Fin u → X) (valid : ∀ i, decode P.xs code (readTag bits i) = some (θ i)) :
    ∃ d, Prefix M c (List.replicate (P.successTicks code (θ ∘ Fin.castLE hn)) .tick) d ∧
      P.Frame dest n c d ∧ d.pc = P.done ∧
      ∀ i : Fin u, i.val < n →
        d.privateMem ((dest + i.val : ℕ) : Word w) = M.publicData (P.name (θ i)) := by
  induction n generalizing c with
  | zero =>
    let d := {c with pc := P.done}
    have eq : c.reg (P.reg 6) = c.reg (P.reg 7) := ready.output.trans ready.stop.symm
    have step : M.program.step c = .localStep d := by
      rw [step_at link 0 ready.pc]
      simp [instruction, Instr.run, eq, d]
    have time : P.successTicks code (θ ∘ Fin.castLE hn) = 1 := by simp [successTicks]
    rw [time]
    exact ⟨d, .tick step (.nil _), ⟨fun _ _ _ _ _ _ ↦ rfl, fun _ _ ↦ rfl, rfl⟩,
      rfl, fun i h ↦ (Nat.not_lt_zero i.val h).elim⟩
  | succ n ih =>
    let i : Fin u := ⟨n,hn⟩
    obtain ⟨t, mid, _, pre, frame, result⟩ :=
      iteration link fits code hk bits base dest i c ready hi hd sep
    rcases result with ⟨invalid,_⟩ | ⟨x,ok,next,value,clock⟩
    · simp [valid] at invalid
    have xeq : x = θ i := Option.some.inj (ok.symm.trans (valid i))
    subst x
    have tag : code (θ i) = readTag bits i := by simpa using List.find?_some (valid i)
    have tick : t = P.visitTicks code (θ i) := by rw [clock, ← tag]; rfl
    obtain ⟨d, tail, frame', done, stored⟩ := ih (by omega) mid next
    have clockStep : P.successTicks code (θ ∘ Fin.castLE hn) =
        t + P.successTicks code (θ ∘ Fin.castLE (show n ≤ u by omega)) := by
      unfold successTicks
      rw [Fin.sum_univ_castSucc, tick]
      change (∑ j : Fin n, P.visitTicks code (θ ⟨j.val, _⟩)) + P.visitTicks code (θ i) + 1 =
        P.visitTicks code (θ i) + ((∑ j : Fin n, P.visitTicks code (θ ⟨j.val, _⟩)) + 1)
      omega
    rw [clockStep,List.replicate_add]
    refine ⟨d, pre.append tail, ?_, done, ?_⟩
    · refine ⟨fun a h₀ h₁ h₂ h₅ h₆ ↦ (frame'.regs a h₀ h₁ h₂ h₅ h₆).trans
          (frame.regs a h₀ h₁ h₂ h₅ h₆), ?_, frame'.persistent.trans frame.persistent⟩
      intro a ha
      exact (frame'.memory a (by omega)).trans
        (frame.memory a (by change a.val < dest + n ∨ dest + n + 1 ≤ a.val; omega))
    · intro j hj
      by_cases eq : j = i
      · subst j
        refine (frame'.memory _ (Or.inr ?_)).trans value
        change dest + n ≤ (dest + n) % (2 ^ w)
        rw [Nat.mod_eq_of_lt (by omega)]
      · have : j.val ≠ n := fun h ↦ eq (Fin.ext h)
        exact stored j (by omega)

/-- Successful anchor decoding takes the same computed number of ticks
for every compatible entry configuration. It returns all validated
selector ordinals at their designated private addresses. -/
theorem native_success (link : P.Linked M) (fits : b ≤ w) (code : X ↪ Word b)
    (hk : ∀ x, M.publicData (P.key x) = MapLookup.widen fits (code x))
    (bits : Fin (payload + u * b) → Bool) (base dest : ℕ)
    (c : Config w p r) (ready : P.Ready bits base dest u c)
    (hi : base + (payload + u * b) < 2 ^ w) (hd : dest + u < 2 ^ w)
    (sep : base + (payload + u * b) ≤ dest ∨ dest + u ≤ base)
    (θ : Fin u → X) (ok : selectors? P.xs code (readTag bits) = some θ) :
    ∃ d, Prefix M c (List.replicate (P.successTicks code θ) .tick) d ∧
      P.Frame dest u c d ∧ d.pc = P.done ∧
      ∀ i : Fin u, d.privateMem ((dest + i.val : ℕ) : Word w) = M.publicData (P.name (θ i)) := by
  have valid (i : Fin u) : decode P.xs code (readTag bits i) = some (θ i) := by
    simp only [selectors?, Vector.getElem_ofFn] at ok
    split at ok
    · cases ok
      exact (Option.some_get _).symm
    · cases ok
  obtain ⟨d, run, frame, pc, val⟩ :=
    partial_success link fits code hk bits base dest u le_rfl c ready hi hd sep θ valid
  exact ⟨d, run, frame, pc, fun i ↦ val i i.isLt⟩

end PairSimulation.AnchorDecode.Program

end VPVNP
end Computability
end OAI
