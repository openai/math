import OAI.Computability.BorderVNP.TeamSiteMeter
import OAI.Computability.BorderVNP.TeamTapeHandoff
import OAI.Computability.BorderVNP.TeamBurstProbeReplay

/-! # Charged local instruction paths before the handoff

A local execution records each fetched action, its complete old-word and choice
payload, and the native sign at its successor. The processor keeps these data
private. Its two countdowns, incoming control, and exact outgoing control are
sufficient to concatenate the executions of successive blocks.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite

open VPVNP RAMTape TeamRAM TeamTapeHandoff

variable {w p r : ℕ}

/-- Each physical instruction reads its guessed old words first, followed by its
own RAM or private choices. -/
def eventBits (e : Event w) : List Bool := TeamBurstProbe.choices e.old ++ e.choices

/-- Complete choice spelling of one local block, with empty deterministic events included. -/
def chunkBits (es : List (Event w)) : List Bool := es.flatMap eventBits

/-- Finite control spelling of each native sign. -/
def signBit : Sign → Option Bool
  | .zero => none
  | .plus => some false
  | .minus => some true

@[simp] theorem signBit_value (s : Sign) : TeamPrivateCall.sign (signBit s) = s := by cases s <;> rfl

/-- Accumulate the local instruction weights in physical finite control. -/
def chunkSign (sg : Option Bool) (es : List (Event w)) : Option Bool :=
  es.foldl (fun s e => Loop.times s (signBit e.sign)) sg

/-- The actual sign accumulator returns the product of all native event weights,
including a private call returning zero. -/
theorem chunkSign_value (sg : Option Bool) (es : List (Event w)) :
    (TeamPrivateCall.sign (chunkSign sg es)).value =
      (TeamPrivateCall.sign sg).value * (es.map (fun e => e.sign.value)).prod := by
  induction es generalizing sg with
  | nil => simp [chunkSign]
  | cons e es ih =>
    change (TeamPrivateCall.sign (chunkSign (Loop.times sg (signBit e.sign)) es)).value = _
    simp [ih, Loop.value_times, mul_assoc]

/-- A finite sequence of locally executed signed instructions inside one guarded
block. The countdown and burst bound are checked on every transition. -/
inductive Chunk (P : TeamOpcode.State w p r → Instr w (TeamOpcode.State w p r)) :
    TeamOpcode.State w p r → Window w → List (Event w) → TeamOpcode.State w p r → Window w → Prop
  | nil (s c) : Chunk P s c [] s c
  | cons {s c e next es last fin} (action : (P s).action = some e.action)
      (advance : (P s).advance e.choices e.old = some (next,e.sign))
      (fits : c.Fits e.action.extra) (cap : e.action.extra ≤ c.cap.val)
      (rest : Chunk P next (c.charge e.action.extra) es last fin) :
      Chunk P s c (e::es) last fin

variable {P : TeamOpcode.State w p r → Instr w (TeamOpcode.State w p r)}
variable {s next last : TeamOpcode.State w p r} {c fin : Window w} {es : List (Event w)}

/-- A guarded segment can be followed by any locally valid accepting continuation. -/
theorem Chunk.append_local (h : Chunk P s c es last fin) {tail : List (Event w)}
    (rest : Local P last tail) : Local P s (es++tail) := by
  induction h with
  | nil => exact rest
  | cons action advance _ _ _ ih => exact ⟨action,_,advance,ih rest⟩

/-- Every processor segment has the same integer clock and countdowns as its summed
native charge. The cap remains the supplied read-only word. -/
theorem Chunk.clock (h : Chunk P s c es last fin) (safe : c.Safe) :
    cost es ≤ c.block.val ∧ cost es ≤ c.global.val ∧ fin.Safe ∧
      fin.block.val = c.block.val-cost es ∧ fin.global.val = c.global.val-cost es ∧
      fin.elapsed.val = c.elapsed.val+cost es ∧ fin.cap = c.cap := by
  induction h with
  | nil => simp [cost, RAMBuckets.cost, safe]
  | @cons s c e next es last fin act go fits cap tail ih =>
    obtain ⟨hb,hg,ht,hs⟩ := c.charged_values e.action.extra safe fits
    obtain ⟨rb,rg,rs,fb,fg,ft,fc⟩ := ih hs
    obtain ⟨lb,lg⟩ := fits
    rw [hb] at rb fb
    rw [hg] at rg fg
    rw [ht] at ft
    rw [show cost (e::es) = 1+e.action.extra+cost es from rfl]
    exact ⟨by omega, by omega, rs, by omega, by omega, by omega, fc⟩

/-- Form the maximal processor prefix of a complete locally valid path. Native
branch identities and all guessed values are preserved through the greedy split. -/
theorem chunk_of_prefix {front tail : List (Event w)}
    (valid : Local P s (front++tail)) (bound : ∀ e ∈ front, e.action.extra ≤ c.cap.val)
    (block : cost front ≤ c.block.val) (global : cost front ≤ c.global.val) (safe : c.Safe) :
    ∃ last fin, Chunk P s c front last fin ∧ Local P last tail := by
  induction front generalizing s c with
  | nil => exact ⟨s,c,.nil ..,valid⟩
  | cons e es ih =>
    obtain ⟨ha, next, hn, rest⟩ := valid
    have hcost : cost (e::es) = 1+e.action.extra+cost es := rfl
    rw [hcost] at block global
    have fits : c.Fits e.action.extra := ⟨by omega,by omega⟩
    obtain ⟨hb,hg,_,hs⟩ := c.charged_values e.action.extra safe fits
    obtain ⟨last, fin, run, rem⟩ := ih (s := next) (c := c.charge e.action.extra) rest
      (fun f hf => bound f (List.mem_cons_of_mem e hf)) (by rw [hb]; omega) (by rw [hg]; omega) hs
    exact ⟨last,fin,.cons ha hn fits (bound e (by simp)) run,rem⟩

end TeamSite

end BorderVNP
end Computability
end OAI
