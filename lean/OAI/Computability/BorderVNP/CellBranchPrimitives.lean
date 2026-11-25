import OAI.Computability.BorderVNP.CellLoopCounter

/-! # Nondestructive empty-stack dispatch for cell fragments

A caller can clear a port or select a returning fragment by testing its
emptiness. On a nonempty port the test restores the popped bit before
the selected fragment starts, preserving all the caller's input words.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellMacro.Generator.Fragment
open VPVNP.RAMTape
open Structured
open private test test_empty test_false test_true from OAI.Computability.BorderVNP.CellStructured

variable {K : Type} [DecidableEq K]

/-- Discard the entire bit word in a caller stack. -/
abbrev clearStack (k : K) : Fragment K := erase k

/-- The checked clearing loop costs at most four instructions per bit and two at termination. -/
theorem clearStack_run (k : K) (s : Stacks K) :
    ∃ t ≤ 4*(s k).length+2, (clearStack k).Runs t s (Function.update s k []) := by
  obtain ⟨t, ht, run⟩ := erase_run k s
  exact ⟨t, by omega, run⟩

/-- Test emptiness of a public stack and enter one of two fragments with disjoint scratch registers. -/
def ifEmpty (k : K) (zero nonzero : Fragment K) : Fragment K where
  Scratch := zero.Scratch ⊕ nonzero.Scratch
  body := test (.inl k) (zero.body.onPorts (Sum.map id Sum.inl))
    (nonzero.body.onPorts (Sum.map id Sum.inr)) (nonzero.body.onPorts (Sum.map id Sum.inr))

/-- The empty branch begins with the original bank, costing only the test instruction. -/
theorem ifEmpty_empty {k : K} {zero nonzero : Fragment K} {s u : Stacks K} {t : ℕ}
    (hs : s k = []) (h : zero.Runs t s u) : (ifEmpty k zero nonzero).Runs (t+1) s u := by
  apply test_empty (s := (ifEmpty k zero nonzero).bank s) (v := (ifEmpty k zero nonzero).bank u)
    (k := Sum.inl k) (show (ifEmpty k zero nonzero).bank s (.inl k) = [] from hs)
  apply zero.body.runs_onPorts_framed (Sum.map_injective.mpr ⟨Function.injective_id, Sum.inl_injective⟩) h
  · intro i; cases i <;> rfl
  · intro i; cases i <;> rfl
  · intro i hn; cases i with | inl j => exact (hn (.inl j) rfl).elim | inr _ => rfl

/-- Testing a nonempty stack costs the pop and its restoring push; the called
fragment sees exactly the original state regardless of the leading bit. -/
theorem ifEmpty_nonempty {k : K} {zero nonzero : Fragment K} {s u : Stacks K} {t : ℕ}
    (hs : s k ≠ []) (h : nonzero.Runs t s u) : (ifEmpty k zero nonzero).Runs (t+2) s u := by
  obtain ⟨bit, rest, hb⟩ := List.exists_cons_of_ne_nil hs
  have branch : (nonzero.body.onPorts (Sum.map id Sum.inr)).Runs t
      ((ifEmpty k zero nonzero).bank s) ((ifEmpty k zero nonzero).bank u) := by
    apply nonzero.body.runs_onPorts_framed (Sum.map_injective.mpr ⟨Function.injective_id, Sum.inr_injective⟩) h
    · intro i; cases i <;> rfl
    · intro i; cases i <;> rfl
    · intro i hn; cases i with | inl j => exact (hn (.inl j) rfl).elim | inr _ => rfl
  rw [show t+2 = 1+t+1 by omega]
  cases bit with
  | false => exact test_false (k := Sum.inl k) (show (ifEmpty k zero nonzero).bank s (.inl k) = false :: rest from hb) branch
  | true => exact test_true (k := Sum.inl k) (show (ifEmpty k zero nonzero).bank s (.inl k) = true :: rest from hb) branch

end CellMacro.Generator.Fragment

end BorderVNP
end Computability
end OAI
