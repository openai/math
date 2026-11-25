import OAI.Hierarchy.DescentDatedAddressBook
import Mathlib.Data.Finset.Insert

namespace OAI
/-! # Earlier immutable evidence survives the measured private-counter updates -/
namespace Hierarchy.DescentDatedAddressBook
open Computability.VPVNP.BurstRAM

/-- On a single earlier address, each intervening date can designate its own finite set of
measured counters. The genuine native private control reuses exactly its old fee word. -/
theorem retained_except {w origin start stop addr : ℕ} (span : ℕ→ℕ) (states : ℕ→Memory w)
    (writes : ℕ→Finset ℕ) (earlier : addr<floor origin span start) (dates : start≤stop)
    (saved : ∀t,start≤t→t<stop→addr∉writes t)
    (kept : ∀t,start≤t→t<stop→∀x<floor origin span t,x∉writes t→states (t+1) x=states t x) :
    states stop addr=states start addr := by
  induction stop,dates using Nat.le_induction with
  | base=>rfl
  | succ j hj ih=>
    have prev:=kept j hj (Nat.lt_succ_self _) addr (earlier.trans_le (floor_mono origin span hj))
      (saved j hj (Nat.lt_succ_self _))
    exact prev.trans (ih (fun t ht lt=>saved t ht (lt.trans (Nat.lt_succ_self _)))
      (fun t ht lt=>kept t ht (lt.trans (Nat.lt_succ_self _))))

theorem retained_outside_counter {w origin start stop addr counter : ℕ} (span : ℕ→ℕ) (states : ℕ→Memory w)
    (earlier : addr<floor origin span start) (dates : start≤stop) (different : addr≠counter)
    (kept : ∀t,start≤t→t<stop→∀x<floor origin span t,x≠counter→states (t+1) x=states t x) :
    states stop addr=states start addr := by
  apply retained_except span states (fun _=>{counter}) earlier dates
  · intro j lo hi
    simpa only [Finset.mem_singleton] using different
  · simpa only [Finset.mem_singleton] using kept

end Hierarchy.DescentDatedAddressBook

end OAI
