import OAI.ThreeFlat.RAM.DeterministicBlock
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic

namespace OAI
/-! # Dense lists of selected vertices in original site order -/

namespace ThreeFlat.RAM.TickSlotLookup

open Computability.VPVNP.BurstRAM PrivateRAM Fin.CommRing

variable {w : ℕ}

/-- The scheduler stores two adjacent physical identifiers for each vertex. -/
abbrev Owner (w : ℕ) := ℕ → Word w × Word w

def matchesOwner (own : Owner w) (g s : Word w) (v : ℕ) : Bool := decide (own v = (g,s))

def put (m : Memory w) (a v : ℕ) : Memory w := fun j => if j=a then (v : Word w) else m j

def store (m : Memory w) (a : ℕ) : List ℕ → Memory w
  | [] => m
  | v::vs => store (put m a v) (a+1) vs

theorem store_outside (m : Memory w) (a j : ℕ) (vs : List ℕ) (h : j < a ∨ a+vs.length ≤ j) :
    store m a vs j = m j := by
  induction vs generalizing m a with
  | nil => rfl
  | cons v vs ih =>
    simp only [List.length_cons] at h
    change store (put m a v) (a+1) vs j = _
    rw [ih _ _ (by omega),put,ite_eq_right (by omega)]

theorem store_get (m : Memory w) (a : ℕ) (vs : List ℕ) (i : ℕ) (hi : i < vs.length) :
    store m a vs (a+i) = (vs[i] : Word w) := by
  induction vs generalizing m a i with
  | nil => simp at hi
  | cons v vs ih =>
    cases i with
    | zero =>
      change store (put m a v) (a+1) vs (a+0) = (v : Word w)
      rw [store_outside _ _ _ _ (Or.inl (by omega))]
      simp [put]
    | succ i =>
      have hi' : i < vs.length := by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using hi
      change store (put m a v) (a+1) vs (a+(i+1)) = (vs[i] : Word w)
      rw [show a+(i+1) = (a+1)+i by omega]
      exact ih _ _ _ (by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using hi)

theorem nodup_indices (own : Owner w) (g s : Word w) (n : ℕ) :
    ((List.range n).filter (matchesOwner own g s)).Nodup := (List.nodup_range).filter _

end ThreeFlat.RAM.TickSlotLookup

end OAI
