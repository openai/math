import OAI.ThreeFlat.Concentrator.Peeling
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Log

namespace OAI
/-! # Halving the set of unassigned requests

The heavy vertices have at least one more remaining request than slots.
The expander mixing bound on their induced edges bounds the requests that
survive one peeling round.
-/

namespace ThreeFlat.Concentrator.ReserveGraph

open Finset

variable {E V : Type*} [DecidableEq E] [DecidableEq V] [Fintype V]
variable (G : ReserveGraph E V)

def heavy (slots : ℕ) (S : Finset E) : Finset V :=
  univ.filter fun v => slots < (G.incident S v).card

def internalEdges (S : Finset E) (H : Finset V) : Finset E :=
  S.filter fun e => G.src e ∈ H ∧ G.dst e ∈ H

omit [DecidableEq E] in
theorem step_eq_internalEdges (slots : ℕ) (S : Finset E) :
    G.step slots S = G.internalEdges S (G.heavy slots S) := by
  ext e
  simp [internalEdges, heavy, step]

theorem heavy_card (slots : ℕ) (S : Finset E) :
    (slots + 1) * (G.heavy slots S).card ≤ 2 * S.card := by
  have total (f : E → V) : ∑ v : V, (S.filter fun e => f e = v).card = S.card :=
    (card_eq_sum_card_fiberwise (t := univ) (fun _ _ => mem_univ _) (f := f) (s := S)).symm
  have hinc (v : V) : (G.incident S v).card ≤ (S.filter fun e => G.src e = v).card +
      (S.filter fun e => G.dst e = v).card := by
    rw [incident, filter_or]
    exact card_union_le _ _
  calc
    (slots + 1) * _ = ∑ _v ∈ G.heavy slots S, (slots + 1) := by simp [Nat.mul_comm]
    _ ≤ ∑ v ∈ G.heavy slots S, (G.incident S v).card := sum_le_sum fun v hv =>
      Nat.succ_le_of_lt (mem_filter.mp hv).2
    _ ≤ ∑ v : V, (G.incident S v).card :=
      sum_le_sum_of_subset (subset_univ _)
    _ ≤ ∑ v : V, ((S.filter fun e => G.src e = v).card +
        (S.filter fun e => G.dst e = v).card) := sum_le_sum fun v _ => hinc v
    _ = _ := by rw [sum_add_distrib, total, total]; omega

/-- Mixing on small vertex sets suffices for logarithmically many rounds.
The four in the induced-edge bound pays both the incidence multiplicity
and the factor-two decrease per round. -/
theorem finished_of_sparse_mixing {all A : Finset E} (hA : A ⊆ all) (slots : ℕ)
    (mix : ∀ H : Finset V, (slots + 1) * H.card ≤ 2 * A.card →
      4 * (G.internalEdges all H).card ≤ (slots + 1) * H.card)
    {cap : ℕ} (hcap : A.card < 2 ^ cap) : G.live slots A cap = ∅ := by
  have decrease (t : ℕ) : 2 * (G.live slots A (t+1)).card ≤ (G.live slots A t).card := by
    let S := G.live slots A t
    have hS : S ⊆ A := (G.live_antitone slots A) (Nat.zero_le t)
    have hH := G.heavy_card slots S
    have hsmall := mix _ (hH.trans (Nat.mul_le_mul_left 2 (card_le_card hS)))
    have hsub := card_le_card (filter_subset_filter
      (fun e => G.src e ∈ G.heavy slots S ∧ G.dst e ∈ G.heavy slots S) (hS.trans hA))
    change 2 * (G.step slots S).card ≤ S.card
    rw [G.step_eq_internalEdges]
    change (G.internalEdges S _).card ≤ (G.internalEdges all _).card at hsub
    omega
  have iter (n : ℕ) : 2 ^ n * (G.live slots A n).card ≤ A.card := by
    induction n with
    | zero => simp [live]
    | succ n hn =>
      rw [pow_succ, Nat.mul_assoc]
      exact (Nat.mul_le_mul_left _ (decrease n)).trans hn
  apply card_eq_zero.mp
  by_contra! hpos
  have hn := (Nat.le_mul_of_pos_right (2 ^ cap) (Nat.pos_of_ne_zero hpos)).trans (iter cap)
  omega

end ThreeFlat.Concentrator.ReserveGraph

end OAI
