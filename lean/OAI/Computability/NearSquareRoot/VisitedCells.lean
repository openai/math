import OAI.Computability.NearSquareRoot.Specification
import Mathlib.Data.Set.Card
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Distinct physical cells visited by a deterministic multitape execution -/

namespace OAI
namespace Computability
namespace NearSquareRoot

open IntegerMultiplication

/-- A partial deterministic transition has a unique state after any specified number of steps. -/
theorem trace_endpoint_unique {X : Type*} {step : X → Option X}
    {x y z : X} {n : ℕ} (hy : Trace step x n y) (hz : Trace step x n z) : y = z := by
  suffices h : ∀ m w, Trace step x m w → n = m → y = w from h n z hz rfl
  clear hz z
  induction hy with
  | nil x =>
    intro m w hw he
    cases hw with
    | nil => rfl
    | cons => omega
  | @cons x a y n hxa _ ih =>
    intro m w hw he
    cases hw with
    | nil => omega
    | @cons _ b _ k hxb hb =>
      have hab : a = b := Option.some.inj (hxa.symm.trans hxb)
      subst b
      exact ih k w hb (by omega)

/-- Two halting traces from the same start must take the same time and have the same endpoint. -/
theorem halting_trace_unique {X : Type*} {step : X → Option X} {x y z : X}
    {n m : ℕ} (hy : Trace step x n y) (halt_y : step y = none)
    (hz : Trace step x m z) (halt_z : step z = none) : n = m ∧ y = z := by
  induction hy generalizing m z with
  | nil x =>
    cases hz with
    | nil => exact ⟨rfl, rfl⟩
    | cons h _ => rw [halt_y] at h; contradiction
  | @cons x a y n hxa _ ih =>
    cases hz with
    | nil => rw [halt_z] at hxa; contradiction
    | @cons _ b _ k hxb hb =>
      have hab : a = b := Option.some.inj (hxa.symm.trans hxb)
      subst b
      obtain ⟨rfl, rfl⟩ := ih halt_y hb halt_z
      exact ⟨rfl, rfl⟩

variable {A Q I : Type}

/-- The set of physical cells reached by any head in the first `steps` transitions,
including the positions before the first transition and after the last. -/
def visitedCells (m : TM.Rule A Q I) (init : TM.Config A Q I) (steps : ℕ) : Set (I × ℤ) :=
  {p | ∃ u ≤ steps, ∃ c, Trace (TM.advance m) init u c ∧ (c.tape p.1).pos = p.2}

theorem visitedCells_finite [Finite I] (m : TM.Rule A Q I) (init : TM.Config A Q I)
    (steps : ℕ) : (visitedCells m init steps).Finite := by
  classical
  let endpoint (u : Fin (steps + 1)) : TM.Config A Q I :=
    if h : ∃ c, Trace (TM.advance m) init u.val c then h.choose else init
  let position (p : Fin (steps + 1) × I) : I × ℤ := (p.2, ((endpoint p.1).tape p.2).pos)
  apply (Set.finite_range position).subset
  rintro ⟨i, address⟩ ⟨u, hu, c, hc, hp⟩
  let v : Fin (steps + 1) := ⟨u, by omega⟩
  have h : ∃ d, Trace (TM.advance m) init v.val d := ⟨c, hc⟩
  have he : endpoint v = c := by
    dsimp only [endpoint]
    rw [dite_eq_left h]
    exact trace_endpoint_unique h.choose_spec hc
  exact ⟨(v, i), by simpa [position, he] using hp⟩

/-- The finite-cover specification is exactly a bound on the cardinality of the
set of visited tape/address pairs. -/
theorem visitsAtMost_iff_ncard [Finite I] (m : TM.Rule A Q I) (init : TM.Config A Q I)
    (steps cells : ℕ) : VisitsAtMost m init steps cells ↔
      (visitedCells m init steps).ncard ≤ cells := by
  classical
  constructor
  · rintro ⟨cover, hcard, h⟩
    have hsub : visitedCells m init steps ⊆ ↑cover := by
      rintro ⟨i, address⟩ ⟨u, hu, c, hc, hp⟩
      change (c.tape i).pos = address at hp
      subst address
      exact h u hu c hc i
    exact (Set.ncard_le_ncard hsub cover.finite_toSet).trans
      (by simpa only [Set.ncard_coe_finset] using hcard)
  · intro h
    have hf := visitedCells_finite m init steps
    refine ⟨hf.toFinset, ?_, ?_⟩
    · rwa [← Set.ncard_eq_toFinset_card _ hf]
    · intro u hu c hc i
      exact hf.mem_toFinset.mpr ⟨u, hu, c, hc, rfl⟩

variable [Fintype I] {m : TM.Rule A Q I} {init : TM.Config A Q I}
  {steps : ℕ}

/-- A separate interval on each tape suffices. The space charge is the sum of the
interval lengths, including both endpoints, regardless of how often a head moves. -/
theorem visitsAtMost_of_tape_fences (lo hi : I → ℤ)
    (hpos : ∀ u ≤ steps, ∀ c : TM.Config A Q I, Trace (TM.advance m) init u c →
      ∀ i : I, lo i ≤ (c.tape i).pos ∧ (c.tape i).pos ≤ hi i) :
    VisitsAtMost m init steps (∑ i : I, (hi i + 1 - lo i).toNat) := by
  classical
  let cells (i : I) := (Finset.Icc (lo i) (hi i)).map (Function.Embedding.sectR i ℤ)
  refine ⟨Finset.univ.biUnion cells, ?_, ?_⟩
  · simpa [cells, Int.card_Icc] using
      (Finset.card_biUnion_le (s := Finset.univ) (t := cells))
  · intro u hu c hc i
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
      Finset.mem_map.mpr ⟨(c.tape i).pos, Finset.mem_Icc.mpr (hpos u hu c hc i), rfl⟩⟩

/-- Common endmarks give a tape-count times interval-length bound. -/
theorem visitsAtMost_of_common_fence (lo hi : ℤ)
    (hpos : ∀ u ≤ steps, ∀ c : TM.Config A Q I, Trace (TM.advance m) init u c →
      ∀ i : I, lo ≤ (c.tape i).pos ∧ (c.tape i).pos ≤ hi) :
    VisitsAtMost m init steps (Fintype.card I * (hi + 1 - lo).toNat) := by
  simpa using visitsAtMost_of_tape_fences (fun _ => lo) (fun _ => hi) hpos

/-- For positive input length, symmetric fences of radius `R * n` have an absolute
space constant depending only on the fixed tape count and `R`. -/
theorem visitsAtMost_of_linear_fence (R n : ℕ) (hn : 0 < n)
    (hpos : ∀ u ≤ steps, ∀ c : TM.Config A Q I, Trace (TM.advance m) init u c →
      ∀ i : I, -((R * n : ℕ) : ℤ) ≤ (c.tape i).pos ∧ (c.tape i).pos ≤ (R * n : ℕ)) :
    VisitsAtMost m init steps ((Fintype.card I * (2 * R + 1)) * n) := by
  obtain ⟨s, hs, hc⟩ := visitsAtMost_of_common_fence _ _ hpos
  refine ⟨s, hs.trans ?_, hc⟩
  rw [Nat.mul_assoc, Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
  apply Nat.mul_le_mul_left
  omega

end NearSquareRoot
end Computability
end OAI
