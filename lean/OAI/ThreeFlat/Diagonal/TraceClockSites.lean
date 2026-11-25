import OAI.ThreeFlat.Diagonal.TraceAdjacent
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin

namespace OAI
/-! # Regrouping native clock checks into paired physical rows -/

namespace ThreeFlat.Diagonal.TraceRows

open Computability.VPVNP.BurstRAM

variable {F C : Type*} {w f : ℕ}

/-- Read an actual CPU row when in bounds, otherwise the forced trailing pad. -/
def clockAt (x : Fin f → Row w C) (i : ℕ) : Row w C :=
  if h : i < f then x ⟨i,h⟩ else .pad

private theorem clockAt_tail {f : ℕ} (x : Fin (f+1) → Row w C) (i : ℕ) :
    clockAt (fun j : Fin f => x j.succ) i = clockAt x (i+1) := by
  by_cases hi : i < f <;> simp [clockAt, hi]

theorem ofFn_headD (x : Fin f → Row w C) : (List.ofFn x).headD .pad = clockAt x 0 := by
  cases f with
  | zero => simp [clockAt]
  | succ f => simp [List.ofFn_succ, clockAt]

/-- Every register transition, including the final boundary, is a single
comparison of two adjacent physical clock positions. -/
theorem pairs_ofFn_iff (P : Program w C) (x : Fin f → Row w C) :
    pairs P (List.ofFn x) ↔ ∀ i : Fin f, pair P (x i) (clockAt x (i.val+1)) := by
  induction f with
  | zero => simp [pairs]
  | succ f ih =>
    rw [List.ofFn_succ, pairs, ofFn_headD, clockAt_tail, ih]
    constructor
    · rintro ⟨h,ht⟩ i
      refine Fin.cases h (fun j => ?_) i
      exact (clockAt_tail x (j.val+1)) ▸ ht j
    · intro h
      refine ⟨h 0, fun j => ?_⟩
      exact (clockAt_tail x (j.val+1)).symm ▸ h j.succ

/-- The logical index at an in-row position. -/
def slotAddress (d : ℕ) (v : Fin (2^d)) (s : Fin 2) : ℕ := 2*v.val+s.val

/-- Locate a clock term among the two-track header/step/padding slots. -/
def atClock {α : Type*} (default : α) (S : ℕ) (g : Fin f → α) (u : ℕ) : α :=
  if S ≤ u then if h : u-S < f then g ⟨u-S,h⟩ else default else default

private def clockEmbedding (S d f : ℕ) (fit : S+f ≤ 2^(1+d)) : Fin f ↪ Fin (2^d) × Fin 2 where
  toFun i := (⟨(S+i.val)/2,by
    have hi := i.isLt
    rw [Nat.pow_add, Nat.pow_one] at fit
    omega⟩,⟨(S+i.val)%2,Nat.mod_lt _ (by decide)⟩)
  inj' := by
    intro i j he
    have h0 := congrArg (fun p : Fin (2^d) × Fin 2 => p.1.val) he
    have h1 := congrArg (fun p : Fin (2^d) × Fin 2 => p.2.val) he
    apply Fin.ext
    dsimp at h0 h1
    omega

private theorem clockEmbedding_address (S d f : ℕ) (fit : S+f ≤ 2^(1+d)) (i : Fin f) :
    slotAddress d ((clockEmbedding S d f fit i).1) ((clockEmbedding S d f fit i).2) = S+i.val := by
  change 2*((S+i.val)/2)+(S+i.val)%2 = S+i.val
  omega

theorem all_clock_sites (S d : ℕ) (fit : S+f ≤ 2^(1+d)) (p : Fin f → Prop) :
    (∀ v s, atClock True S p (slotAddress d v s)) ↔ ∀ i, p i := by
  constructor
  · intro h i
    have hi := h (clockEmbedding S d f fit i).1 (clockEmbedding S d f fit i).2
    simpa [clockEmbedding_address, atClock, i.isLt] using hi
  · intro h v s
    unfold atClock
    split <;> first | trivial | split <;> first | trivial | exact h _

/-- Multiplying all clock factors in the containing physical array counts
each active time exactly once and all other slots with unit weight. -/
theorem prod_clock_sites [CommMonoid F] (S d : ℕ) (fit : S+f ≤ 2^(1+d)) (g : Fin f → F) :
    (∏ v : Fin (2^d), ∏ s : Fin 2, atClock 1 S g (slotAddress d v s)) = ∏ i, g i := by
  classical
  let emb := clockEmbedding S d f fit
  let term := fun u : Fin (2^d) × Fin 2 => atClock 1 S g (slotAddress d u.1 u.2)
  change (∏ v, ∏ s, term (v,s)) = _
  rw [← Fintype.prod_prod_type (f:=term)]
  have hval (i : Fin f) : term (emb i) = g i := by
    simp [term, emb, clockEmbedding_address, atClock, i.isLt]
  rw [← Finset.prod_subset (s₁ := Finset.univ.map emb) (s₂ := Finset.univ) (f := term)
    (Finset.subset_univ _) ?_, Finset.prod_map]
  · exact Finset.prod_congr rfl (fun i _ => hval i)
  · intro u _ hu
    by_cases ha : S ≤ slotAddress d u.1 u.2
    · by_cases hb : slotAddress d u.1 u.2-S < f
      · exfalso
        let i : Fin f := ⟨slotAddress d u.1 u.2-S,hb⟩
        apply hu
        apply Finset.mem_map.mpr
        refine ⟨i, Finset.mem_univ _, ?_⟩
        apply Prod.ext <;> apply Fin.ext
        · change (S + (slotAddress d u.1 u.2-S)) / 2 = u.1.val
          rw [Nat.add_sub_of_le ha]
          have := u.2.isLt
          unfold slotAddress
          omega
        · change (S + (slotAddress d u.1 u.2-S)) % 2 = u.2.val
          rw [Nat.add_sub_of_le ha]
          have := u.2.isLt
          unfold slotAddress
          omega
      · simp [term, atClock, ha, hb]
    · simp [term, atClock, ha]

end ThreeFlat.Diagonal.TraceRows

end OAI
