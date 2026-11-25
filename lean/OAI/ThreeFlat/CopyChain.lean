import OAI.ThreeFlat.BitNetwork
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

namespace OAI
/-! # Contraction of chains of trivalent copy tensors

Each source has one more trunk edge than spokes. Its unary boundary coefficient
pins the first trunk edge or leaves it free. The final trunk edge is summed.
The remaining network may depend jointly on every assigned edge.
-/

namespace ThreeFlat.CopyChain

open scoped BigOperators

variable {S F : Type*}

/-- Chain propagators and boundary values as scalar indicators. -/
noncomputable def ind (F : Type*) [Zero F] [One F] (P : Prop) : F := by
  classical exact if P then 1 else 0

private theorem prod_ind [Fintype S] [CommSemiring F] (p : S → Prop) :
    (∏ s, ind F (p s)) = ind F (∀ s, p s) := by
  classical
  by_cases h : ∀ s, p s <;> simp [ind, Fintype.prod_boole, h]

private theorem ind_mul [CommSemiring F] (p q : Prop) : ind F p * ind F q = ind F (p ∧ q) := by
  classical
  by_cases h : p <;> by_cases k : q <;> simp [ind, h, k]

/-- The ternary cell at a spoke of the chain. -/
noncomputable def copy (F : Type*) [Zero F] [One F] (x y z : Bool) : F :=
  ind F (x = y ∧ y = z)

abbrev Trunks (m : S → ℕ) := ∀ s, Fin (m s + 1) → Bool
abbrev Spokes (m : S → ℕ) := ∀ s, Fin (m s) → Bool

def trunks (m : S → ℕ) (b : S → Bool) : Trunks m := fun s _ => b s
def spokes (m : S → ℕ) (b : S → Bool) : Spokes m := fun s _ => b s

noncomputable def links [CommSemiring F] {m : ℕ} (y : Fin (m+1) → Bool) (z : Fin m → Bool) : F :=
  ∏ i, copy F (y i.castSucc) (y i.succ) (z i)

/-- A prescribed root and trivalent equality cells in one chain. -/
noncomputable def chain [CommSemiring F] {m : ℕ} (b : Bool)
    (y : Fin (m+1) → Bool) (z : Fin m → Bool) : F :=
  ind F (y 0 = b) * links y z

theorem chain_eq [CommSemiring F] {m : ℕ} (b : Bool) (y : Fin (m+1) → Bool) (z : Fin m → Bool) :
    chain (F := F) b y z = ind F (y = (fun _ => b) ∧ z = (fun _ => b)) := by
  unfold chain links copy
  rw [prod_ind, ind_mul]
  congr 1
  apply propext
  constructor
  · rintro ⟨hy, h⟩
    have hall (i : Fin (m+1)) : y i = b :=
      Fin.induction hy (fun j hj => (h j).1.symm.trans hj) i
    exact ⟨funext hall, funext fun j => (h j).2.symm.trans (hall j.succ)⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩

theorem sum_one [CommSemiring F] {m : ℕ} (b : Bool)
    (T : (Fin (m+1) → Bool) → (Fin m → Bool) → F) :
    (∑ y, ∑ z, chain b y z * T y z) = T (fun _ => b) (fun _ => b) := by
  classical
  rw [Finset.sum_eq_single (fun _ => b)]
  · rw [Finset.sum_eq_single (fun _ => b)]
    · simp [chain_eq, ind]
    · intro z _ hz
      simp [chain_eq, ind, hz]
    · simp
  · intro y _ hy
    simp [chain_eq, ind, hy]
  · simp

theorem family_eq [Fintype S] [CommSemiring F] (m : S → ℕ) (b : S → Bool) (y : Trunks m)
    (z : Spokes m) : (∏ s, chain (F := F) (b s) (y s) (z s)) =
      ind F (y = trunks m b ∧ z = spokes m b) := by
  simp_rw [chain_eq]
  rw [prod_ind]
  congr 1
  apply propext
  constructor
  · intro h
    exact ⟨funext fun s => (h s).1, funext fun s => (h s).2⟩
  · rintro ⟨rfl, rfl⟩
    exact fun _ => ⟨rfl, rfl⟩

/-- Contracting simultaneously in a coupled table substitutes every source bit at all its uses. -/
theorem sum_family [Fintype S] [DecidableEq S] [CommSemiring F] (m : S → ℕ) (b : S → Bool)
    (T : Trunks m → Spokes m → F) :
    (∑ y, ∑ z, (∏ s, chain (b s) (y s) (z s)) * T y z) = T (trunks m b) (spokes m b) := by
  classical
  rw [Finset.sum_eq_single (trunks m b)]
  · rw [Finset.sum_eq_single (spokes m b)]
    · simp [family_eq, ind]
    · intro z _ hz
      simp [family_eq, ind, hz]
    · simp
  · intro y _ hy
    simp [family_eq, ind, hy]
  · simp

/-- A hidden source is free, a pin reads its prescribed bit, and a constant reads its literal. -/
def Boundary {n p : ℕ} (pins : Fin p → Bool) : BitSource n p → Bool → Prop
  | .hidden _, _ => True
  | .pin i, x => x = pins i
  | .constant b, x => x = b

private theorem valid_iff {n p : ℕ} (pins : Fin p → Bool) (v : BitSource n p → Bool) :
    (∀ s, Boundary pins s (v s)) ↔ v = BitSource.read (fun i => v (.hidden i)) pins := by
  constructor
  · intro h
    funext s
    cases s with
    | hidden i => rfl
    | pin i => exact h (.pin i)
    | constant b => exact h (.constant b)
  · intro h s
    rw [congrFun h s]
    cases s <;> simp [Boundary, BitSource.read]

/-- Summing a single binary assignment per hidden address removes precisely those boundary pins. -/
theorem hidden_roots {n p : ℕ} [CommSemiring F] (pins : Fin p → Bool) (v : BitSource n p → Bool) :
    (∏ s, ind F (Boundary pins s (v s))) =
      ∑ h : Fin n → Bool, ∏ s, ind F (v s = (BitSource.read h pins) s) := by
  classical
  let h0 := fun i : Fin n => v (.hidden i)
  rw [Finset.sum_eq_single h0]
  · rw [prod_ind, prod_ind]
    congr 1
    apply propext
    exact (valid_iff pins v).trans ⟨fun e s => congrFun e s, fun h => funext h⟩
  · intro h _ hh
    rw [prod_ind]
    have hbad : ¬ ∀ s, v s = (BitSource.read h pins) s := by
      intro hs
      exact hh (funext fun i => (hs (.hidden i)).symm)
    simp [ind, hbad]
  · simp

/-- The contraction of all source chains, with the network's physical unary boundary tensors. -/
theorem sum_network {n p : ℕ} [CommSemiring F] (m : BitSource n p → ℕ)
    (pins : Fin p → Bool) (T : Trunks m → Spokes m → F) :
    (∑ y : Trunks m, ∑ z : Spokes m,
      (∏ s, ind F (Boundary pins s (y s 0)) * links (y s) (z s)) * T y z) =
    ∑ h : Fin n → Bool, T (trunks m (BitSource.read h pins)) (spokes m (BitSource.read h pins)) := by
  classical
  calc
    _ = ∑ y : Trunks m, ∑ z : Spokes m, ∑ h : Fin n → Bool,
        (∏ s, chain (BitSource.read h pins s) (y s) (z s)) * T y z := by
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro z _
      simp_rw [chain, Finset.prod_mul_distrib]
      rw [hidden_roots pins (fun s => y s 0), Finset.sum_mul, Finset.sum_mul]
    _ = ∑ h : Fin n → Bool, ∑ y : Trunks m, ∑ z : Spokes m,
        (∏ s, chain (BitSource.read h pins s) (y s) (z s)) * T y z := by
      exact Eq.trans (Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)) Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun h _ => sum_family m (BitSource.read h pins) T

end ThreeFlat.CopyChain

end OAI
