import OAI.Hierarchy.DescentSeedTrivalentMenu
import OAI.Hierarchy.DescentNetworkStack
import OAI.Hierarchy.ProtocolStackContraction

namespace OAI
/-! # First-stage histogram menus for tensor powers of the actual local tables -/

namespace Hierarchy.DescentInitialHost
open Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
variable {F : Type*} [Field F] {D : ℕ} {P : Type*} [Fintype P] {b : P→ℕ}
variable (N : Network D P b)

abbrev Count (s : ℕ) (v : N.Site) := Pattern N v → Fin (s+1)

def counts {s : ℕ} {v : N.Site} (row : Fin s→Pattern N v) : Count N s v := fun p =>
  ⟨(Finset.univ.filter fun i=>row i=p).card,Nat.lt_succ_of_le ((Finset.card_le_card (Finset.filter_subset ..)).trans (by simp))⟩

def censusWeight (T : N.Tables F) (s : ℕ) (v : N.Site) (h : Count N s v) : F :=
  ∏p,(coeff N T v p)^(h p).val

def censusTable (s : ℕ) (v : N.Site) (h : Count N s v)
    (z : ∀ e : {e // N.src e=v ∨ N.dst e=v},Fin (s*N.width e.1) → Bool)
    (x : ∀ p : {p // N.attach p=v},Fin (s*b p.1) → Bool) : F :=
  if h=counts N (fun i=>⟨fun e=>rowAt (z e) i,fun p=>rowAt (x p) i⟩) then 1 else 0

theorem local_histogram (T : N.Tables F) (s : ℕ) (v : N.Site)
    (z : ∀ e : {e // N.src e=v ∨ N.dst e=v},Fin (s*N.width e.1) → Bool)
    (x : ∀ p : {p // N.attach p=v},Fin (s*b p.1) → Bool) :
    (∑h : Count N s v, censusWeight N T s v h*censusTable N s v h z x) =
      stackTable N T v z x := by
  let row (i : Fin s) : Pattern N v := ⟨fun e=>rowAt (z e) i,fun p=>rowAt (x p) i⟩
  simp only [censusTable,mul_ite,mul_zero,mul_one,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  calc
    _ = ∏ i : Fin s, coeff N T v (row i) := by
      rw [ProtocolStackContraction.table_histogram row (coeff N T v)]
      unfold censusWeight
      apply Finset.prod_congr (by ext p; simp)
      intro p _
      apply congrArg (fun n : ℕ => coeff N T v p ^ n)
      simp only [counts, Fin.val_mk]
      apply congrArg (fun z : Finset (Fin s) => z.card)
      ext i
      simp [row]
    _ = _ := rfl

def seedLocal (s : ℕ) (h : ∀v,Count N s v) : (stacked N s).Tables F :=
  fun v z x => censusTable N s v (h v) z x

/-- All local choices are genuine small count vectors. The old field entries
occur only as one scalar monomial outside the selected Boolean subnetwork. -/
theorem seed_value (T : N.Tables F) (s : ℕ) (x : Ports (fun p=>s*b p)) :
    (∑h : ∀v,Count N s v, (∏v,censusWeight N T s v (h v))*
      (stacked N s).value (seedLocal N s h) x) =
      ∏ i : Fin s,N.value T (fun p=>rowAt (x p) i) := by
  rw [←stack_value N s T x]
  unfold Network.value
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  let factor (v : N.Site) (h : Count N s v) : F :=
    censusWeight N T s v h * censusTable N s v h (fun e => a e.val) (fun p => x p.val)
  calc
    _ = ∑ h : ∀ v, Count N s v, ∏ v, factor v (h v) := by
      apply Finset.sum_congr rfl
      intro h _
      simp only [factor, Finset.prod_mul_distrib, Network.read, seedLocal]
      apply congrArg₂ (· * ·)
      · rfl
      · refine Finset.prod_congr ?_ ?_
        · ext v
          constructor <;> intro _ <;> apply @Finset.mem_univ
        · intro v _
          rfl
    _ = ∏ v, ∑ h, factor v h := (Fintype.prod_sum factor).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro v _
      exact local_histogram N T s v _ _

end
end Hierarchy.DescentInitialHost

end OAI
