import OAI.Hierarchy.DescentPackedWalshCanonical

namespace OAI
/-! # The real all-site integer sums fit in one central estimator word -/
namespace Hierarchy.DescentPackedWalsh
open DescentSIMDLookup DescentGL DescentIntegerScale DescentMeasuredWeights DescentWeightColumnRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {A C : Type} [Fintype A] [Fintype C] {u l N b g : ℕ}
local notation "k" => u+l

theorem padded_measure {I α : Type} (loc : I↪Fin N) (v : I→α) (blank : α)
    (good : α→Prop) (input : ∀i,good (v i)) (empty : good blank) (i : Fin N) :
    good (padded loc v blank i) := by
  by_cases active : ∃a,loc a=i
  · obtain ⟨a,rfl⟩:=active
    simpa only [padded_at] using input a
  · rw [padded_else loc v blank i active]
    exact empty

theorem padded_bill (levels : A→ℕ) (loc : Item levels C↪Fin N)
    (j : (a:A)→Fin (levels a)→ℕ) (cj : C→ℕ) (x : A→Bits k→ℕ) (y : C→Bits k→ℕ)
    (f full K : ℕ) (gainBits : ∀i,padded loc (gain levels f full K) 0 i<2^g)
    (measured : ∀t d,gain levels f full K t*natCorrelation (load levels x y t) d<2^b) :
    ∀s (v : Fin N) d,bill s (padded loc (level levels j cj) 0)
      (fun z=>(⟨_,gainBits z⟩:Cell g)) (padded loc (load levels x y) (fun _=>0)) v d<2^b := by
  intro s v d
  by_cases active : ∃t,loc t=v
  · obtain ⟨t,rfl⟩:=active
    simp only [bill,padded_at]
    split <;> first | exact measured t _ | exact Nat.two_pow_pos _
  · simp only [bill,padded_else loc (gain levels f full K) 0 v active,zero_mul,ite_self,Nat.two_pow_pos]

theorem global_precision (levels : A→ℕ) (loc : Item levels C↪Fin N)
    (j : (a:A)→Fin (levels a)→ℕ) (cj : C→ℕ) (x : A→Bits k→ℕ) (y : C→Bits k→ℕ)
    (f full K : ℕ) (gainBits : ∀i,padded loc (gain levels f full K) 0 i<2^g)
    (measured : ∀t d,gain levels f full K t*natCorrelation (load levels x y t) d<2^b) :
    ∀v d,mixingWeightNumerator levels j cj x y f full K v d≤2^(b+Nat.clog 2 N) := by
  intro v d
  let i : Fin (2^k):=finFunctionFinEquiv d
  have hd : DescentGLScoreRAM.vec i=d:=finFunctionFinEquiv.symm_apply_apply d
  rw [←hd]
  rw [←original_weights levels loc j cj x y f full K gainBits v i]
  calc
    _ ≤ ∑_ : Fin N,2^b := Finset.sum_le_sum (fun i _=> (padded_bill levels loc j cj x y f full K gainBits measured _ i _).le)
    _ = N*2^b := by simp
    _ ≤ 2^(Nat.clog 2 N)*2^b := Nat.mul_le_mul_right (2^b) (Nat.le_pow_clog (by decide : 1 < 2) N)
    _ = 2^(b+Nat.clog 2 N) := by rw [pow_add, Nat.mul_comm]

end
end Hierarchy.DescentPackedWalsh

end OAI
