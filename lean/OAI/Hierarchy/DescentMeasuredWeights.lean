import OAI.Hierarchy.DescentMixingIntegerWeights
import OAI.Hierarchy.DescentWeightColumnRAM
import Mathlib.Algebra.BigOperators.Fin

namespace OAI
/-! # Sparse native measurement rows of the actual coupled estimator -/
namespace Hierarchy.DescentMeasuredWeights
open DescentGL DescentIntegerScale DescentWeightColumnRAM
open scoped Classical BigOperators
noncomputable section
variable {A C : Type} [Fintype A] [Fintype C] {k : ℕ}

abbrev Item (levels : A→ℕ) (C : Type) := (Σa,Fin (levels a))⊕C

def level (levels : A→ℕ) (j : (a:A)→Fin (levels a)→ℕ) (cj : C→ℕ) : Item levels C→ℕ :=
  Sum.elim (fun u=>j u.1 u.2) cj

def gain (levels : A→ℕ) (f B K : ℕ) : Item levels C→ℕ :=
  Sum.elim (fun u=>2^f*B*(4*2^((u.2.val+7)/8))) (fun _=>2^f*B*K^2)

def load (levels : A→ℕ) (x : A→Bits k→ℕ) (y : C→Bits k→ℕ) : Item levels C→Bits k→ℕ :=
  Sum.elim (fun u=>x u.1) y

theorem size (levels : A→ℕ) : Fintype.card (Item levels C)=(∑a,levels a)+Fintype.card C := by
  simp [Item,Fintype.card_sigma]

/-- Native dense addresses visit only the present levels and actual
contacts. A site can use its previously installed rank for its row order. -/
def address {H : ℕ} (rank : A ≃ Fin H) (levels : A→ℕ) (contact : C ≃ Fin (Fintype.card C)) :
    Item levels C ≃ Fin ((∑i:Fin H,levels (rank.symm i))+Fintype.card C) :=
  let site : (Σa,Fin (levels a)) ≃ (Σi:Fin H,Fin (levels (rank.symm i))) :=
    (Equiv.sigmaCongrLeft' rank)
  (site.trans finSigmaFinEquiv).sumCongr contact |>.trans finSumFinEquiv

/-- After decoding a row ordinal, the polynomial weight printed by the
word-RAM is exactly the integer work estimator, including its normalization. -/
theorem money_eq {N : ℕ} (levels : A→ℕ) (ord : Fin N ≃ Item levels C)
    (j : (a:A)→Fin (levels a)→ℕ) (cj : C→ℕ) (x : A→Bits k→ℕ) (y : C→Bits k→ℕ)
    (f B K : ℕ) (l : Fin (k+1)) (d : Bits k) :
    money l.val (level levels j cj ∘ord) (gain levels f B K ∘ord)
      (fun i=>natCorrelation (load levels x y (ord i))) d=
      mixingWeightNumerator levels j cj x y f B K l d := by
  let v (s : Item levels C) :=
    if level levels j cj s=l.val then gain levels f B K s*natCorrelation (load levels x y s) d else 0
  change (∑i:Fin N,v (ord i))=_
  rw [ord.sum_comp,Fintype.sum_sum_type,Fintype.sum_sigma]
  simp only [mixingWeightNumerator,Nat.mul_add,Finset.mul_sum]
  apply congrArg₂ (·+·)
  · apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro s _
    by_cases h : j a s=l.val <;> simp [v,level,gain,load,h,eq_comm,Nat.mul_assoc]
  · apply Finset.sum_congr rfl
    intro c _
    by_cases h : cj c=l.val <;> simp [v,level,gain,load,h,eq_comm,Nat.mul_assoc]

theorem normalized {N : ℕ} (levels : A→ℕ) (ord : Fin N ≃ Item levels C)
    (j : (a:A)→Fin (levels a)→ℕ) (hj : ∀ a s,j a s≤k)
    (cj : C→ℕ) (hcj : ∀c,cj c≤k) (x : A→Bits k→ℕ) (y : C→Bits k→ℕ)
    (f B K : ℕ) (l : Fin (k+1)) (d : Nonzero k) :
    (money l.val (level levels j cj ∘ord) (gain levels f B K ∘ord)
      (fun i=>natCorrelation (load levels x y (ord i))) d.val:ℝ) / ((2^f*B:ℕ):ℝ)^2=
    DescentBaseVariance.mixingCollisionWeights levels j hj cj hcj
      (fun a i=>(x a i:ℝ)/((2^f*B:ℕ):ℝ)) (fun c i=>(y c i:ℝ)/((2^f*B:ℕ):ℝ)) f B K l d := by
  rw [money_eq]
  exact (mixingCollisionWeights_eq_integer levels j hj cj hcj x y f B K l d).symm

end
end Hierarchy.DescentMeasuredWeights

end OAI
