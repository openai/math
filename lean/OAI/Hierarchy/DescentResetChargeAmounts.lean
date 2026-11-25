import OAI.Hierarchy.DescentTerminalChartScale
import Mathlib.Data.Fin.VecNotation

namespace OAI
/-! Finite addition of the charged segments of one reset instruction. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentCompiler.TerminalScale Filter
noncomputable section
structure EnteredCharges where
  roots : ℕ
  actor : ℕ
  received : ℕ
  compact : ℕ
  contact : ℕ
  masks : ℕ
  numbered : ℕ
  sheets : ℕ
  funding : ℕ
  venue : ℕ
  mover : ℕ
  classes : ℕ
  birth : ℕ
  metadata : ℕ

def EnteredCharges.total (x : EnteredCharges) :=
  x.roots+x.actor+x.received+x.compact+x.contact+x.masks+x.numbered+x.sheets+
    x.funding+x.venue+x.mover+x.classes+x.birth+x.metadata

namespace EnteredCharges
def amount (x : EnteredCharges) : Fin 14 → ℕ :=
  ![x.roots,x.actor,x.received,x.compact,x.contact,x.masks,x.numbered,
    x.sheets,x.funding,x.venue,x.mover,x.classes,x.birth,x.metadata]

theorem sum_amount (x : EnteredCharges) : (∑j,x.amount j)=x.total := by
  simp [amount,total,Fin.sum_univ_succ,Nat.add_assoc]

/-- Each scalar rate is fixed by its concrete program. They all use the same
old-host and original group rectangle, and share one ambient lookup allowance. -/
theorem finite_paid {n : ℕ} (expense : Fin n → ℕ) (J hosts slots copies saving : ℕ)
    (leads rates shares : Fin n → ℕ)
    (paid : ∀j, expense j ≤ hosts*(leads j*scale J (rates j))+
      slots*(leads j*scale J (rates j))+shares j*(copies/(2^J)^(saving+1)))
    (large : (∑j,shares j) ≤ 2^J) :
    (∑j,expense j) ≤ hosts*((∑j,leads j)*scale J (∑j,rates j))+
      slots*((∑j,leads j)*scale J (∑j,rates j))+copies/(2^J)^saving := by
  let unit:=scale J (∑j,rates j)
  let quotient:=copies/(2^J)^(saving+1)
  have region (j : Fin n) : expense j ≤ hosts*(leads j*unit)+slots*(leads j*unit)+shares j*quotient := by
    have one : rates j ≤ ∑i,rates i := Finset.single_le_sum (fun i _=>Nat.zero_le (rates i)) (Finset.mem_univ j)
    have growing : scale J (rates j) ≤ unit:=Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.mul_le_mul_right _ one)
    have per:=Nat.mul_le_mul_left (leads j) growing
    exact (paid j).trans (Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_left _ per) (Nat.mul_le_mul_left _ per)) _)
  have shared:(∑j,shares j)*quotient ≤ copies/(2^J)^saving := by
    apply (Nat.le_div_iff_mul_le (Nat.pow_pos (Nat.two_pow_pos _))).mpr
    calc
      _ ≤ (2^J*quotient)*(2^J)^saving:=Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ large)
      _ = quotient*(2^J)^(saving+1):=by rw [pow_succ];ring
      _ ≤ copies:=Nat.div_mul_le_self ..
  apply (Finset.sum_le_sum fun j _=>region j).trans
  simpa only [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_mul,unit] using
    (Nat.add_le_add_left shared (hosts*((∑j,leads j)*unit)+slots*((∑j,leads j)*unit)))

theorem total_paid (x : EnteredCharges) (J hosts slots copies saving : ℕ)
    (leads rates shares : Fin 14 → ℕ)
    (paid : ∀j,x.amount j ≤ hosts*(leads j*scale J (rates j))+
      slots*(leads j*scale J (rates j))+shares j*(copies/(2^J)^(saving+1)))
    (large : (∑j,shares j) ≤ 2^J) :
    x.total ≤ hosts*((∑j,leads j)*scale J (∑j,rates j))+
      slots*((∑j,leads j)*scale J (∑j,rates j))+copies/(2^J)^saving := by
  rw [←sum_amount]
  exact finite_paid x.amount J hosts slots copies saving leads rates shares paid large

def paddedAmount (x : EnteredCharges) (hostPad : ℕ) : Fin 15 → ℕ := Fin.cons hostPad x.amount

theorem sum_padded (x : EnteredCharges) (hostPad : ℕ) :
    (∑j,x.paddedAmount hostPad j)=hostPad+x.total := by
  rw [Fin.sum_univ_succ]
  simp only [paddedAmount,Fin.cons_zero,Fin.cons_succ,sum_amount]

/-- The shared factor is absorbed once, even when the calendar divisor is
chosen after the bounds for all fifteen stages have been fixed. -/
theorem uniform {Param : Type*} {Sample : Param → ℕ → Type*}
    (divisor : Param → ℕ) (allowed : Param → Prop) (positive : ∀p,allowed p → 0 < divisor p)
    (cost : ∀p h,Sample p h → EnteredCharges) (archive hosts slots copies : ∀p h,Sample p h → ℕ)
    (saving : ℕ)
    (price : ∀j : Fin 15,∃C E share : ℕ,∀p,allowed p → ∀ᶠ h : ℕ in Filter.atTop,∀i : Sample p h,
      let J:=Nat.log 2 h/(2*divisor p)
      (cost p h i).paddedAmount (archive p h i) j ≤ hosts p h i*(C*scale J E)+
        slots p h i*(C*scale J E)+share*(copies p h i/(2^J)^(saving+1))) :
    ∃C E : ℕ,∀p,allowed p → ∀ᶠ h : ℕ in Filter.atTop,∀i : Sample p h,
      let J:=Nat.log 2 h/(2*divisor p)
      archive p h i+(cost p h i).total ≤ hosts p h i*(C*scale J E)+
        slots p h i*(C*scale J E)+copies p h i/(2^J)^saving := by
  classical
  choose leads rates shares estimates using price
  refine ⟨∑j,leads j,∑j,rates j,?_⟩
  intro p ok
  let count:=∑j,shares j
  have all:=Filter.eventually_all.mpr (fun j=>estimates j p ok)
  filter_upwards [all,Filter.eventually_ge_atTop (2^(count*(2*divisor p)))] with h bills late
  intro i J
  have den:0 < 2*divisor p:=Nat.mul_pos (by decide) (positive p ok)
  have big:count ≤ J:=(Nat.le_div_iff_mul_le den).mpr (Nat.le_log_of_pow_le (by decide) late)
  rw [←sum_padded]
  exact finite_paid _ J _ _ _ saving leads rates shares (fun j=>bills j i)
    (big.trans (Nat.lt_two_pow_self (n:=J)).le)

end EnteredCharges
end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
