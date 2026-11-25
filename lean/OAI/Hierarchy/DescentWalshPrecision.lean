import OAI.Hierarchy.DescentWalshWordBounds
import OAI.Hierarchy.DescentWalshPrecisionNumbers
import OAI.Hierarchy.DescentMeasuredWeights
import OAI.Hierarchy.DescentPackedWalshPrice

namespace OAI
/-! # One short precision covers each original measurement and its weighted correlations -/
namespace Hierarchy.DescentWalshPrecision
open DescentGL DescentIntegerScale DescentMeasuredWeights DescentPackedWalsh
open scoped BigOperators

theorem numerator_room (m f K u full : ℕ) (fit : full≤2^u) :
    2^(3*m)*full^2<2^(bits m f K u) := by
  have square:=Nat.pow_le_pow_left fit 2
  apply lt_of_le_of_lt (Nat.mul_le_mul_left (2^(3*m)) square)
  rw [←pow_mul,←pow_add]
  apply Nat.pow_lt_pow_right (by decide : 1<2)
  unfold bits
  omega

theorem gain_room {A C : Type} (m f K u full : ℕ) (height : A→ℕ) (levels : ∀a,height a ≤ m+1)
    (fit : full≤2^u) (i : Item height C) : gain height f full K i<2^(gainBits m f K u) := by
  have coeff : (Sum.elim (fun a : Σ v,Fin (height v)=>4*2^((a.2.val+7)/8)) (fun _ : C=>K^2) i)≤2^rate m K := by
    cases i with
    | inl a=>
      have lev:=a.2.isLt.trans_le (levels a.1)
      have depth : (a.2.val+7)/8≤(m+7)/8:=Nat.div_le_div_right (by omega)
      change 4*2^((a.2.val+7)/8)≤_
      rw [show 4=2^2 by decide,←pow_add]
      exact Nat.pow_le_pow_right (by decide) ((Nat.add_le_add_left depth 2).trans (le_max_left ..))
    | inr c=>
      change K^2≤_
      apply (Nat.pow_le_pow_left (Nat.le_pow_clog (by decide : 1<2) K) 2).trans
      rw [←pow_mul,Nat.mul_comm (Nat.clog 2 K)]
      exact Nat.pow_le_pow_right (by decide) (le_max_right ..)
  have «prefix»:=Nat.mul_le_mul (Nat.mul_le_mul_left (2^f) fit) coeff
  have cap : gain height f full K i≤2^(f+u+rate m K) := by
    rw [pow_add,pow_add]
    cases i <;> exact «prefix»
  exact cap.trans_lt (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _))

theorem correlation_room {m f K u : ℕ} (x : Bits m→ℕ) (full gain : ℕ) (z : Bits m)
    (fit : full≤2^u) (input : ∀i,x i≤full) (stored : gain<2^(gainBits m f K u)) :
    gain*natCorrelation x z<2^(bits m f K u) := by
  have all_ := Finset.sum_le_sum (s:=Finset.univ) (fun (a : Bits m) _=>Nat.mul_le_mul (input a) (input (a+z)))
  have card : Fintype.card (Bits m)=2^m := by simp [DescentGL.Bits]
  have corr : natCorrelation x z≤2^m*full^2 := by
    simpa only [natCorrelation,Finset.sum_const,Finset.card_univ,card,nsmul_eq_mul,Nat.cast_id,pow_two] using all_
  have cut := Nat.mul_le_mul stored.le (corr.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left fit 2)))
  apply cut.trans_lt
  rw [←pow_mul,←pow_add,←pow_add]
  apply Nat.pow_lt_pow_right (by decide)
  unfold bits
  omega

theorem cutoff_room (m f K u h : ℕ)
    (height : m+Nat.clog 2 (m+2)+8*bits m f K u≤h/2) :
    Nat.clog 2 (m+2)+(m+u)≤h/2 ∧ 2^(Nat.clog 2 (m+2)+(m+u))≤2^(h/2) := by
  have price : u≤bits m f K u := by unfold bits;omega
  have whole : Nat.clog 2 (m+2)+(m+u)≤h/2 := by omega
  exact ⟨whole,Nat.pow_le_pow_right (by decide) whole⟩

end Hierarchy.DescentWalshPrecision

end OAI
