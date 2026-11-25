import OAI.ThreeFlat.Routing.CallPoolBudget
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

namespace OAI
/-! # Width and word cost of the signed dyadic score aggregation -/

namespace Hierarchy.DescentWalshDyadicBudget
open ThreeFlat.Routing
open scoped BigOperators

theorem floor_weighted (H b d : ℕ) :
    ∑ t ∈ Finset.range d,(H/2^t)*(b+t)≤2*H*(b+1) := by
  induction d generalizing H b with
  | zero=>simp
  | succ d ih=>
    rw [Finset.sum_range_succ']
    have terms (t : ℕ) : H/2^(t+1)*(b+(t+1))=(H/2)/2^t*((b+1)+t) := by
      rw [Nat.div_div_eq_div_mul,pow_succ,Nat.mul_comm (2^t) 2]
      congr 1; omega
    simp only [terms,Nat.pow_zero,Nat.div_one,Nat.add_zero]
    have tail := ih (H/2) (b+1)
    have half : 2*(H/2)≤H := by simpa only [Nat.mul_comm 2] using Nat.div_mul_le_self H 2
    have small := Nat.mul_le_mul_right (b+1+1) half
    nlinarith

theorem ceil_le (x d : ℕ) (positive : 0<d) : poolBatchCount x d≤x/d+1 := by
  unfold poolBatchCount
  rw [Nat.div_le_iff_le_mul positive,Nat.succ_mul]
  have rep := Nat.div_add_mod x d
  have modlt := Nat.mod_lt x positive
  rw [Nat.mul_comm d (x/d)] at rep
  omega

def sites (H t : ℕ) := poolBatchCount H (2^(t+1))

theorem sites_le (H t : ℕ) : sites H t≤H/2^t+1 := by
  apply (ceil_le _ _ (Nat.two_pow_pos _)).trans
  rw [pow_succ,←Nat.div_div_eq_div_mul]
  exact Nat.add_le_add_right (Nat.div_le_self _ _) _

theorem weighted (H b d : ℕ) :
    ∑ t ∈ Finset.range d,sites H t*(b+t)≤2*H*(b+1)+d*(b+d) := by
  calc
    _ ≤ ∑t ∈ Finset.range d,((H/2^t)*(b+t)+(b+d)) := Finset.sum_le_sum (fun t ht=>by
      have first := Nat.mul_le_mul_right (b+t) (sites_le H t)
      have before := Finset.mem_range.mp ht
      rw [Nat.add_mul,Nat.one_mul] at first
      omega)
    _ = (∑t ∈ Finset.range d,(H/2^t)*(b+t))+d*(b+d) := by simp [Finset.sum_add_distrib]
    _ ≤ _ := Nat.add_le_add_right (floor_weighted H b d) _

theorem sites_total (H d : ℕ) : ∑t ∈ Finset.range d,sites H t≤4*H+d := by
  have padded (t : ℕ) : sites H t≤(H/2^t)*(1+t)+1 :=
    (sites_le H t).trans (Nat.add_le_add_right
      (by simpa using Nat.mul_le_mul_left (H/2^t) (show 1≤1+t by omega)) 1)
  calc
    _ ≤ ∑t ∈ Finset.range d,((H/2^t)*(1+t)+1) := Finset.sum_le_sum (fun t _=>padded t)
    _ = (∑t ∈ Finset.range d,(H/2^t)*(1+t))+d := by simp [Finset.sum_add_distrib]
    _ ≤ _ := Nat.add_le_add_right (by simpa [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using floor_weighted H 1 d) d

theorem lanes (q μ p W h K : ℕ) (pos : 0<μ) (scale : W≤K*h)
    (grain : μ=q ∨ h≤16*p*μ) : W*poolBatchCount q μ≤W+16*K*p*q := by
  rcases grain with rfl|split
  · have one : poolBatchCount μ μ≤1 := by
      unfold poolBatchCount
      rw [Nat.div_le_iff_le_mul pos]
      omega
    have small := Nat.mul_le_mul_left W one
    omega
  · have small := Nat.mul_le_mul_left W (ceil_le q μ pos)
    have wb : W≤16*K*p*μ := scale.trans (by
      calc K*h ≤ K*(16*p*μ) := Nat.mul_le_mul_left _ split
           _ = _ := by ring)
    have part : W*(q/μ)≤16*K*p*q := calc
      _ ≤ (16*K*p*μ)*(q/μ) := Nat.mul_le_mul_right _ wb
      _ = 16*K*p*((q/μ)*μ) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.div_mul_le_self q μ)
    rw [Nat.mul_add,Nat.mul_one] at small
    omega

/-- Exact tick envelope of a native two-predecessor merge pass. -/
def clock (H q t μ : ℕ) := 4+200*sites H t*poolBatchCount q μ

/-- Word-operation bill for all actual precision levels. The lane mount is
either an entire radix or a batch occupying at least a sixteenth of the payload
at its true signed precision. -/
theorem paid (H q b d W h K : ℕ) (μ : ℕ→ℕ) (scale : W≤K*h) (stages : d≤H+1)
    (depth : d≤W+1) (precision : b≤W+1)
    (live : ∀t<d,0<μ t) (mount : ∀t<d,μ t=q ∨ h≤16*(b+t+1)*μ t) :
    (∑t ∈ Finset.range d,clock H q t (μ t)*W) ≤
      1004*(H+1)*W+12800*K*H*q*(b+1)+12800*K*q*(W+1)^2 := by
  let s := ∑t ∈ Finset.range d,sites H t
  let p := ∑t ∈ Finset.range d,sites H t*((b+1)+t)
  have piece (t : ℕ) (ht : t<d) : clock H q t (μ t)*W ≤
      4*W+(200*W)*sites H t + (3200*K*q)*(sites H t*((b+1)+t)) := by
    have atT := lanes q (μ t) (b+t+1) W h K (live t ht) scale (mount t ht)
    calc
      _ = 4*W+200*sites H t*(W*poolBatchCount q (μ t)) := by unfold clock;ring
      _ ≤ 4*W+200*sites H t*(W+16*K*(b+t+1)*q) := Nat.add_le_add_left (Nat.mul_le_mul_left _ atT) _
      _ = _ := by ring
  have invoice : (∑t ∈ Finset.range d,clock H q t (μ t)*W)≤d*(4*W)+(200*W)*s+(3200*K*q)*p := by
    apply (Finset.sum_le_sum (fun t ht=>piece t (Finset.mem_range.mp ht))).trans_eq
    simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_id,
      ←Finset.mul_sum,s,p]
  have sg : s≤4*H+d := sites_total ..
  have pg : p≤2*H*((b+1)+1)+d*((b+1)+d) := weighted ..
  have first : d*(4*W)+(200*W)*s≤1004*(H+1)*W := by
    have sb : s≤5*(H+1) := by omega
    have drow := Nat.mul_le_mul_right (4*W) stages
    have weightedSites := Nat.mul_le_mul_left (200*W) sb
    nlinarith
  have right : (b+1)+d≤3*(W+1) := by omega
  have depthCost := Nat.mul_le_mul depth right
  have bulk : 2*H*((b+1)+1)≤4*H*(b+1) := by nlinarith
  have pp : p≤4*H*(b+1)+4*(W+1)^2 := by nlinarith
  have prices := Nat.mul_le_mul_left (3200*K*q) pp
  apply invoice.trans
  nlinarith

theorem physical (H m b W h K : ℕ) (μ : ℕ→ℕ) (scale : W≤K*h) (host : H≤2^W) (precision : b≤W+1)
    (live : ∀t<Nat.clog 2 H,0<μ t)
    (mount : ∀t<Nat.clog 2 H,μ t=2^m ∨ h≤16*(b+t+1)*μ t) :
    (∑t ∈ Finset.range (Nat.clog 2 H),clock H (2^m) t (μ t)*W) ≤
      1004*(H+1)*W+12800*K*H*2^m*(b+1)+12800*K*2^m*(W+1)^2 := by
  apply paid _ _ _ _ _ _ _ μ scale _ _ precision live mount
  · exact ((Nat.clog_le_iff_le_pow (by decide)).mpr (Nat.lt_two_pow_self.le : H≤2^H)).trans (Nat.le_succ _)
  · exact ((Nat.clog_le_iff_le_pow (by decide)).mpr host).trans (Nat.le_succ _)

/-- A terminal level and one shared immutable dictionary per level. -/
theorem inclusive (H m b W h K : ℕ) (μ : ℕ→ℕ) (scale : W≤K*h) (host : H≤2^W) (precision : b≤W+1)
    (live : ∀t≤Nat.clog 2 H,0<μ t)
    (mount : ∀t≤Nat.clog 2 H,μ t=2^m ∨ h≤16*(b+t+1)*μ t) :
    (∑t ∈ Finset.range (Nat.clog 2 H+1),(clock H (2^m) t (μ t)+2^(h/2))*W) ≤
      1004*(H+1)*W+12800*K*H*2^m*(b+1)+12800*K*2^m*(W+1)^2+(Nat.clog 2 H+1)*2^(h/2)*W := by
  have edge := (Nat.clog_le_iff_le_pow (by decide : 1<2)).mpr (Nat.lt_two_pow_self.le : H≤2^H)
  have depth := (Nat.clog_le_iff_le_pow (by decide : 1<2)).mpr host
  have bill := paid H (2^m) b (Nat.clog 2 H+1) W h K μ scale (by omega) (by omega) precision
    (fun t ht=>live t (Nat.le_of_lt_succ ht)) (fun t ht=>mount t (Nat.le_of_lt_succ ht))
  calc
    _ = (∑t ∈ Finset.range (Nat.clog 2 H+1),clock H (2^m) t (μ t)*W)+(Nat.clog 2 H+1)*2^(h/2)*W := by
      simp only [Nat.add_mul,Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_id]
      ring
    _ ≤ _ := Nat.add_le_add_right bill _

end Hierarchy.DescentWalshDyadicBudget

end OAI
