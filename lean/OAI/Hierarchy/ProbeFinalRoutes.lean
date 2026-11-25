import OAI.Hierarchy.ProbeBudget
import OAI.Hierarchy.ProbeScore

namespace OAI
/-! # Paying the actual residual and unused-catalyst routes -/

namespace Hierarchy.AdaptiveProbe
open scoped BigOperators
noncomputable section

variable {E I C : Type*} [Fintype E] [DecidableEq E] [Fintype I] [Fintype C]

def routeLoad (route : I → List E) (bits : I → ℕ) (e : E) : ℕ :=
  ∑ i,(route i).count e*bits i

/-- Histograms count every occurrence of a link, even when a walk repeats it. -/
theorem route_price (len : E → ℝ) (walk : List E) :
    (∑ e,len e*(walk.count e:ℝ)) = (walk.map len).sum := by
  induction walk with
  | nil => simp
  | cons e tail ih =>
    classical
    simp only [List.count_cons,List.map_cons,List.sum_cons]
    simp_rw [Nat.cast_add,mul_add]
    rw [Finset.sum_add_distrib]
    rw [ih]
    have delta : (∑ z,len z*(((if e==z then 1 else 0):ℕ):ℝ))=len e := by
      simp [apply_ite,beq_iff_eq]
    rw [delta,add_comm]

theorem stock_route_bill (len : E→ℝ) (route : I→List E) (bits : I→ℕ) (w : ℕ) :
    (∑ e,len e*((routeLoad route bits e:ℝ)/w)) =
      ∑ i,(route i |>.map len).sum*((bits i:ℝ)/w) := by
  calc
    _ = ∑ e,∑ i,(len e*((route i).count e:ℝ))*((bits i:ℝ)/w) := by
      simp [routeLoad,Finset.mul_sum,Nat.cast_sum,div_eq_mul_inv,
        mul_assoc,Finset.sum_mul]
    _ = ∑ i,∑ e,(len e*((route i).count e:ℝ))*((bits i:ℝ)/w) := Finset.sum_comm
    _ = _ := by simp only [← Finset.sum_mul,route_price]

/-- A link incurs its activation charge once while all routed bit widths add.
The result allows different routes and arbitrary reserve multiplicities per pair. -/
theorem settle_installed_routes (p q Q Λ : ℝ) (n w M : ℕ) (_hn : 0<n) (hw : 0<w)
    (t len : E→ℝ) (installed : E→ℕ) (cash : ℝ) (box : I→ℝ)
    (core : I→List E) (stock : I→ℕ) (center : C→List E) (reserved used : C→ℕ)
    (within : ∀ c,used c≤reserved c) (ordinary : ∀ i,((core i).map len).sum≤box i)
    (central : ∀ c,((center c).map len).sum≤2*M)
    (prepaid : (∑ e,(len e*((installed e:ℝ)/w)+Λ*capacity p q Q (t e) (len e))) ≤
      cash+2*M*(∑ c,(used c:ℝ))/w)
    (budget : cash + pairing (fun i=>(stock i:ℝ)/w) box ≤ 6*n) :
    TermBudget p q Q Λ n w M (∑ c,reserved c) t len
      (fun e=>((installed e+routeLoad core stock e+routeLoad center (fun c=>reserved c-used c) e:ℕ):ℝ)/w) := by
  let remain := fun c=>reserved c-used c
  have billCore : (∑ e,len e*((routeLoad core stock e:ℝ)/w))≤pairing (fun i=>(stock i:ℝ)/w) box := by
    rw [stock_route_bill]
    exact Finset.sum_le_sum fun i _=> (mul_le_mul_of_nonneg_right (ordinary i) (by positivity)).trans_eq (mul_comm ..)
  have billRet : (∑ e,len e*((routeLoad center remain e:ℝ)/w))≤2*M*(∑ c,(remain c:ℝ))/w := by
    rw [stock_route_bill]
    calc
      _ ≤ ∑ c,2*(M:ℝ)*((remain c:ℝ)/w) := Finset.sum_le_sum fun c _=>
        mul_le_mul_of_nonneg_right (central c) (by positivity)
      _ = _ := by simp [Finset.mul_sum,Finset.sum_div,mul_div_assoc]
  have pieces (e : E) :
      len e*(((installed e+routeLoad core stock e+routeLoad center remain e:ℕ):ℝ)/w)+Λ*capacity p q Q (t e) (len e) =
        (len e*((installed e:ℝ)/w)+Λ*capacity p q Q (t e) (len e))+
        len e*((routeLoad core stock e:ℝ)/w)+len e*((routeLoad center remain e:ℝ)/w) := by
    push_cast; ring
  have reserve : (∑ c,(remain c:ℝ))+(∑ c,(used c:ℝ))=(∑ c,reserved c:ℕ) := by
    rw [← Finset.sum_add_distrib,Nat.cast_sum]
    exact Finset.sum_congr rfl (fun c _=>by simp [remain,Nat.cast_sub (within c)])
  have split := congrArg (fun z:ℝ=>2*M*z/w) reserve
  simp only [mul_add,add_div] at split
  change (∑ e,(len e*(((installed e+routeLoad core stock e+routeLoad center remain e:ℕ):ℝ)/w)+
    Λ*capacity p q Q (t e) (len e)))≤_
  simp only [pieces,Finset.sum_add_distrib]
  rw [Finset.sum_add_distrib] at prepaid
  linarith [Nat.cast_nonneg (α:=ℝ) n]

end
end Hierarchy.AdaptiveProbe

end OAI
