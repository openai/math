import OAI.Hierarchy.DescentTerminalPointerPrice
import OAI.Hierarchy.DescentTerminalChartScale
import OAI.Hierarchy.DescentTerminalNodeDigit

namespace OAI
/-! # Choosing a single short input width for every actual terminal pointer column -/
namespace Hierarchy.DescentTerminalPointerDigits
open DescentCompiler.TerminalScale Filter
open scoped BigOperators

/-- All word witnesses may be rounded to one width. The matrix and the
host's sorted list of frozen digits occupy just one shared word apiece. -/
def inputWidth (groups used matrix frozen pins nodes arity ptr side : ℕ) :=
  max (max (matrix*matrix) ((frozen+1)*pins))
    (groups*max nodes (max (arity*used) (max (ptr*used) side)))

theorem input_bounds (groups used matrix frozen pins nodes arity ptr side : ℕ) :
    let d:=inputWidth groups used matrix frozen pins nodes arity ptr side
    matrix*matrix≤d ∧ (frozen+1)*pins≤d ∧ nodes*groups≤d ∧
      (arity*used)*groups≤d ∧ (ptr*used)*groups≤d ∧ side*groups≤d := by
  dsimp only [inputWidth]
  let a:=max (ptr*used) side
  let b:=max (arity*used) a
  let c:=max nodes b
  have feed (x : ℕ) (small : x≤c) :
      x*groups≤ max (max (matrix*matrix) ((frozen+1)*pins)) (groups*c):=by
    rw [Nat.mul_comm x]
    exact (Nat.mul_le_mul_left _ small).trans (Nat.le_max_right _ _)
  exact ⟨(Nat.le_max_left _ _).trans (Nat.le_max_left _ _),
    (Nat.le_max_right _ _).trans (Nat.le_max_left _ _),feed _ (Nat.le_max_left _ _),
    feed _ ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _)),
    feed _ ((Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))),
    feed _ ((Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _)))⟩

/-- The maximum depends on the fixed local capacities and the final number of groups.
No cable address or cumulative matrix field is charged at the total machine width. -/
theorem width_by_group {groups used matrix frozen pins nodes arity ptr side E : ℕ} (g : 0<groups) (e : 0<E)
    (w : matrix≤E) (f : frozen+1≤E) (p : pins≤E) (u : used≤E) (n : nodes≤E)
    (a : arity≤E) (r : ptr≤E) (s : side≤E) :
    inputWidth groups used matrix frozen pins nodes arity ptr side≤groups*E^2 := by
  have sq : E≤E^2:=by rw [pow_two];exact Nat.le_mul_of_pos_right _ e
  have hh : E^2≤groups*E^2:=Nat.le_mul_of_pos_left _ g
  have pair (x y : ℕ) (h : x≤E) (k : y≤E) : x*y≤E^2 :=by rw [pow_two];exact Nat.mul_le_mul h k
  exact max_le (max_le ((pair _ _ w w).trans hh) ((pair _ _ f p).trans hh))
    (Nat.mul_le_mul_left _ (max_le (n.trans sq) (max_le (pair _ _ a u) (max_le (pair _ _ r u) (s.trans sq)))))

/-- The horizon and residual were already chosen. Every pointer entry of the previous
stage and all current operands fit the same already-paid half-word literal table. -/
theorem eventually_lookup (τ s e B : ℕ) (hB : 0<B) (large : 2*(τ+0+(2*e+(2*s+4)))≤B) :
    ∀ᶠ h : ℕ in atTop,let J:=Nat.log 2 h/(2*B)
      ∀groups used matrix frozen pins nodes arity ptr side cap N A : ℕ,
        0<groups → groups≤2^(tail τ J)→
        (∀z∈[used,matrix,frozen+1,pins,nodes,arity,ptr,side],z≤ scale J e)→
        (∀z∈[cap,N,A],z≤ scale J s)→
        let d:=inputWidth groups used matrix frozen pins nodes arity ptr side
        d≤h/2 ∧ d*columns cap N A≤h/2 ∧
          d*columns cap N A+Nat.clog 2 (columns cap N A+1)≤h/2 := by
  filter_upwards [eventually_home τ 0 (2*e+(2*s+4)) B hB large] with h good
  dsimp only
  intro groups used matrix frozen pins nodes arity ptr side cap N A g amount source localCap
  let J:=Nat.log 2 h/(2*B)
  have hp : 0<scale J e :=Nat.two_pow_pos _
  have src:=width_by_group g hp (source matrix (by simp)) (source (frozen+1) (by simp))
    (source pins (by simp)) (source used (by simp)) (source nodes (by simp)) (source arity (by simp))
    (source ptr (by simp)) (source side (by simp))
  have power (v : ℕ) : (2*2^J)^v=scale J v :=by
    simp only [scale,show 2*2^J=2^(J+1) by rw [pow_succ,Nat.mul_comm],←pow_mul,Nat.mul_comm (J+1)]
  have capFit : columns cap N A ≤ scale J (2*s+4) := by
    rw [←power]
    exact column_bound (T:=2^J) (cap:=cap) (N:=N) (A:=A) (s:=s) (Nat.two_pow_pos _)
      (by simpa only [power] using localCap cap (by simp))
      (by simpa only [power] using localCap N (by simp))
      (by simpa only [power] using localCap A (by simp))
  have lim:=good.2 0 groups (scale J (2*e+(2*s+4))) (by simpa using amount) (by simp) le_rfl
  have bound:=Nat.mul_le_mul src capFit
  have product : (groups*(scale J e)^2)*scale J (2*s+4)=groups*scale J (2*e+(2*s+4)) :=by
    rw [pow_two,Nat.mul_assoc,scale_mul,scale_mul,two_mul e]
  rw [product] at bound
  have lpos : 1≤columns cap N A:=by unfold columns;omega
  have one:=Nat.le_mul_of_pos_right (inputWidth groups used matrix frozen pins nodes arity ptr side) lpos
  have monotone : scale J (2*s+4)≤ scale J (2*e+(2*s+4)) :=
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega))
  have extra : Nat.clog 2 (columns cap N A+1)≤groups*scale J (2*e+(2*s+4)) :=
    ((Nat.clog_le_iff_le_pow (by decide : 1<2)).mpr
      (show columns cap N A+1≤2^columns cap N A from Nat.lt_two_pow_self)).trans
      ((capFit.trans monotone).trans (Nat.le_mul_of_pos_left _ g))
  omega

end Hierarchy.DescentTerminalPointerDigits

end OAI
