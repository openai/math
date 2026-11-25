import OAI.Computability.IntegerMultiplication.Scale.Season
import Mathlib.Data.Nat.GCD.BigOperators

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Cap
open Finset
variable {d:ℕ}
abbrev Bounds (d:ℕ) := Fin d → ℕ
abbrev Vector_ {d} (s:Bounds d) := (i:Fin d)→Fin (s i)
def space (s:Bounds d) := ∏ i,s i
def body (s:Bounds (d+1)) : Bounds d:= fun i=> s i.succ
abbrev bodyV {s:Bounds (d+1)} (a:Vector_ s) : Vector_ (body s) :=
  fun i=>a i.succ
def base (s:Bounds d) (i:Fin d) :=
  ∏ j:Fin d,if j < i then s j else 1

theorem space_next (s:Bounds (d+1)) : space s=s 0*space (body s) :=
  Fin.prod_univ_succ _
@[simp] theorem base0 (s:Bounds (d+1)) : base s 0=1 := by
  unfold base; simp
@[simp] theorem base_next (s:Bounds (d+1)) (i:Fin d):
    base s i.succ=s 0 * base (body s) i := by
  unfold base body; rw [Fin.prod_univ_succ]
  simp

def amount (s:Bounds d) (v:Vector_ s) :=
  ∑ i:Fin d,(v i).val*base s i
theorem amount_next (s:Bounds (d+1)) (v:Vector_ s):
    amount s v=(v 0).val +s 0*amount (body s) (bodyV v) := by
  unfold amount
  rw [Fin.sum_univ_succ]; simp only [base0, mul_one,base_next]
  rw [mul_sum]
  congr 1
  exact sum_congr rfl (fun i hi=> by rw [mul_left_comm])
theorem amount_lt (s:Bounds d) (v:Vector_ s) :
    amount s v < space s := by
  induction d with
  | zero => simp [amount,space]
  | succ d ih=>
    rw [amount_next,space_next]
    have u:=ih (body s) (bodyV v)
    have t := (v 0).isLt
    nlinarith [Nat.mul_le_mul_left (s 0) (show amount (body s) (bodyV v)+1≤ space (body s) from u)]
def index (s:Bounds d) : Vector_ s → Fin (space s):=
  fun i=>⟨amount s i,amount_lt ..⟩

theorem amount_inj (s:Bounds d) (x y:Vector_ s)
    (e:amount s x=amount s y):
    x=y := by
  induction d with
  | zero=> exact Subsingleton.elim _ _
  | succ d ih=>
    have p:= (x 0).isLt
    have q:= (y 0).isLt
    have t : 0<s 0:= by omega
    rw [amount_next,amount_next] at e
    have c:= congrArg (·%s 0) e
    have g:= congrArg (·/s 0) e
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt p,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt q] at c
    rw [Nat.add_mul_div_left _ _ t,Nat.div_eq_of_lt p,zero_add,Nat.add_mul_div_left _ _ t,Nat.div_eq_of_lt q,zero_add] at g
    funext i
    refine Fin.cases (Fin.ext c) (fun i=> ?_) i
    exact congrFun (ih _ (bodyV x) (bodyV y) g) i
theorem card (s:Bounds d):
    Fintype.card (Vector_ s)=space s := by unfold Vector_ space; simp
noncomputable def rank (s:Bounds d): Vector_ s ≃ Fin (space s):=
  Equiv.ofBijective (index s)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨fun _ _ e=> amount_inj _ _ _ (Fin.ext_iff.mp e),
      by rw [card,Fintype.card_fin]⟩)

end Cap

end IntegerMultiplication
end Computability
end OAI
