import Mathlib.Data.Nat.Basic

namespace OAI
/-! # The relative shape threshold carried by a single numbered peer -/
namespace Hierarchy.DescentRelativeClassChip

def threshold (width root : ℕ) : Option ℕ → ℕ
  | none=>0
  | some peer=>if peer/width<root then 1 else if peer/width=root then 2+peer%width else 0

def earlier (tag shape : ℕ) : Bool := decide (tag=1 ∨ 2≤tag ∧ tag-2<shape)

theorem threshold_room (width root : ℕ) (positive : 0<width) (peer : Option ℕ) :
    threshold width root peer<width+2 := by
  cases peer with
  | none=>change 0<width+2;omega
  | some a=>
    have small:=Nat.mod_lt a positive
    by_cases low : a/width<root
    · simp [threshold,low]
    · by_cases same : a/width=root
      · simpa [threshold,low,same] using (by omega : 2+a%width<width+2)
      · simp [threshold,low,same]

theorem threshold_read (width root shape : ℕ) (positive : 0<width) (small : shape<width) (p : Option ℕ) :
    earlier (threshold width root p) shape=p.any (·<shape+width*root) := by
  cases p with
  | none=>rfl
  | some n=>
    have frac:=Nat.mod_lt n positive
    have decomp:=Nat.mod_add_div n width
    by_cases lt : n/width<root
    · have hi : (n/width+1)*width≤root*width:=Nat.mul_le_mul_right width lt
      rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm (n/width) width,Nat.mul_comm root width] at hi
      have yes : n<shape+width*root:=by omega
      simp [earlier,threshold,lt,yes]
    · by_cases eqn : n/width=root
      · rw [eqn] at decomp
        change earlier (threshold width root (some n)) shape=decide (n<shape+width*root)
        rw [show threshold width root (some n)=2+n%width by simp [threshold,eqn]]
        unfold earlier
        by_cases early : n<shape+width*root <;> simp [early] <;> omega
      · have lo : (root+1)*width≤n/width*width:=Nat.mul_le_mul_right width (by omega)
        rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm root width,Nat.mul_comm (n/width) width] at lo
        have no : ¬n<shape+width*root:=by omega
        simp [earlier,threshold,lt,eqn,no]

end Hierarchy.DescentRelativeClassChip

end OAI
