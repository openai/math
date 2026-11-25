import OAI.Hierarchy.DescentTerminalRouteDimensions
import OAI.Hierarchy.DescentTerminalLocalPortNames
import OAI.Hierarchy.DescentTerminalGraphPositions

namespace OAI
/-! # Numeric names shared by both orders of a terminal position -/
namespace Hierarchy.DescentTerminalLocalPortBook
open DescentTerminalRecipeRows DescentTerminalGraphPositions Computability.VPVNP.BurstRAM
open scoped Classical


def rowName {G V M A : ℕ} (t : Site) (f : Room t G V M A) :
    t.Name ↪ Word (nameBits G M) where
  toFun r := ⟨r.1.val*M+r.2.val, by
    have offset := Nat.lt_of_lt_of_le r.2.isLt (f.size r.1)
    have place := Nat.mul_le_mul_right M (Nat.succ_le_of_lt (r.1.isLt.trans_le f.groups))
    rw [Nat.succ_mul] at place
    exact (by omega : r.1.val*M+r.2.val<G*M+1).trans_le (Nat.le_pow_clog (by decide) _)⟩
  inj' := by
    rintro ⟨g,j⟩ ⟨g',j'⟩ eqn
    have same:=congrArg Fin.val eqn
    change g.val*M+j.val=g'.val*M+j'.val at same
    have left:=j.isLt.trans_le (f.size g)
    have right:=j'.isLt.trans_le (f.size g')
    have positive:0<M:=Nat.zero_lt_of_lt right
    have coord : g.val = g'.val := by
      simpa only [Nat.mul_comm g.val M, Nat.mul_comm g'.val M, Nat.mul_add_div positive,
        Nat.div_eq_of_lt left, Nat.div_eq_of_lt right, Nat.add_zero] using congrArg (· / M) same
    have groups : g = g' := Fin.ext coord
    subst g'
    exact congrArg (Sigma.mk g) (Fin.ext (Nat.add_left_cancel same))

def refName {G V M A : ℕ} (t : Site) (f : Room t G V M A) (r : t.Arg) : Word (nameBits G M) :=
  rowName t f (t.arg r.1 r.2)

theorem names_eq {G V M A : ℕ} (t : Site) (f : Room t G V M A) (r : t.Arg) :
    refName t f r=rowName t f (t.arg r.1 r.2) := rfl

/-- Physical array form. An unused position in either rectangle has literal value zero. -/
theorem name_at {G V M A : ℕ} (t : Site) (f : Room t G V M A) (g : Fin G) (j : Fin M) :
    ((issue t f (rowName t f) (refName t f)).portName g j).val=
      if hg:g.val<t.groups then if j.val<t.size ⟨g.val,hg⟩ then g.val*M+j.val else 0 else 0 := by
  classical
  by_cases hg:g.val<t.groups
  · by_cases hj:j.val<t.size ⟨g.val,hg⟩ <;> simp [issue,hg,hj]; rfl
  · simp [issue,hg]

end Hierarchy.DescentTerminalLocalPortBook

end OAI
