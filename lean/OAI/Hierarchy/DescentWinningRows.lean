import OAI.Hierarchy.DescentColonyScoreCore
import OAI.Hierarchy.DescentColonyWinningSlabs

namespace OAI
/-! # The semantic outgoing panels chosen by a fixed multiplier -/
namespace Hierarchy
namespace DescentColonies.WinningSlabs.Selected
open DescentGL
variable {G H k : ℕ}
noncomputable def winningRows (income : Fin H→List (Fin H)) (weight : Fin G→Fin H→Block k→ℕ) (D cap : ℕ)
    (a : Bits k) (μ : Nonzero k) (g : Fin G) := Scan.build income (multiplierLoad (weight g) a μ.val) D cap k

def winningAmounts (amount : Fin G→Fin H→Block k→ℕ) (a : Bits k) (μ : Nonzero k) (g : Fin G) :=
  multiplierLoad (amount g) a μ.val

end DescentColonies.WinningSlabs.Selected
namespace DescentAffineColors.RosterPaint
open DescentColonies DescentGL DescentColonies.WinningSlabs
open scoped BigOperators Classical
variable {G H k : ℕ}
/-- The dyadic slab directory partitions the outgoing words, including those
in zero-load rows. Its cost bound can use the sum on the original graph. -/
theorem mass (rows : Fin G→Scan.Buffer (Fin H) k) (amount : Fin G→Fin H→Block k→ℕ) :
    (∑ c,∑x,worldValue rows amount c x)=∑g,∑v,∑x,amount g v x := by
  have split (g : Fin G) (v : Fin H) (x : Block k) :
      (∑j : Fin (keys k).length,filtered (rows g) v (amount g v) (keyName k j.val) x)=amount g v x := by
    let d := Scan.leafDepth (rows g) v x
    let target := (d,group d x)
    have depth : d≤k := Scan.leafDepth_le ..
    have keyLimit : group d x<2^d := by
      apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2
      change x.val<2^d*2^(k-d)
      rw [←pow_add,Nat.add_sub_of_le depth]
      exact x.isLt
    have member := (mem_keys k d (group d x)).mpr ⟨depth,keyLimit⟩
    let key : Fin (keys k).length := ⟨(keys k).idxOf target,List.idxOf_lt_length_iff.mpr member⟩
    have val : keyName k key.val=target := by
      simp only [keyName,dite_eq_left key.isLt]
      exact List.idxOf_get (a:=target) (l:=keys k) key.isLt
    have test (j : Fin (keys k).length) : WinningSlabs.member (rows g) v (keyName k j.val).1 (keyName k j.val).2 x ↔ j=key := by
      constructor
      · rintro ⟨level,idx⟩
        apply name_injective (k:=k)
        change keyName k j.val = keyName k key.val
        rw [val]
        exact Prod.ext level.symm (idx.symm.trans (congrArg (fun d => group d x) level.symm))
      · rintro rfl
        rw [val]
        exact ⟨rfl,rfl⟩
    simp [filtered,test]
  rw [←(directory G H k).sum_comp
    (fun c : Slot G H k => ∑ x : Block k,worldValue rows amount c x)]
  simp only [worldValue,Equiv.symm_apply_apply,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro g _
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _=>split g v x

end DescentAffineColors.RosterPaint
end Hierarchy

end OAI
