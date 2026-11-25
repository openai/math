import OAI.Computability.IntegerMultiplication.Adic.Fibre

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Adic
open IntegerMultiplication.Port Strip Strip.Dims Code
variable {p j : ℕ} [NeZero p]
noncomputable section

def oppose : Tower p j ≃ Tower p j where
  toFun x := -1-x
  invFun x := -1-x
  left_inv x := by exact sub_sub_cancel _ _
  right_inv x := by exact sub_sub_cancel _ _
def mirror : Block p j ≃ Block p j :=
  ((index p j).trans oppose).trans (index p j).symm
@[simp] theorem restored (x : Block p j) : mirror.symm x=mirror x := rfl
@[simp] theorem reflects (x : Block p j) : index p j (mirror x) = -1-index p j x := by
  rw [mirror,Equiv.trans_apply,Equiv.apply_symm_apply]; rfl
theorem order (x : Block p j) :
    number (mirror x) + number x + 1 = p^j := by
  have e : least (mirror x)=veil (least x) :=
    (Holds.std _).single (by rw [reflects]; exact turned (Holds.std _))
  unfold number; rw [e,covered,length']

theorem walking : ((layout (field p j)).explore.reverse) = (layout (field p j)).tab mirror := by
  let rel (x y : Block p j) := number y < number x
  have a := clean p j
  have e : ((layout (field p j)).explore.reverse).Pairwise rel :=
    List.pairwise_reverse.mpr a
  have f : ((layout (field p j)).tab mirror).Pairwise rel := by
    rw [Series.tab,List.pairwise_map]
    apply a.imp
    intro x y hy
    change number (mirror y)<number (mirror x)
    have := order x; have := order y; omega
  let : Std.Antisymm rel := ⟨fun _ _ e q => by unfold rel at *; omega⟩
  let : Std.Irrefl rel := ⟨fun i => Nat.lt_irrefl _⟩
  apply e.eq_of_mem_iff f
  intro x
  rw [List.mem_reverse,Series.elements]
  have g := (layout (field p j)).complete x
  exact ⟨fun _ => ⟨mirror.symm x,Equiv.apply_symm_apply _ _⟩,fun _ => g⟩

theorem returning {I} (f : Block p j → I) :
    ((layout (field p j)).tab f).reverse =
    (layout (field p j)).tab (f ∘ mirror) := by
  rw [← Series.map_tab _ _ f, ← walking, Series.tab,List.map_reverse]

theorem toss {I : Type} (j : I→ℕ) (v : (i:I)→Block p (j i)→Tree)
    {w : I→ℝ} {q : I→Tree}
    (l : Carries w q (stackRun (fun i => layout (field p (j i))) v)) :
    Carries w q (stackRun (fun i => layout (field p (j i))) fun i x => v i (mirror x)) := by
  unfold stackRun at *; simp_rw [stripe_eq] at *
  simpa only [returning,Function.comp_def] using l.chain (Carries.func l.budget l.out
    List.reverse Easy.reverse)
end
end Adic

end IntegerMultiplication
end Computability
end OAI
