import OAI.Computability.IntegerMultiplication.Adic.Words

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Adic
open Strip Strip.Dims
variable {p l : ℕ}

theorem clean (p l : ℕ) [NeZero p] :
    (layout (field p l)).explore.Pairwise (fun i j => number i < number j) := by
  induction l with
  | zero => change List.Pairwise (fun (i j : Unit) => number (l:=0) (p:=p) i < number (l:=0) (p:=p) j) [()]; simp
  | succ l ih =>
    change (layout (p::field p l)).explore.Pairwise _
    rw [← Series.tab_id, tab_cons]
    change List.Pairwise (fun i j : Block p (l+1) => number i < number j)
      (((Series.natural p).tab fun b => (layout (field p l)).tab fun i => id (node (b, i))).flatten)
    apply List.pairwise_flatten.mpr
    have he (j : Fin p) := ((layout (field p l)).elements (fun i => head j i))
    constructor
    · intro c e
      rcases (Series.elements ..).mp e with ⟨f,h⟩
      rw [← h]
      change List.Pairwise (fun i j : Pin (p :: field p l) =>
        number (p:=p) (l:=l+1) i < number (p:=p) (l:=l+1) j)
        ((layout (field p l)).tab (fun i => head f i))
      exact ih.map (fun i => head f i)
        (by intro i j e; simpa only [number_cons, Function.onFun_apply,
          Nat.add_lt_add_iff_right] using e)
    have ascend : (Series.natural p).explore.Pairwise ((· < ·)) := by
      change (List.finRange p).Pairwise _
      apply List.pairwise_iff_getElem.mpr
      intro i j hi hj h
      simp; exact h
    apply ascend.map (fun b => (layout (field p l)).tab (fun i => head b i))
    intro i j e x hx y hy
    rcases (he i _).mp hx with ⟨ix,rfl⟩
    rcases (he j _).mp hy with ⟨iy,rfl⟩
    rw [number_cons,number_cons]
    have hp := number_lt ix
    have hb : p^l*(i.val+1) ≤ p^l*j.val :=
      Nat.mul_le_mul_left _ (by exact e)
    rw [Nat.mul_add,Nat.mul_one] at hb
    omega

theorem field_add (p i k : ℕ) : field p (i+k) = field p i ++ field p k := by
  induction i with
  | zero => simp [field]
  | succ i ih => rw [Nat.add_right_comm,field,field,List.cons_append,ih]
-- direct Equiv splitting blocks, arithmetic correspondence
def binary (p : ℕ) (i k : ℕ) : Block p i × Block p k ≃ Block p (i+k) :=
  (Dims.Union ..).trans (Equiv.cast (congrArg Pin (field_add p i k).symm))

theorem schedule {i k : ℕ} {X : Type} (f : Block p (i+k) → X) :
    (layout (field p (i+k))).tab f =
      ((layout (field p i)).cart (layout (field p k))).tab (f ∘ binary p i k) := by
  -- cast of f input
  suffices z : ∀ (g : Tape) (e : field p i++field p k=g) (f : Pin g→X),
    (layout g).tab f = ((layout (field p i)).cart (layout (field p k))).tab
      (f ∘ ((Dims.Union _ _).trans (Equiv.cast (congrArg Pin e)))) by apply z; exact (field_add p i k).symm
  rintro _ rfl f
  exact tab_cat ..
end Adic

end IntegerMultiplication
end Computability
end OAI
