import OAI.Hierarchy.DescentResetCoarseGroups
import OAI.Hierarchy.DescentFineTerminals

namespace OAI
/-! # Every common hub is populated in every surviving block -/

namespace Hierarchy.DescentFineTerminals
open DescentGL DescentColonies DescentContacts DescentRelativeContacts DescentChosenRouter
open scoped Classical
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V] {k f g r B D n : ℕ}
variable (near : V→Finset V) (wt : V→Block k→ℕ) (room : ∀v i,wt v i≤B) (b : V→ℕ)
variable (hub : V→Bool) (L : Layout k) (row : Bool→V×Block k→Fin (2^n))

theorem hub_shape (t : ↥(Directory (D:=D) (f:=f) (g:=g) near wt room b hub L row)) :
    hub t.val.1=true ↔ t.val.2.2=none := by
  obtain ⟨⟨s,⟨v,x⟩⟩,_,eq⟩ := Finset.mem_image.mp t.property
  change name (D:=D) (f:=f) (g:=g) near wt room b hub L row s (v,x)=t.val at eq
  apply (congrArg (fun z : V × Endpoint (2^n) => hub z.1=true ↔ z.2.2=none) eq).mp
  cases hh : hub v <;> simp [name,hh]

theorem hub_cover (gr : g≤r) (rk : r≤k)
    (t : ↥(Directory (D:=D) (f:=f) (g:=g) near wt room b hub L row))
    (tag : hub t.val.1=true) (c : Block (k-r)) :
    ∃t' : ↥(Directory (D:=D) (f:=f) (g:=g) near wt room b hub L row),
      hub t'.val.1=true ∧ coarseName (k-r) t'.val=c.val ∧
      shortName (k-r) t'.val=shortName (k-r) t.val := by
  obtain ⟨⟨s,⟨v,x⟩⟩,_,eq⟩ := Finset.mem_image.mp t.property
  change name (D:=D) (f:=f) (g:=g) near wt room b hub L row s (v,x)=t.val at eq
  rw [←eq] at tag ⊢
  have first : (name (D:=D) (f:=f) (g:=g) near wt room b hub L row s (v,x)).1 = v := by
    cases hv : hub v <;> simp [name,hv]
  have atV : hub v=true := by simpa only [first] using tag
  let inner := 2^(r-g)
  let last := group (k-g) (rearrange L x)%inner
  have positive : 0 < inner := Nat.two_pow_pos _
  have final_lt : last < inner := Nat.mod_lt _ positive
  let addr := inner*c.val+last
  have addrFit : addr<2^(k-g) := by
    calc
      addr < inner*c.val+inner := Nat.add_lt_add_left final_lt _
      _ = inner*(c.val+1) := by ring
      _ ≤ inner*2^(k-r) := Nat.mul_le_mul_left _ c.isLt
      _ = 2^(k-g) := by rw [←Nat.pow_add];congr 1;omega
  let y : Block k := ⟨addr*2^g,by
    calc addr*2^g < 2^(k-g)*2^g := Nat.mul_lt_mul_of_pos_right addrFit (Nat.two_pow_pos _)
         _ = 2^k := by rw [←Nat.pow_add, Nat.sub_add_cancel (gr.trans rk)]⟩
  have part : group (k-g) y=addr := by
    change (addr*2^g)/2^(k-(k-g))=addr
    rw [Nat.sub_sub_self (gr.trans rk),Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
  have dep : k-g-(k-r)=r-g := by omega
  let out := terminal (D:=D) (f:=f) (g:=g) near wt room b hub L row s (v,(rearrange L).symm y)
  refine ⟨out,?_,?_,?_⟩
  · simp [out,terminal,name,atV]
  · simp only [out,terminal,name,atV,ite_true,Equiv.apply_symm_apply,coarseName,part,dep]
    change (inner*c.val+last)/inner=c.val
    rw [Nat.mul_add_div positive,Nat.div_eq_of_lt final_lt,Nat.add_zero]
  · have sameDigit : addr%inner=last := by
      change (inner*c.val+last)%inner=last
      rw [Nat.mul_add_mod,Nat.mod_eq_of_lt final_lt]
    simp only [out,terminal,name,atV,ite_true,Equiv.apply_symm_apply,shortName,part,dep]
    rw [show addr % 2^(r-g) = group (k-g) (rearrange L x) % 2^(r-g) from sameDigit]

end
end Hierarchy.DescentFineTerminals

end OAI
