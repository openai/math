import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.List.OfFn

namespace OAI
/-! # Numerical names of the original packet role and the first copy of a paid row -/

noncomputable section
namespace Hierarchy.WireTelescope.ChosenPackets.RowRouting
open scoped Classical

def halfCode {n : ℕ} (i : Fin n) (b : Bool) : Fin (n*2) := finProdFinEquiv (i,finTwoEquiv.symm b)

theorem halfCode_val {n : ℕ} (i : Fin n) (b : Bool) : (halfCode i b).val=2*i.val+b.toNat := by
  cases b <;> simp [halfCode,finProdFinEquiv_apply_val,finTwoEquiv,Bool.toNat,Nat.add_comm]

namespace PostCode
variable {M n : ℕ} (ids : Fin n→Fin M)

def first (key : Fin M) : Fin (n+1) := ⟨min ((List.ofFn (fun i=>(ids i).val)).idxOf key.val) n,by omega⟩

theorem first_live (key : Fin M) (seen : ∃i,ids i=key) :
    (first ids key).val=((List.ofFn (fun i=>(ids i).val)).idxOf key.val) := by
  obtain ⟨i,hit⟩:=seen
  have mem : key.val∈List.ofFn (fun i=>(ids i).val) := List.mem_ofFn.mpr ⟨i,congrArg Fin.val hit⟩
  have bound:=List.idxOf_lt_length_of_mem mem
  simp only [List.length_ofFn] at bound
  exact Nat.min_eq_left bound.le

theorem first_injective {x y : Fin M} (hx : ∃i,ids i=x) (hy : ∃i,ids i=y)
    (same : first ids x=first ids y) : x=y := by
  have ix:=congrArg Fin.val same
  rw [first_live ids _ hx,first_live ids _ hy] at ix
  obtain ⟨i,hi⟩:=hx
  obtain ⟨j,hj⟩:=hy
  let xs:=List.ofFn (fun i=>(ids i).val)
  have ax:=List.idxOf_lt_length_of_mem (show x.val∈xs from List.mem_ofFn.mpr ⟨i,congrArg Fin.val hi⟩)
  have ay:=List.idxOf_lt_length_of_mem (show y.val∈xs from List.mem_ofFn.mpr ⟨j,congrArg Fin.val hj⟩)
  exact Fin.ext ((List.getElem_idxOf ax).symm.trans ((getElem_congr_idx ix).trans (List.getElem_idxOf ay)))

def after (oldRoles : ℕ) (key : Fin M) (b : Bool) : ℕ :=
  oldRoles*2+(halfCode (first ids key) b).val

theorem after_lt (roles : ℕ) (key : Fin M) (b : Bool) :
    after ids roles key b<roles*2+(n+1)*2 := Nat.add_lt_add_left (halfCode _ b).isLt _

theorem after_injective {roles : ℕ} {x y : Fin M} {b b' : Bool}
    (hx : ∃i,ids i=x) (hy : ∃i,ids i=y) (code : after ids roles x b=after ids roles y b') :
    x=y ∧ b=b' := by
  have h : halfCode (first ids x) b=halfCode (first ids y) b' := Fin.ext (Nat.add_left_cancel code)
  obtain ⟨eq,sides⟩:=Prod.mk.inj (finProdFinEquiv.injective h)
  exact ⟨first_injective ids hx hy eq,finTwoEquiv.symm.injective sides⟩
end PostCode

end Hierarchy.WireTelescope.ChosenPackets.RowRouting

end
end OAI
