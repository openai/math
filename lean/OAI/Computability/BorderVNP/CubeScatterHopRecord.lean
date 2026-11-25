import OAI.Computability.BorderVNP.TransmissionAssignedPayload

/-! # Inverting a physical relay hop to its nonlocal source record -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open Routing

private theorem pairKey_eq_ends (tab : TableLayout) {a b c d : ℕ}
    (ha : a < tab.teams) (hb : b < tab.teams) (hc : c < tab.teams) (hd : d < tab.teams)
    (key : tab.pairKey a b = tab.pairKey c d) : (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  let x : Fin tab.teams × Fin tab.teams := (⟨min a b,(min_le_left ..).trans_lt ha⟩,⟨max a b,max_lt ha hb⟩)
  let y : Fin tab.teams × Fin tab.teams := (⟨min c d,(min_le_left ..).trans_lt hc⟩,⟨max c d,max_lt hc hd⟩)
  have eqn : finProdFinEquiv x = finProdFinEquiv y := by
    apply Fin.ext
    change max a b+tab.teams*min a b = max c d+tab.teams*min c d
    simpa only [TableLayout.pairKey,Nat.add_comm,Nat.mul_comm] using key
  have same := finProdFinEquiv.injective eqn
  have lo : min a b = min c d := congrArg (fun z : Fin tab.teams × Fin tab.teams => z.1.val) same
  have hi : max a b = max c d := congrArg (fun z : Fin tab.teams × Fin tab.teams => z.2.val) same
  omega

/-- Every hop recovers its actual descriptor, its interior bit offset, both endpoints
up to orientation and its assigned data bit from the packed unordered list. -/
theorem TableLayout.hop_record {w N : ℕ} {hR : 2 < N} {width : Fin N → Fin N → ℕ} {u v : Fin N}
    (tab : TableLayout) (row : ℕ → TableRow) (fit : tab.RowsFit w row) (teams : N = tab.teams)
    (widthEq : width = Transmission.tableWidth tab row teams) (value : Fin tab.count → ℕ → Bool)
    (p : Hop hR width u v) :
    ∃ (i : Fin tab.count) (j : ℕ), j < (row i).width ∧ tab.ordinal row i+j = p.2.val ∧
      (((row i).first = u.val ∧ (row i).second = p.1.val) ∨
        ((row i).first = p.1.val ∧ (row i).second = u.val)) ∧
      tab.recordPayload row value (min u p.1) (max u p.1) p.2.val = value i j := by
  have hp : p.2.val ∈ pairBits hR u p.1 v (demand width u p.1) := p.2.property
  have ne : u ≠ p.1 := by
    rintro he
    simp only [pairBits,dite_eq_right (not_ne_iff.mpr he),Finset.notMem_empty] at hp
  simp only [pairBits,dite_eq_left ne] at hp
  have bound : p.2.val < demand width u p.1 := Finset.mem_range.mp (Finset.mem_filter.mp hp).1
  simp only [demand,ite_eq_right ne,widthEq] at bound
  let key := tab.pairKey u.val p.1.val
  have hq : p.2.val < tab.pairWidth row tab.count key := bound
  let e := tab.recordBitsEquiv row key
  let x := e.symm ⟨p.2.val,hq⟩
  obtain ⟨_,hk,inside⟩ := x.property
  have ordinal : tab.ordinal row x.val.1+x.val.2 = p.2.val := congrArg Fin.val (e.apply_symm_apply _)
  obtain ⟨_,first,second⟩ := fit.labels x.val.1 x.val.1.isLt
  have ends := pairKey_eq_ends tab first second (teams ▸ u.isLt) (teams ▸ p.1.isLt) hk
  refine ⟨x.val.1,x.val.2,inside,ordinal,ends,?_⟩
  rw [← ordinal]
  rcases ends with h | h
  · exact tab.recordPayload_eq row value u p.1 ne _ h.1 h.2 _ inside
  · simpa only [min_comm p.1 u,max_comm p.1 u] using
      tab.recordPayload_eq row value p.1 u ne.symm _ h.1 h.2 _ inside

end RoutingISA

end BorderVNP
end Computability
end OAI
