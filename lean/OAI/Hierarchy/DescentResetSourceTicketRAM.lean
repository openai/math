import OAI.Hierarchy.DescentResetSourceFields
import OAI.Hierarchy.DescentIssuedGoodHeaders

namespace OAI
/-! # Computing the raw incidence prefix at an installed reset cable's source -/
namespace Hierarchy.DescentResetSourceTicketRAM
open DescentSIMDLookup DescentPackedZip DescentPacking.PackedMatch.Local.Gather DescentPackedFallbackTree.Image
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {K bits H G M w : ℕ}

def ticket (cap : ℕ) (query : Fin K) (x : Fields K bits) : Cell (ProtocolRAMPurchaseSampler.bits cap) :=
  ((∑j,fee x query j : ℕ):Cell (ProtocolRAMPurchaseSampler.bits cap))

/-- The compact roster may contain unrelated rows. Every positive parent
incident at this host has one slot. Slots outside the active image either
carry zero mass or refer to a different host. The original ordering only
needs to agree on comparisons at this host. -/
theorem ticket_sum {E : Type} [Fintype E] (_cap : ℕ) (query : Fin K) (x : Fields K bits)
    (whereAt : E→Prop) (ordinal mass : E→ℕ) (target : E)
    (slot : {e : E // 0< mass e ∧ whereAt e} ↪ Fin K)
    (present : ∀e,field x (slot e) 0=field x query 0 ∨ field x (slot e) 1=field x query 0)
    (before : ∀e,field x (slot e) 2<field x query 2 ↔ ordinal e.val<ordinal target)
    (weight : ∀e,field x (slot e) 3=mass e.val)
    (other : ∀j,(∀e,slot e≠j)→
      field x j 3=0 ∨ (field x j 0≠field x query 0 ∧ field x j 1≠field x query 0))
    : (∑a,fee x query a)=∑e,if whereAt e ∧ ordinal e<ordinal target then mass e else 0 := by
  classical
  let pay (e : E):=if whereAt e ∧ ordinal e<ordinal target then mass e else 0
  have window : (∑j,fee x query j) = ∑j∈Finset.univ.map slot,fee x query j := by
    apply (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro j _ miss
    have none : ∀e,slot e≠j:=fun e eqn=>miss (Finset.mem_map.mpr ⟨e,Finset.mem_univ _,eqn⟩)
    rcases other j none with zero|⟨src,dst⟩
    · simp [fee,zero]
    · simp [fee,src,dst]
  rw [Finset.sum_map] at window
  have charges (e : {e : E // 0< mass e ∧ whereAt e}) : fee x query (slot e)=pay e.val := by
    simp [fee,present,before,weight,pay,e.property.2]
  simp only [charges] at window
  have base : (∑e : {e : E // 0< mass e ∧ whereAt e},pay e.val)=∑e,pay e := by
    rw [←Fintype.sum_subtype_add_sum_subtype (fun e=>0< mass e ∧ whereAt e) pay]
    have zero : (∑e : {e : E // ¬(0< mass e ∧ whereAt e)},pay e.val)=0:=by
      apply Finset.sum_eq_zero
      intro e _
      by_cases yes : whereAt e.val
      · have absent : mass e.val=0:=Nat.eq_zero_of_not_pos (fun hp=>e.property ⟨hp,yes⟩)
        simp [pay,absent]
      · simp [pay,yes]
    rw [zero,Nat.add_zero]
  exact window.trans base

theorem ticket_read {E : Type} [Fintype E] (cap : ℕ) (query : Fin K) (x : Fields K bits)
    (whereAt : E→Prop) (ordinal mass : E→ℕ) (target : E)
    (slot : {e : E // 0< mass e ∧ whereAt e} ↪ Fin K)
    (present : ∀e,field x (slot e) 0=field x query 0 ∨ field x (slot e) 1=field x query 0)
    (before : ∀e,field x (slot e) 2<field x query 2 ↔ ordinal e.val<ordinal target)
    (weight : ∀e,field x (slot e) 3=mass e.val)
    (other : ∀j,(∀e,slot e≠j)→
      field x j 3=0 ∨ (field x j 0≠field x query 0 ∧ field x j 1≠field x query 0))
    (small : (∑e,if whereAt e ∧ ordinal e<ordinal target then mass e else 0)≤cap) :
    (ticket cap query x).val=∑e,if whereAt e ∧ ordinal e<ordinal target then mass e else 0 := by
  have total:=ticket_sum cap query x whereAt ordinal mass target slot present before weight other
  change (∑j,fee x query j) % 2^(ProtocolRAMPurchaseSampler.bits cap)=_
  rw [total]
  exact Nat.mod_eq_of_lt (small.trans_lt (ProtocolRAMPurchaseSampler.lt_span cap))


theorem run (cap : ℕ) (query : Fin K)
    (tables : Fin (K*4)→Tables) (reads : Fin (K*4)→Expr) (menu : DescentSIMDLookup.Banks)
    (mid out : ℕ) (x : Fin H→Fin G→Fields K bits) (positive : 0<M)
    (mem : Memory w) (bounds : Bounds (w:=w) (d:=bits) (M:=M) tables reads mid)
    (constants : ∀j,Static (tables j) (setField (d:=bits) j) M mem)
    (sources : ∀j,Source (reads j) (fun a g=>x a g j) M mem) (room : mid+H*chunks G M<2^w)
    (fit : DescentSIMDLookup.Fits menu (bits*(K*4)) (ProtocolRAMPurchaseSampler.bits cap) M H G w out)
    (rom : resident (ticket cap query ∘ (encode bits (K*4)).symm) menu H G M mem)
    (dictLow : menu.dictionary.base+2^((bits*(K*4))*M)≤ mid) (maskLow : menu.mask.base+H*chunks G M≤ mid)
    (wire : menu.source.base=mid) :
    let act:=assembly tables reads
    let rows:=H*chunks G M
    let dst:=imageBank H G M out menu (image mid rows act mem)
    ((scan w mid rows act).seq (DescentSIMDLookup.program menu out H G M w)).Exec mem dst
      ((4+rows*(2*act.work+4))+(4+44*rows)) ∧
    (∀a g,digit (ProtocolRAMPurchaseSampler.bits cap) (lane g positive).val (dst (out+(row H G M (position a g positive)).val)).val=(ticket cap query (x a g)).val) ∧
    ∀addr,(addr< mid ∨ mid+rows≤addr)→(addr<out ∨ out+rows≤addr)→dst addr=mem addr :=
  DescentIssuedGoodHeaders.gathered (ticket cap query) tables reads menu mid out x positive
    mem bounds constants sources room fit rom dictLow maskLow wire

end
end Hierarchy.DescentResetSourceTicketRAM

end OAI
