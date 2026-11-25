import OAI.Hierarchy.DescentDonorShape
import OAI.Hierarchy.DescentPackedDonorPrimitives

namespace OAI
/-! # The eight supply widths from the funded per-leaf topology and birth words -/
namespace Hierarchy.DescentRawCablePanel.DepotRAM.Fresh
open DescentSIMDLookup DescentPacking.PackedMatch DescentPacking.PackedMatch.Local DescentOrdinaryAtomFieldRAM
open scoped BigOperators Classical Fin.CommRing
noncomputable section

variable {H G M K : ℕ} (s : DepotRAM.Shape) (z : DescentPacking.PackedMatch.Shape)

abbrev Slots (s : DepotRAM.Shape) := Fin ((s.blocks*s.cap)*8)
def decodeSlot (j : Slots s) : (Fin s.blocks×Fin s.cap)×Fin 8 :=
  let p:=finProdFinEquiv.symm j
  (finProdFinEquiv.symm p.1,p.2)

def unpack (c : Cell (rawBits s)) : Panel s.blocks s.degree (2*s.cap) s.short :=
  decodePanel (finProdFinEquiv.symm (finCongr (pow_add 2 1 _) c)).2

@[simp] theorem unpack_register (l : Bool) (u : Panel s.blocks s.degree (2*s.cap) s.short) :
    unpack s (Owners.register l u)=u := by simp [unpack,Owners.register]

def cell (B prof C pad scale key : ℕ) (u : Panel s.blocks s.degree (2*s.cap) s.short)
    (top : Cell (SixBirths.topology z M)) (born : Cell (SixBirths.width z M)) (l : Fin M) (j : Slots s) : Cell s.widths :=
  let a:=decodeSlot s j
  if leaf (u.winner a.1.1).val=key ∧ (Stage.query B prof u a.1.1 a.1.2.val true).isSome then
    word s.widths (digit s.widths l.val (bornField z M scale (Stage.branchDigit s.widths C pad a.2)
      (word z.digit (a.1.1.val*(2*s.cap)+a.1.2.val)) 0 top born).val)
  else 0

def keyed (B prof C pad scale key live : ℕ) (panel : Cell (rawBits s*M))
    (top : Cell (SixBirths.topology z M)) (born : Cell (SixBirths.width z M)) : ℕ :=
  ∑l : Fin M,(if l.val<live then (∑j : Slots s,
    (cell s z B prof C pad scale key (unpack s ((encode (rawBits s) M).symm panel l)) top born l j).val*(2^s.widths)^j.val) else 0)*
    (2^(freshBits s))^l.val

def physicalIndex (key : Fin K) (p : Row H G M) : Fin ((K*H)*chunks G M) :=
  row (K*H) G M (finProdFinEquiv (key,p.1),p.2)

private theorem field_at {a : ℕ} (field : Fin H → Fin G → Cell a)
    (p : Row H G M) (l : Fin M) (active : p.2.val*M+l.val<G) :
    (encode a M).symm (data field p) l = field p.1 ⟨_,active⟩ := by
  unfold data
  rw [Equiv.symm_apply_apply]
  exact dite_eq_left active

private theorem index_at (hm : 0<M) (p : Row H G M) (j : Fin M) (bound : p.2.val*M+j.val<G) (key : Fin K) :
    row (K*H) G M (position (finProdFinEquiv (key,p.1)) (⟨p.2.val*M+j.val,bound⟩:Fin G) hm)=physicalIndex key p ∧
      lane (⟨p.2.val*M+j.val,bound⟩:Fin G) hm=j := by
  constructor
  · unfold physicalIndex
    apply congrArg (row (K*H) G M)
    apply Prod.ext
    · rfl
    · apply Fin.ext
      change (p.2.val*M+j.val)/M = p.2.val
      rw [Nat.mul_comm p.2.val M,Nat.mul_add_div hm,Nat.div_eq_of_lt j.isLt,Nat.add_zero]
  · apply Fin.ext
    simp [lane,Nat.add_mod,Nat.mod_eq_of_lt j.isLt]

def tile (B prof C pad scale : ℕ) (hm : 0<M) (u : Fin H→Fin G→Panel s.blocks s.degree (2*s.cap) s.short)
    (top : Fin ((K*H)*chunks G M)→Cell (SixBirths.topology z M))
    (born : Fin ((K*H)*chunks G M)→Cell (SixBirths.width z M)) (h : Fin H) (g : Fin G) : Cell (freshBits s) :=
  encode s.widths _ (fun j=>let a:=decodeSlot s j
    Stage.numericSupply z B prof s.widths C pad scale hm (u h g) h g a.1.1 a.1.2 K top born a.2)

theorem digits (B prof C pad scale : ℕ) (hm : 0<M) (u : Fin H→Fin G→Panel s.blocks s.degree (2*s.cap) s.short)
    (layout : Fin H→Fin G→Bool) (top : Fin ((K*H)*chunks G M)→Cell (SixBirths.topology z M))
    (born : Fin ((K*H)*chunks G M)→Cell (SixBirths.width z M)) (p : Row H G M) :
    (∑q : Fin K,keyed s z B prof C pad scale q.val (used G M p.2.val)
      (data (fun h g=>Owners.register (layout h g) (u h g)) p) (top (physicalIndex q p)) (born (physicalIndex q p)))=
    (data (tile s z B prof C pad scale hm u top born) p).val := by
  classical
  unfold keyed
  rw [Finset.sum_comm]
  change _=∑l : Fin M,(if yes : p.2.val*M+l.val<G then
    tile s z B prof C pad scale hm u top born p.1 ⟨_,yes⟩ else 0).val*(2^(freshBits s))^l.val
  apply Finset.sum_congr rfl
  intro l _
  rw [←Finset.sum_mul]
  by_cases active : p.2.val*M+l.val<G
  · let g : Fin G:=⟨_,active⟩
    have live : l.val<used G M p.2.val:=by unfold used;have:=l.isLt;omega
    have panelAt : unpack s ((encode (rawBits s) M).symm
        (data (fun h g=>Owners.register (layout h g) (u h g)) p) l) = u p.1 g := by
      exact (congrArg (unpack s) (field_at (a:=rawBits s)
        (fun h g=>Owners.register (layout h g) (u h g)) p l active)).trans
        (unpack_register s _ _)
    simp only [ite_eq_left live,dite_eq_left active,panelAt]
    congr 1
    unfold tile
    change _=∑j : Slots s,(Stage.numericSupply z B prof s.widths C pad scale hm (u p.1 g) p.1 g
      (decodeSlot s j).1.1 (decodeSlot s j).1.2 K top born (decodeSlot s j).2).val*(2^s.widths)^j.val
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [←Finset.sum_mul]
    congr 1
    let a:=decodeSlot s j
    let α:=leaf ((u p.1 g).winner a.1.1).val
    by_cases legal : α<K
    · let q : Fin K:=⟨α,legal⟩
      rw [Finset.sum_eq_single q]
      · have read:=index_at hm p l active q
        simp [cell,Stage.numericSupply,a,α,q,g,legal,read.1,read.2]
      · intro i _ ne
        have distinct : α≠i.val:=fun h=>ne (Fin.ext h.symm)
        simp [cell,a,α,distinct]
      · simp
    · have allZero (q : Fin K) : α≠q.val:=fun h=>legal (h.trans_lt q.isLt)
      simp [cell,Stage.numericSupply,a,α,legal,allZero]
  · have usedUp : ¬l.val<used G M p.2.val:=by unfold used;omega
    simp [active,usedUp]

end
end Hierarchy.DescentRawCablePanel.DepotRAM.Fresh

end OAI
