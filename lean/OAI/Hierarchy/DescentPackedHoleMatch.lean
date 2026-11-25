import OAI.Hierarchy.DescentPositiveAperture
import OAI.Hierarchy.DescentPackedLocalMatchSource
import Mathlib.Data.List.Forall2

namespace OAI
/-! # Exact dense matching using geometrical padded destination slots -/

noncomputable section
namespace Hierarchy.DescentPacking.PackedLocalMatch.Holes
open PositiveAperture
open scoped Classical BigOperators
variable {C I : Type*} [Fintype C] [DecidableEq C] {n b : ℕ}
variable (f : I→ℕ) (xs : List I) (orig : C→ℕ) (cap : Fin b→ℕ)
variable (M : PositiveAperture.Map orig (cap ∘ position b)) (fits : xs.length≤n)
local notation "old" => Packing.decisions (pack f xs orig)
local notation "geom" => Packing.decisions (pack f xs (cap ∘ position b))
local notation "num" => Packing.decisions (packing (needs (n:=n) f xs) cap)

private theorem original_length : (old).length=xs.length := by
  simpa using congrArg List.length (pack f xs orig).order

include fits in
private theorem correspondence (i : Fin (num).length) (j : Fin (old).length) (eqn : i.val=j.val) :
    ((num).get i).1=f ((old).get j).1 ∧
    (0<f ((old).get j).1→M.Hit ((old).get j).2 ((num).get i).2) := by
  let l := M.allocated f xs
  let p : Fin (geom).length := ⟨j.val,j.isLt.trans_eq l.length_eq⟩
  have related : M.Row f ((old).get j) ((geom).get p) := l.get (i:=j.val) j.isLt p.isLt
  have t : ∃tail,num=(geom).map (written f)++tail := by
    unfold packing
    rw [needs_fit f xs fits,pack_append,map_amount]
    exact ⟨_,rfl⟩
  obtain ⟨tail,split⟩ := t
  have h := congrArg (fun ys : List (ℕ×Option (Fin b))=>ys[i.val]?) split
  have use : i.val<(geom).length := eqn ▸ p.isLt
  have le : i.val<((geom).map (written f)).length := by simpa using use
  have numeric : (num).get i=written f ((geom).get p) := by
    have pp : (⟨i.val,use⟩:Fin (geom).length)=p := Fin.ext eqn
    rw [←pp]
    simpa only [List.getElem?_append_left le,List.getElem?_map,List.getElem?_eq_getElem i.isLt,
      List.getElem?_eq_getElem use,Option.map_some,Option.some.injEq,List.get_eq_getElem] using h
  refine ⟨(congrArg Prod.fst numeric).trans (congrArg f related.1.symm),?_⟩
  rw [numeric]
  exact related.2

omit [DecidableEq C] in
private theorem selected (c : {v//0<orig v}) {p : Option C} {q : Option (Fin b)} (rel : M.Hit p q) :
    (p=some c.val ↔ q=some (M.dest c).val) ∧ (p.isSome=q.isSome) := by
  rcases rel with ⟨rfl,rfl⟩|⟨x,rfl,rfl⟩
  · simp
  · simp only [Option.some.injEq,Option.isSome_some,and_true]
    exact ⟨fun h=>congrArg Subtype.val (congrArg M.dest (Subtype.ext h)),
      fun h=>congrArg Subtype.val (M.dest.injective (Subtype.ext h))⟩

omit [DecidableEq C] in
theorem «prefix» (c : {v//0<orig v}) :
    ProtocolRAMPortRanks.«prefix» cap Fin.val (position b (M.dest c).val) =
      ProtocolRAMPortRanks.«prefix» orig rank c.val := by
  unfold ProtocolRAMPortRanks.«prefix»
  symm
  apply Finset.sum_bij_ne_zero
    (fun v _ live=>position b (M.dest ⟨v,Nat.pos_of_ne_zero live⟩).val)
  · intro v h live
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(M.order ⟨v,_⟩ c).mp (Finset.mem_filter.mp h).2⟩
  · intro v hv pv u hu pu eqn
    exact congrArg Subtype.val (M.dest.injective (Subtype.ext ((position b).injective eqn)))
  · intro p hp live
    let v := (position b).symm p
    let u : {x // 0 < (cap ∘ position b) x} := ⟨v,by simpa [v] using Nat.pos_of_ne_zero live⟩
    let x := M.dest.symm u
    have hx : (M.dest x).val=v := congrArg Subtype.val (M.dest.apply_symm_apply u)
    have before : rank (M.dest x).val<rank (M.dest c).val := by
      change (position b (M.dest x).val).val<(position b (M.dest c).val).val
      rw [hx]
      simpa only [v,Equiv.apply_symm_apply] using (Finset.mem_filter.mp hp).2
    exact ⟨x.val,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(M.order x c).mpr before⟩,
      x.property.ne',by rw [show (M.dest ⟨x.val,_⟩).val=v from hx];simp [v]⟩
  · intro v _ live
    exact (M.mass ⟨v,Nat.pos_of_ne_zero live⟩).symm

include fits in
/-- Input and old record sums agree through every live old position, ignoring
the names selected by zero-amount items in either directory. -/
private theorem before {a : ℕ} (small : a≤(old).length) (p : Option C→Bool) (q : Option (Fin b)→Bool)
    (aligned : ∀ x y,M.Hit x y→p x=q y) :
    (∑i : Fin (num).length,if i.val<a ∧ q ((num).get i).2 then ((num).get i).1 else 0)=
      ∑i : Fin (old).length,if i.val<a ∧ p ((old).get i).2 then f ((old).get i).1 else 0 := by
  have huge : a≤(num).length := (small.trans ((original_length f xs orig).le.trans fits)).trans_eq (length _ _).symm
  simp_rw [ite_and]
  apply prefix_sum huge small
  intro i
  let l : Fin (num).length := ⟨i.val,i.isLt.trans_le huge⟩
  let r : Fin (old).length := ⟨i.val,i.isLt.trans_le small⟩
  have rel := correspondence f xs orig cap M fits l r rfl
  change (if q ((num).get l).2 then ((num).get l).1 else 0)=(if p ((old).get r).2 then f ((old).get r).1 else 0)
  rw [rel.1]
  by_cases zero : f ((old).get r).1=0
  · simp only [zero, ite_self]
  · rw [aligned _ _ (rel.2 (Nat.pos_of_ne_zero zero))]

include fits in
theorem dense (e : Pairs f old) {limit : ℕ} (bound : e.2.2.val<limit) :
    ∃c : {v//0<orig v},c.val=e.1 ∧ ∃r : Record,
      PackedLocalMatch.dense (needs (n:=n) f xs) cap limit (pairNumber f old e).val=some r ∧
      r.accepted=(pairNumber f old e).val ∧ r.bin=(position b (M.dest c).val).val ∧
      r.thin=(∑i : Locations old,if i.val<e.2.1.val.val then f ((old).get i).1 else 0)+e.2.2.val ∧
      r.thick=ProtocolRAMPortRanks.«prefix» orig rank e.1+(thickEnd (pack f xs orig) e).2.val := by
  let t := e.2.1.val
  have small := t.isLt.trans_le ((original_length f xs orig).le.trans fits)
  let j : Fin (num).length := ⟨t.val,small.trans_eq (length _ _).symm⟩
  have row := correspondence f xs orig cap M fits j t rfl
  have pos : 0<f ((old).get t).1 := Nat.zero_lt_of_lt e.2.2.isLt
  rcases row.2 pos with ⟨no,_⟩|⟨c,src,dst⟩
  · have impossible : some e.1 = none := e.2.1.property.symm.trans no
    cases impossible
  have named := Option.some.inj (src.symm.trans e.2.1.property)
  let z : Unit (needs (n:=n) f xs) cap := ⟨(M.dest c).val,⟨j,dst⟩,⟨e.2.2.val,e.2.2.isLt.trans_eq row.1.symm⟩⟩
  let d := fields (needs (n:=n) f xs) cap z
  have order : d.accepted=(pairNumber f old e).val := by
    change (pairNumber id num z).val=_
    rw [pairNumber_prefix,pairNumber_prefix]
    exact congrArg (·+e.2.2.val) (before f xs orig cap M fits t.isLt.le Option.isSome Option.isSome
      (fun _ _ rel=>(selected orig cap M c rel).2))
  have readback : PackedLocalMatch.dense (needs (n:=n) f xs) cap limit d.accepted = some d :=
    PackedLocalMatch.dense_at (limit:=limit) (needs (n:=n) f xs) cap z bound
  rw [order] at readback
  refine ⟨c,named,d,readback,order,rfl,?_,?_⟩
  · change ProtocolRAMPortRanks.«prefix» _ Fin.val _+_=_
    apply congrArg (·+e.2.2.val)
    unfold ProtocolRAMPortRanks.«prefix»
    rw [Finset.sum_filter]
    apply prefix_sum small.le t.isLt.le
    intro i
    let l : Fin (num).length := ⟨i.val,i.isLt.trans_le j.isLt.le⟩
    let r : Fin (old).length := ⟨i.val,i.isLt.trans_le t.isLt.le⟩
    exact (amount_at _ _ l).symm.trans (correspondence f xs orig cap M fits l r rfl).1
  · change ProtocolRAMPortRanks.«prefix» _ _ _+(thickEnd (packing _ _) z).2.val=_+_
    have prefix_eq := («prefix» orig cap M c).trans
      (congrArg (ProtocolRAMPortRanks.«prefix» orig rank) named)
    rw [prefix_eq]
    apply congrArg (_+·)
    rw [thickEnd_prefix,thickEnd_prefix]
    apply congrArg (·+e.2.2.val)
    simp_rw [ite_and]
    apply prefix_sum j.isLt.le t.isLt.le
    intro i
    let l : Fin (num).length := ⟨i.val, i.isLt.trans_le j.isLt.le⟩
    let r : Fin (old).length := ⟨i.val, i.isLt.trans_le t.isLt.le⟩
    have rel := correspondence f xs orig cap M fits l r rfl
    change (if ((num).get l).2 = some (M.dest c).val then ((num).get l).1 else 0) =
      (if ((old).get r).2 = some e.1 then f ((old).get r).1 else 0)
    rw [rel.1]
    by_cases zero : f ((old).get r).1 = 0
    · simp only [zero, ite_self]
    · have hit := (selected orig cap M c (rel.2 (Nat.pos_of_ne_zero zero))).1
      have equal : ((old).get r).2 = some e.1 ↔ ((num).get l).2 = some (M.dest c).val := by
        simpa only [named] using hit
      by_cases chosen : ((old).get r).2 = some e.1
      · rw [ite_eq_left (equal.mp chosen), ite_eq_left chosen]
      · rw [ite_eq_right (fun h => chosen (equal.mpr h)), ite_eq_right chosen]

include M fits in
theorem count : Fintype.card (Unit (needs (n:=n) f xs) cap)=Fintype.card (Pairs f old) := by
  rw [accepted_total,accepted_total]
  let t := (old).length
  have equality := before f xs orig cap M fits (a:=t) le_rfl Option.isSome Option.isSome (by
    rintro _ _ (⟨rfl,rfl⟩|⟨c,rfl,rfl⟩) <;> rfl)
  refine Eq.trans ?_ (equality.trans ?_)
  · apply Finset.sum_congr rfl
    intro i _
    by_cases h : i.val<t
    · simp [h]
    · have zero : ((num).get i).1=0 := (amount_at _ _ _).trans (by
        have off : xs.length≤ i.val := by simpa only [t,original_length f xs orig] using Nat.le_of_not_gt h
        simp [needs,index,List.getElem?_eq_none off])
      simp only [id_eq, zero, ite_self]
  · apply Finset.sum_congr rfl
    intro i _
    simp [show i.val<t from i.isLt]

end Hierarchy.DescentPacking.PackedLocalMatch.Holes

end
end OAI
