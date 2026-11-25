import OAI.Hierarchy.DescentTerminalCableOrder
import OAI.Hierarchy.DescentTerminalDenseGraphRead

namespace OAI
/-! # Actual group slot starts in the single densely paid terminal bit stream -/
namespace Hierarchy.DescentTerminalCableOrder
open Computability.BorderVNP.Crossing DescentTerminalGraphPositions DescentTerminalPorts
open DescentTerminalDenseWindow DescentTerminalDenseGraphRead
open ThreeFlat.Routing
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false

theorem ordered_lt {A : Type} [Fintype A] (key : A ↪ ℕ) (a b : A) :
    ordered key a<ordered key b ↔ key a<key b := by
  let keys:=Finset.univ.image key
  let size : keys.card=Fintype.card A := (Finset.card_image_of_injective _ key.injective).trans (by simp)
  let eqv:=keys.orderIsoOfFin size
  let aa : keys := ⟨key a,Finset.mem_image_of_mem key (Finset.mem_univ a)⟩
  let bb : keys := ⟨key b,Finset.mem_image_of_mem key (Finset.mem_univ b)⟩
  change eqv.symm aa<eqv.symm bb ↔ aa<bb
  exact eqv.symm.lt_iff_lt

theorem sum_before {n : ℕ} (len : Fin n→ℕ) (k : ℕ) (bound : k≤n) :
    pref len k=∑ i : Fin n,if i.val<k then len i else 0 := by
  induction k with
  | zero=>simp [pref]
  | succ k ih=>
    have hk : k<n := by omega
    let t : Fin n:=⟨k,hk⟩
    change pref len k+lengthAt len k=_
    rw [ih hk.le]
    have now : lengthAt len k=∑ i : Fin n,if i=t then len i else 0 := by simp [lengthAt,hk,t]
    rw [now,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases eq : i=t
    · subst i;simp [t]
    · have ne : i.val≠k:=fun h=>eq (Fin.ext h)
      by_cases low : i.val<k <;> simp [eq,low,show i.val<k+1 ↔ i.val<k by omega]

variable {D S p : ℕ} {P : Type} [Fintype P] {bits : P→ℕ} (N : Network D P bits)
    (home : N.Site→Fin S) (native : N.Edge ↪ Fin (Fintype.card N.Edge))
    (external : P ↪ ℕ) (nodes : N.Site ↪ ℕ) (ops : ∀v,DescentKernelHistory.Boundary N v ↪ ℕ)
local notation "L" => order N home native p external nodes ops

def nameWidth : Names N p→ℕ
  | .inl ⟨e,k⟩=>pieceSize p (N.width e) k.val
  | .inr ⟨z,k⟩=>pieceSize p (bits z) k.val

def groupLengths (L' : Order N S p) (i : Fin S) (g : Order.Group L' i) :
    Fin (Fintype.card (Order.At L' i g))→ℕ :=
  fun j=>nameWidth N ((Order.inGroup L' i g).symm j).val

private theorem prior_name_sum (L' : Order N S p) (i : Fin S) (g : Order.Group L' i)
    (nm : Order.At L' i g) (weight : Names N p→ℕ) :
    (∑ t : Fin (Fintype.card (Order.At L' i g)), if t.val<(Order.inGroup L' i g nm).val then
      weight ((Order.inGroup L' i g).symm t).val else 0)=
      ∑ x ∈ Finset.univ.filter (fun x=>Order.Used L' i x ∧ Order.neighbor L' i x=g.val),
        if L'.wireRank x<L'.wireRank nm.val then weight x else 0 := by
  let slots:=Order.inGroup L' i g
  let cost (t : Fin (Fintype.card (Order.At L' i g))) :=
    if t.val<(slots nm).val then weight (slots.symm t).val else 0
  change (∑ t, cost t)=_
  rw [←slots.sum_comp cost]
  rw [Finset.sum_subtype (p:=fun x : Names N p=>Order.Used L' i x ∧ Order.neighbor L' i x=g.val)
    (Finset.univ.filter (fun x : Names N p=>Order.Used L' i x ∧ Order.neighbor L' i x=g.val))
    (by intro x; simp only [Finset.mem_filter,Finset.mem_univ,true_and])
    (fun x=>if L'.wireRank x<L'.wireRank nm.val then weight x else 0)]
  apply Finset.sum_congr rfl
  intro a _
  have cmp : (slots a).val<(slots nm).val ↔ L'.wireRank a.val<L'.wireRank nm.val :=
    ordered_lt ((Function.Embedding.subtype _).trans L'.wireRank : Order.At L' i g ↪ ℕ) a nm
  simp only [cost,cmp,Equiv.symm_apply_apply]

theorem group_sum (L' : Order N S p) (i : Fin S) (g : Order.Group L' i) (nm : Order.At L' i g) :
    pref (groupLengths N L' i g) (Order.inGroup L' i g nm).val=
      ∑ x ∈ Finset.univ.filter (fun x=>Order.Used L' i x ∧ Order.neighbor L' i x=g.val),
        if L'.wireRank x<L'.wireRank nm.val then nameWidth N x else 0 := by
  rw [sum_before _ _ (Order.inGroup L' i g nm).isLt.le]
  exact prior_name_sum N L' i g nm (nameWidth N)

theorem sum_pieces {n k : ℕ} (bound : k≤n) (w : ℕ→ℕ) :
    (∑ j : Fin n, if j.val<k then w j.val else 0)=∑ t ∈ Finset.range k,w t := by
  rw [←sum_before (fun j=>w j.val) k bound,prefix_eq_sum]
  apply Finset.sum_congr rfl
  intro a ha
  exact dite_eq_left ((Finset.mem_range.mp ha).trans_le bound)

theorem sum_piece_sizes (p width : ℕ) (hp : 0<p) :
    (∑ l : Fin (poolBatchCount width p), pieceSize p width l.val)=width := by
  have total := (sum_pieces (Nat.le_refl (poolBatchCount width p)) (pieceWidth width p)).trans
    (whole_cable width p hp)
  simpa only [Fin.is_lt,ite_true,pieceWidth,pieceSize] using total

omit [Fintype P] in
private theorem no_exterior_neighbor (L' : Order N S p) (i j : Fin S) (z : P)
    (l : Fin (poolBatchCount (bits z) p)) :
    ¬(Order.Used L' i (.inr ⟨z,l⟩) ∧ Order.neighbor L' i (.inr ⟨z,l⟩)=some j) := by
  intro h
  have impossible : (none : Option (Fin S))=some j := h.2
  cases impossible

/-- The filtered chunk sum of a native cable equals its whole width when its ordinal is
earlier, the real exclusive bit index when it is the chosen cable, and zero otherwise. -/
private theorem cable_contribution (hp : 0<p) (i j : Fin S) (e f : N.Edge)
    (k : Fin (poolBatchCount (N.width e) p)) (atPair : pairIndex N home e=pair i j) :
    (∑ l : Fin (poolBatchCount (N.width f) p),
      if pairIndex N home f=pair i j then
        (if wireRank N home native p external (.inl ⟨f,l⟩)<wireRank N home native p external (.inl ⟨e,k⟩)
          then nameWidth N (.inl ⟨f,l⟩) else 0) else 0) =
    (if pairIndex N home f=pair i j ∧ native f<native e then N.width f else 0)+
      (if f=e then k.val*p else 0) := by
  by_cases same : f=e
  · subst f
    simp only [slice_lt,lt_self_iff_false,true_and,false_or,and_false,atPair,ite_true,ite_false,zero_add,nameWidth]
    exact (sum_pieces k.isLt.le (pieceWidth (N.width e) p)).trans
      ((piece_before ..).trans (Nat.min_eq_right (piece_used hp k).le))
  · by_cases pairEq : pairIndex N home f=pair i j
    · by_cases rank : native f<native e
      · simp only [slice_lt,edge_lt,pairEq,atPair,lt_self_iff_false,true_and,ite_true,
          rank,or_true,true_or,same,ite_false,Nat.add_zero,nameWidth]
        exact sum_piece_sizes p (N.width f) hp
      · simp [slice_lt,edge_lt,pairEq,atPair,rank,same]
    · simp [pairEq,same]

theorem group_total (hp : 0<p) (i j : Fin S) (g : Order.Group L i) (target : g.val=some j) :
    pref (groupLengths N L i g) (Fintype.card (Order.At L i g))=pairMass N home (pair i j) := by
  rw [sum_before _ _ (le_refl _)]
  simp only [Fin.is_lt,ite_true]
  rw [←(Order.inGroup L i g).sum_comp]
  simp only [groupLengths,Equiv.symm_apply_apply]
  rw [←Finset.sum_subtype (Finset.univ.filter (fun x=>Order.Used L i x ∧ Order.neighbor L i x=g.val))
    (by simp) (nameWidth N)]
  have test (f : N.Edge) (l : Fin (poolBatchCount (N.width f) p)) :
      (Order.Used L i (.inl ⟨f,l⟩) ∧ Order.neighbor L i (.inl ⟨f,l⟩)=some j) ↔
        pairIndex N home f=pair i j := between_iff N p L i j f l
  simp only [target,Finset.sum_filter,Fintype.sum_sum_type,Fintype.sum_sigma,test,
    no_exterior_neighbor N L i j,ite_false,Finset.sum_const_zero,Nat.add_zero]
  unfold pairMass
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro f _
  by_cases same : pairIndex N home f=pair i j
  · simp only [same,ite_true,nameWidth]
    exact sum_piece_sizes p (N.width f) hp
  · simp [same]

theorem group_prefix (hp : 0<p) (i j : Fin S) (g : Order.Group L i) (target : g.val=some j)
    (nm : Order.At L i g) (e : N.Edge) (k : Fin (poolBatchCount (N.width e) p))
    (label : nm.val=.inl ⟨e,k⟩) :
    pairBase N home i j+pref (groupLengths N L i g) (Order.inGroup L i g nm).val=
      ProtocolRAMPortRanks.prefix N.width (edgeCode N home native) e+k.val*p := by
  have own : Order.between L i j (.inl ⟨e,k⟩) := label ▸ ⟨nm.2.1,nm.2.2.trans target⟩
  have atPair : pairIndex N home e=pair i j := (between_iff N p L i j e k).mp own
  rw [edge_start N home native e i j atPair,group_sum]
  simp only [target,label,Finset.sum_filter,Fintype.sum_sum_type,Fintype.sum_sigma]
  have cable (f : N.Edge) (l : Fin (poolBatchCount (N.width f) p)) :
      (Order.Used L i (.inl ⟨f,l⟩) ∧ Order.neighbor L i (.inl ⟨f,l⟩)=some j) ↔
        pairIndex N home f=pair i j := between_iff N p L i j f l
  have rankEq : (L).wireRank=wireRank N home native p external := rfl
  have contribution (f : N.Edge) := cable_contribution N home native external hp i j e f k atPair
  simp only [cable,no_exterior_neighbor N L i j,ite_false,Finset.sum_const_zero,Nat.add_zero,rankEq]
  simp only [contribution,Finset.sum_add_distrib]
  simp [earlierCables,Finset.sum_filter,Nat.add_assoc]

/-- Local route names count pieces. A short final piece consumes one slot. -/
theorem group_rank (L' : Order N S p) (i : Fin S) (g : Order.Group L' i) (nm : Order.At L' i g) :
    (Order.inGroup L' i g nm).val=
      ∑ x ∈ Finset.univ.filter (fun x=>Order.Used L' i x ∧ Order.neighbor L' i x=g.val),
        if L'.wireRank x<L'.wireRank nm.val then 1 else 0 := by
  have lower : (∑t : Fin (Fintype.card (Order.At L' i g)),
      if t.val<(Order.inGroup L' i g nm).val then 1 else 0)=(Order.inGroup L' i g nm).val :=
    (sum_pieces (Order.inGroup L' i g nm).isLt.le (fun _=>1)).trans (by simp)
  exact lower.symm.trans (prior_name_sum N L' i g nm (fun _=>1))

theorem count_units {A : Type} [DecidableEq A] (width : A→ℕ) (rank : A ↪ ℕ)
    (keep : A→Prop) [DecidablePred keep] (e f : A) (t : Fin (width e)) (live : keep e) :
    (∑g : Fin (width f),if keep f then
      (if rank f<rank e ∨ (f=e ∧ g.val<t.val) then 1 else 0) else 0)=
      (if keep f ∧ rank f<rank e then width f else 0)+(if f=e then t.val else 0) := by
  by_cases eq : f=e
  · subst f
    simp only [live,ite_true,lt_self_iff_false,true_and,false_or,and_false,ite_false,zero_add]
    exact (sum_pieces t.isLt.le (fun _=>1)).trans (by simp)
  · by_cases yes : keep f <;> by_cases less : rank f<rank e <;> simp [yes,less,eq]

theorem cable_local_ordinal (i j : Fin S) (g : Order.Group L i) (target : g.val=some j)
    (nm : Order.At L i g) (e : N.Edge) (k : Fin (poolBatchCount (N.width e) p)) (label : nm.val=.inl ⟨e,k⟩) :
    (Order.inGroup L i g nm).val=
      (∑f ∈ Finset.univ.filter (fun f=>pairIndex N home f=pair i j ∧ native f<native e),
        poolBatchCount (N.width f) p)+k.val := by
  have own : Order.between L i j (.inl ⟨e,k⟩) := label ▸ ⟨nm.2.1,nm.2.2.trans target⟩
  have atPair : pairIndex N home e=pair i j := (between_iff N p L i j e k).mp own
  have cable (f : N.Edge) (l : Fin (poolBatchCount (N.width f) p)) :
      (Order.Used L i (.inl ⟨f,l⟩) ∧ Order.neighbor L i (.inl ⟨f,l⟩)=some j) ↔
        pairIndex N home f=pair i j := between_iff N p L i j f l
  have units (f : N.Edge) :
      (∑l : Fin (poolBatchCount (N.width f) p),if pairIndex N home f=pair i j then
        (if wireRank N home native p external (.inl ⟨f,l⟩)<wireRank N home native p external (.inl ⟨e,k⟩)
        then 1 else 0) else 0)=
        (if pairIndex N home f=pair i j ∧ native f<native e then poolBatchCount (N.width f) p else 0)+
        (if f=e then k.val else 0) := by
    have cmp (u v : N.Edge) :
        (native.trans Fin.valEmbedding) u<(native.trans Fin.valEmbedding) v ↔ native u<native v := Iff.rfl
    by_cases good : pairIndex N home f=pair i j
    · simpa only [slice_lt,edge_lt,good,atPair,cmp,lt_self_iff_false,or_false,false_or,true_and,ite_true]
        using count_units (fun f=>poolBatchCount (N.width f) p) (native.trans Fin.valEmbedding)
          (fun f=>pairIndex N home f=pair i j) e f k atPair
    · simp [good,show f≠e from fun h=>good (h ▸ atPair)]
  have absent (a : P) (l : Fin (poolBatchCount (bits a) p)) :
      ¬(Order.Used L i (.inr ⟨a,l⟩) ∧ Order.neighbor L i (.inr ⟨a,l⟩)=some j) := by
    intro h
    have impossible : (none : Option (Fin S))=some j := h.2
    cases impossible
  have rankEq : (L).wireRank=wireRank N home native p external := rfl
  rw [group_rank]
  simp only [target,label,Finset.sum_filter,Fintype.sum_sum_type,Fintype.sum_sigma,cable,absent,
    ite_false,Finset.sum_const_zero,Nat.add_zero,rankEq]
  simp only [units,Finset.sum_add_distrib]
  simp

theorem exterior_local_ordinal (i : Fin S) (g : Order.Group L i) (target : g.val=none)
    (nm : Order.At L i g) (e : P) (k : Fin (poolBatchCount (bits e) p)) (label : nm.val=.inr ⟨e,k⟩) :
    (Order.inGroup L i g nm).val=
      (∑f ∈ Finset.univ.filter (fun f=>home (N.attach f)=i ∧ external f<external e),
        poolBatchCount (bits f) p)+k.val := by
  have used: Order.Used L i (.inr ⟨e,k⟩):=label ▸ nm.2.1
  have atSite:home (N.attach e)=i:=(Order.used_port L i e k).mp used
  have cmp (f : P) (l : Fin (poolBatchCount (bits f) p)) :
      wireRank N home native p external (.inr ⟨f,l⟩)<wireRank N home native p external (.inr ⟨e,k⟩) ↔
      external f<external e ∨ (f=e ∧ l.val<k.val) := by
    change 2*_+1<2*_+1 ↔ _
    rw [Nat.add_lt_add_iff_right,Nat.mul_lt_mul_left (by decide : 0<2),
      digit_lt (pin_piece_room N p f l) (pin_piece_room N p e k),external.injective.eq_iff]
  have absent (f : N.Edge) (l : Fin (poolBatchCount (N.width f) p)) :
      ¬(Order.Used L i (.inl ⟨f,l⟩) ∧ Order.neighbor L i (.inl ⟨f,l⟩)=none) := by
    intro h
    have impossible : some (if home (N.src f)=i then home (N.dst f) else home (N.src f))=none := h.2
    cases impossible
  have pin (f : P) (l : Fin (poolBatchCount (bits f) p)) :
      (Order.Used L i (.inr ⟨f,l⟩) ∧ Order.neighbor L i (.inr ⟨f,l⟩)=none) ↔ home (N.attach f)=i :=
    ⟨fun h=>(Order.used_port L i f l).mp h.1,fun h=>⟨(Order.used_port L i f l).mpr h,rfl⟩⟩
  have units (f : P) :
      (∑l : Fin (poolBatchCount (bits f) p),if home (N.attach f)=i then
        (if external f<external e ∨ (f=e ∧ l.val<k.val) then 1 else 0) else 0)=
        (if home (N.attach f)=i ∧ external f<external e then poolBatchCount (bits f) p else 0)+
          (if f=e then k.val else 0) :=
    count_units (fun f=>poolBatchCount (bits f) p) external (fun f=>home (N.attach f)=i) e f k atSite
  have rankEq : (L).wireRank=wireRank N home native p external := rfl
  rw [group_rank]
  simp only [target,label,Finset.sum_filter,Fintype.sum_sum_type,Fintype.sum_sigma,absent,pin,
    ite_false,Finset.sum_const_zero,Nat.zero_add,rankEq,cmp]
  simp only [units,Finset.sum_add_distrib]
  simp

theorem partner_prefix (hp : 0<p) (i j : Fin S) (g : Order.Group L i) (target : g.val=some j)
    (nm : Order.At L i g) (e : N.Edge) (k : Fin (poolBatchCount (N.width e) p))
    (label : nm.val=.inl ⟨e,k⟩) :
    let g':=Order.partner L g target
    let nm':=Order.transfer L g target nm
    pairBase N home i j+pref (groupLengths N L i g) (Order.inGroup L i g nm).val=
      pairBase N home j i+pref (groupLengths N L j g') (Order.inGroup L j g' nm').val := by
  dsimp only
  exact (group_prefix N home native external nodes ops hp i j g target nm e k label).trans
    (group_prefix N home native external nodes ops hp j i _ (Order.partner_val L g target)
      (Order.transfer L g target nm) e k label).symm

theorem cable_slot_address (hp : 0<p) {q : ℕ} (i j : Fin S) (g : Order.Group L i) (target : g.val=some j)
    (r : ℕ) (s : Fin q) (e : N.Edge) (k : Fin (poolBatchCount (N.width e) p))
    (hit : r*q+s.val<Fintype.card (Order.At L i g))
    (label : ((Order.inGroup L i g).symm ⟨r*q+s.val,hit⟩).val=.inl ⟨e,k⟩) :
    DescentTerminalDenseWindow.begin (groupLengths N L i g) q (pairBase N home i j) r s =
      ProtocolRAMPortRanks.prefix N.width (edgeCode N home native) e+k.val*p ∧
    lengthAt (groupLengths N L i g) (r*q+s.val)=pieceSize p (N.width e) k.val := by
  refine ⟨?_,?_⟩
  · simpa only [DescentTerminalDenseWindow.begin,Equiv.apply_symm_apply] using
      group_prefix N home native external nodes ops hp i j g target _ e k label
  · simp [lengthAt,hit,groupLengths,label,nameWidth]


end
end Hierarchy.DescentTerminalCableOrder

end OAI
