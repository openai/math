import OAI.Hierarchy.DescentPackedLocalMatch
import OAI.Hierarchy.DescentSparseRowMap
import OAI.Hierarchy.DescentPackSelectionCounters

namespace OAI
/-! # Reading the bounded local match table on the actual ordered source packs -/

noncomputable section
namespace Hierarchy.DescentPacking.PackedLocalMatch
open SparseBinRAM
open scoped BigOperators Classical
variable {C I : Type*} [Fintype C] [DecidableEq C] {M n : ℕ} {S : Finset C}

/-- Physical numeric aperture field, after the public ordinal reindexing in the RAM. -/
def capacities (A : Aperture S M) (cap : C→ℕ) (i : Fin M) := A.mass cap ((position M).symm i)

def needs (amount : I→ℕ) (xs : List I) (i : Fin n) := (xs[i.val]?.map amount).getD 0

theorem needs_fit (amount : I→ℕ) (xs : List I) (h : xs.length≤n) :
    List.ofFn (needs (n:=n) amount xs) = xs.map amount ++ List.replicate (n-xs.length) 0 := by
  apply List.ext_getElem
  · simp;omega
  · intro i hi hj
    by_cases live : i<xs.length
    · rw [List.getElem_append_left (by simpa using live)]
      simp [needs,List.getElem?_eq_getElem live]
    · rw [List.getElem_append_right (by simpa using Nat.le_of_not_gt live)]
      simp [needs,List.getElem?_eq_none (Nat.le_of_not_gt live)]

def written {B : Type*} (f : I→ℕ) (r : I×Option B) := (f r.1,r.2)

theorem map_amount {B : Type*} [Fintype B] [DecidableEq B] (f : I→ℕ) (xs : List I) (cap : B→ℕ) :
    (pack id (xs.map f) cap).decisions=(pack f xs cap).decisions.map (written f) := by
  induction xs generalizing cap with
  | nil => rfl
  | cons x xs ih =>
    change (pack id (f x :: xs.map f) cap).decisions = _
    rw [pack_decisions_cons, pack_decisions_cons, List.map_cons]
    exact congrArg (List.cons (f x, firstFit (f x) cap)) (ih _)

variable (A : Aperture S M) (f : I→ℕ) (xs : List I) (cap : C→ℕ) (fits : xs.length≤n)
local notation "numeric" => Packing.decisions (packing (needs (n:=n) f xs) (capacities A cap))
local notation "localRows" => Packing.decisions (pack f xs (Aperture.mass A cap))
local notation "original" => Packing.decisions (pack f xs cap)

include fits in
theorem numeric_decisions : ∃tail, numeric=(localRows).map (written f)++tail := by
  have undo : capacities A cap ∘ position M=A.mass cap := by ext v;simp [capacities]
  unfold packing
  rw [undo,needs_fit f xs fits,pack_append,map_amount]
  exact ⟨_,rfl⟩

private theorem localLength : (localRows).length=xs.length := by
  simpa using congrArg List.length (pack f xs (A.mass cap)).order

include fits in
theorem same_row (i : Fin (numeric).length) (j : Fin (localRows).length) (eqn : i.val=j.val) :
    (numeric).get i = written f ((localRows).get j) := by
  obtain ⟨tail,split⟩ := numeric_decisions A f xs cap fits
  have h := congrArg (fun ys : List (ℕ×Option (Fin M))=>ys[j.val]?) split
  have hi : j.val<(numeric).length := eqn ▸ i.isLt
  have hj : j.val<((localRows).map (written f)).length := by simp
  have hIx : (⟨j.val,hi⟩ : Fin (numeric).length)=i := Fin.ext eqn.symm
  rw [←hIx]
  simpa only [List.getElem?_append_left hj,List.getElem?_map,List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem j.isLt,Option.map_some,Option.some.injEq,List.get_eq_getElem] using h

variable (support : ∀v,0<cap v→v∈Sparse.keep S)

theorem prefix_sum {a b t : ℕ} (ha : t≤a) (hb : t≤b) (l : Fin a→ℕ) (r : Fin b→ℕ)
    (same : ∀i : Fin t,l ⟨i.val,i.isLt.trans_le ha⟩=r ⟨i.val,i.isLt.trans_le hb⟩) :
    (∑i : Fin a,if i.val<t then l i else 0)=∑i : Fin b,if i.val<t then r i else 0 := by
  rw [←SelectionTrace.sum_before ha,←SelectionTrace.sum_before hb]
  exact Finset.sum_congr rfl (fun i _=>same i)

private theorem value_prefix {a b t : ℕ} (ha : t≤a) (hb : t≤b) (l : Fin a→ℕ) (r : Fin b→ℕ)
    (p : Fin a→Bool) (q : Fin b→Bool)
    (same : ∀i : Fin t,l ⟨i.val,i.isLt.trans_le ha⟩=r ⟨i.val,i.isLt.trans_le hb⟩ ∧
      p ⟨i.val,i.isLt.trans_le ha⟩=q ⟨i.val,i.isLt.trans_le hb⟩) :
    (∑i : Fin a,if i.val<t ∧ p i then l i else 0)=∑i : Fin b,if i.val<t ∧ q i then r i else 0 := by
  simp_rw [ite_and]
  exact prefix_sum ha hb _ _ (fun i => by rw [(same i).1,(same i).2])

private theorem capacity_at (u : Fin (Sparse.roster S).length) :
    capacities A cap (u.castLE A.capacity)=cap ((Sparse.roster S).get u) := by
  let : Nonempty (Fin (Sparse.roster S).length) := ⟨u⟩
  let a := (Sparse.coordinate S).symm u
  have hu : position M ((Sparse.padded A.capacity).slot a)=u.castLE A.capacity := by
    apply Fin.ext
    exact (A.numeric_slot a).trans
      (congrArg (fun j : Fin (Sparse.roster S).length => j.val)
        ((Sparse.coordinate S).apply_symm_apply u))
  unfold capacities
  rw [←hu,Equiv.symm_apply_apply,Aperture.mass,A.row_at]
  change cap ((Sparse.roster S).get (Sparse.coordinate S a))=_
  simp [a]

include support in
/-- At every occupied slot, flattened old thick-edge offsets agree with the
original global destination order, even across omitted zero-traffic bins. -/
theorem capacity_prefix (u : Fin (Sparse.roster S).length) :
    ProtocolRAMPortRanks.«prefix» (capacities A cap) Fin.val (u.castLE A.capacity) =
      ProtocolRAMPortRanks.«prefix» cap code ((Sparse.roster S).get u) := by
  unfold ProtocolRAMPortRanks.«prefix»
  let loc (i : Fin M) (h : i.val < u.val) : Fin (Sparse.roster S).length := ⟨i.val,h.trans u.isLt⟩
  apply Finset.sum_bij_ne_zero (fun i hi _=> (Sparse.roster S).get (loc i (Finset.mem_filter.mp hi).2))
  · intro i hi _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(roster_strict S) (Finset.mem_filter.mp hi).2⟩
  · intro i hi _ j hj _ eqn
    exact Fin.ext (congrArg (fun k : Fin (Sparse.roster S).length => k.val) ((Sparse.roster_nodup S).injective_get eqn))
  · intro c hc live
    have included : c∈Sparse.roster S :=
      List.mem_filter.mpr ⟨mem_binOrder c,decide_eq_true (support c (Nat.pos_of_ne_zero live))⟩
    obtain ⟨j,hj⟩ := List.mem_iff_get.mp included
    have before : j<u := (roster_strict S).lt_iff_lt.mp (by rw [hj];exact (Finset.mem_filter.mp hc).2)
    refine ⟨j.castLE A.capacity,Finset.mem_filter.mpr ⟨Finset.mem_univ _,before⟩,?_,hj⟩
    rw [capacity_at A cap j,hj]
    exact live
  · intro i hi _
    exact capacity_at A cap (loc i (Finset.mem_filter.mp hi).2)

include fits support in
/-- The old occurrence, its sparse target slot and all three chronological
counters read by the short table. Capacity before this target is kept as an
explicit relative source offset. -/
theorem original_fields (e : Pairs f original) :
    ∃z : Unit (needs (n:=n) f xs) (capacities A cap),∃u : Fin (Sparse.roster S).length,
      (Sparse.roster S).get u=e.1 ∧ z.2.1.val.val=e.2.1.val.val ∧ z.2.2.val=e.2.2.val ∧
      let d := fields (needs (n:=n) f xs) (capacities A cap) z
      d.accepted=(pairNumber f original e).val ∧ d.bin=u.val ∧
      d.thin=(∑i : Locations original,if i.val<e.2.1.val.val then f ((original).get i).1 else 0)+e.2.2.val ∧
      d.thick=ProtocolRAMPortRanks.«prefix» cap code e.1+(thickEnd (pack f xs cap) e).2.val := by
  let := Aperture.roster_nonempty e.1 S
  let old := e.2.1.val
  let loc : Fin (localRows).length := ⟨old.val,old.isLt.trans_eq (A.rows_length f xs cap).symm⟩
  have nRows : (numeric).length=n := length _ _
  have locSmall : loc.val<n := loc.isLt.trans_le ((localLength A f xs cap).le.trans fits)
  let j : Fin (numeric).length := ⟨loc.val,locSmall.trans_eq nRows.symm⟩
  obtain ⟨v,opt,l,r⟩ := A.source_row f xs cap support loc old rfl
  have selected : opt.map (Sparse.dense S).name=some e.1 := (congrArg Prod.snd r).symm.trans e.2.1.property
  obtain ⟨a,ha,orig⟩ := Option.map_eq_some_iff.mp selected
  let slot := (Sparse.padded A.capacity).slot a
  let u := Sparse.coordinate S a
  have line := same_row A f xs cap fits j loc rfl
  rw [l,ha] at line
  have chosen : ((numeric).get j).2 = some slot := congrArg Prod.snd line
  have amt : ((numeric).get j).1=f ((original).get old).1 := by rw [r,line];rfl
  let z : Unit (needs (n:=n) f xs) (capacities A cap) := ⟨slot,⟨j,chosen⟩,⟨e.2.2.val,e.2.2.isLt.trans_eq amt.symm⟩⟩
  refine ⟨z,u,orig,rfl,rfl,?_,A.numeric_slot a,?_,?_⟩
  · change (pairNumber id numeric z).val=_
    rw [pairNumber_prefix,pairNumber_prefix]
    apply congrArg (·+e.2.2.val)
    apply Eq.trans _ (A.aligned_totals f xs cap support old.val).2
    apply value_prefix j.isLt.le loc.isLt.le
    intro i
    have atI := same_row A f xs cap fits ⟨i.val,i.isLt.trans_le j.isLt.le⟩ ⟨i.val,i.isLt.trans_le loc.isLt.le⟩ rfl
    exact ⟨congrArg Prod.fst atI,congrArg (fun p=>p.2.isSome) atI⟩
  · change ProtocolRAMPortRanks.«prefix» _ Fin.val _+e.2.2.val=_
    apply congrArg (·+e.2.2.val)
    unfold ProtocolRAMPortRanks.«prefix»
    rw [Finset.sum_filter]
    apply Eq.trans _ (A.aligned_totals f xs cap support old.val).1
    apply prefix_sum locSmall.le loc.isLt.le
    intro i
    have ln := same_row A f xs cap fits ⟨i.val,i.isLt.trans_le j.isLt.le⟩ ⟨i.val,i.isLt.trans_le loc.isLt.le⟩ rfl
    exact (amount_at _ _ _).symm.trans (congrArg Prod.fst ln)
  · change ProtocolRAMPortRanks.«prefix» (capacities A cap) Fin.val (position M slot)+(thickEnd (packing _ _) z).2.val=_+_
    have here : position M slot=u.castLE A.capacity := Fin.ext (A.numeric_slot a)
    rw [here,capacity_prefix A cap support u,show (Sparse.roster S).get u=e.1 from orig]
    apply congrArg (_+·)
    rw [thickEnd_prefix,thickEnd_prefix]
    apply congrArg (·+e.2.2.val)
    rw [←assigned_take, ←assigned_take]
    refine Eq.trans ?_ ((A.original_use f xs cap support old.val a).trans
      (congrArg (fun c : C => assigned f c ((original).take old.val)) orig))
    change assigned id slot ((numeric).take j.val) =
      assigned f slot ((localRows).take loc.val)
    rw [assigned_take, assigned_take]
    simp_rw [ite_and]
    apply prefix_sum j.isLt.le loc.isLt.le
    intro i
    have row := same_row A f xs cap fits
      ⟨i.val,i.isLt.trans_le j.isLt.le⟩ ⟨i.val,i.isLt.trans_le loc.isLt.le⟩ rfl
    exact congrArg (fun p : ℕ × Option (Fin M) => if p.2 = some slot then p.1 else 0) row

/-- Padded source descriptors have no accepted occurrences beyond those of
the original all-destination allocator. -/
theorem accepted_total {U V : Type*} [Fintype V] [DecidableEq V]
    (g : U→ℕ) (ds : List (U×Option V)) :
    Fintype.card (Pairs g ds)= ∑i : Fin ds.length,if (ds.get i).2.isSome then g (ds.get i).1 else 0 := by
  rw [Fintype.card_congr (byItem g ds),Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [←Finset.sum_filter]
  exact (Finset.sum_subtype (p := fun i : Locations ds => (ds.get i).2.isSome)
    (Finset.univ.filter fun i : Locations ds => (ds.get i).2.isSome)
    (fun _ => by simp) (fun i => g (ds.get i).1)).symm

include fits support in
theorem source_count [Nonempty (Fin (Sparse.roster S).length)] :
    Fintype.card (Unit (needs (n:=n) f xs) (capacities A cap))=Fintype.card (Pairs f original) := by
  rw [accepted_total,accepted_total]
  have ll := localLength A f xs cap
  have nl : (numeric).length=n := length _ _
  have full := A.rows_length f xs cap
  let t := (localRows).length
  have tFits : t≤(numeric).length := ll.le.trans (fits.trans_eq nl.symm)
  calc
    _ = ∑i : Fin (numeric).length,if i.val<t ∧ ((numeric).get i).2.isSome then ((numeric).get i).1 else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases live : i.val<t
      · simp [live]
      · have beyond : xs.length≤ i.val := by simpa only [t,ll] using Nat.le_of_not_gt live
        have zero : ((numeric).get i).1=0 := (amount_at _ _ i).trans (by
          simp [needs,index,List.getElem?_eq_none beyond])
        simp only [id_eq, zero, ite_self]
    _ = ∑i : Fin (localRows).length,if i.val<t ∧ ((localRows).get i).2.isSome then f ((localRows).get i).1 else 0 := by
      apply value_prefix tFits le_rfl
      intro i
      have l := same_row A f xs cap fits ⟨i.val,i.isLt.trans_le tFits⟩ i rfl
      exact ⟨congrArg Prod.fst l,congrArg (fun p=>p.2.isSome) l⟩
    _ = _ := by
      rw [(A.aligned_totals f xs cap support t).2]
      apply Finset.sum_congr rfl
      intro i _
      simp [show i.val<t from i.isLt.trans_eq full.symm]

include fits support in
theorem original_dense {limit : ℕ} (small : ∀z∈xs,f z≤limit) (e : Pairs f original) :
    ∃u : Fin (Sparse.roster S).length,∃d : Record,(Sparse.roster S).get u=e.1 ∧
      dense (needs (n:=n) f xs) (capacities A cap) limit (pairNumber f original e).val=some d ∧
      d.accepted=(pairNumber f original e).val ∧ d.bin=u.val ∧
      d.thin=(∑i : Locations original,if i.val<e.2.1.val.val then f ((original).get i).1 else 0)+e.2.2.val ∧
      d.thick=ProtocolRAMPortRanks.«prefix» cap code e.1+(thickEnd (pack f xs cap) e).2.val := by
  obtain ⟨z,u,old,_loc,offset,order,slot,thin,thick⟩ := original_fields A f xs cap fits support e
  have member : ((original).get e.2.1.val).1∈xs := by
    have mapped : ((original).get e.2.1.val).1 ∈ (original).map Prod.fst :=
      List.mem_map.mpr ⟨_, List.get_mem _ _, rfl⟩
    exact (congrArg (fun ys : List I => ((original).get e.2.1.val).1 ∈ ys)
      (pack f xs cap).order).mp mapped
  have bound := e.2.2.isLt.trans_le (small _ member)
  have zbound : z.2.2.val < limit := by
    rw [offset]
    exact bound
  have d := dense_at (limit:=limit) (needs (n:=n) f xs) (capacities A cap) z zbound
  rw [order] at d
  exact ⟨u,_,old,d,order,slot,thin,thick⟩


end Hierarchy.DescentPacking.PackedLocalMatch

end
end OAI
