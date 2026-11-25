import OAI.Computability.BorderVNP.PackedBottomCoreChoices
import OAI.Computability.BorderVNP.DiagonalTallyReportChoices

/-! # The unique passing compact-use suffix of a single fixed physical cell -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomReports

open CellSparse DiagonalTallyCellReports
open private slice_append from OAI.Computability.BorderVNP.DiagonalTallyReportChoices

private theorem copy_slot_lt (b : Bundle) {pre : List Bool} (hp : b.CorePass pre)
    (i : Fin b.header.copies) {r : ℕ} (hr : r < b.header.cap) :
    b.header.boxBase+i.val*b.header.stride+b.header.orig+r < pre.length := by
  have hi := Nat.mul_le_mul_right b.header.stride (Nat.succ_le_of_lt i.isLt)
  rw [Nat.succ_mul] at hi
  have hs := hp.stride
  have hb := hp.extent
  unfold bottomStride at hs
  omega

private theorem pair_index (start : ℕ) {r c : ℕ} (j : Fin r) (i : Fin c) :
    start+(finProdFinEquiv (j,i)).val = start+j.val*c+i.val := by
  change start+(i.val+c*j.val) = _
  rw [Nat.mul_comm c j.val]
  omega

/-- A checked original box and its true zero padding make the supplemental
row list equivalent to the one compact block of original unary choices. -/
theorem Bundle.reportRows_iff_useChoice (b : Bundle) (pre : List Bool) (hp : b.CorePass pre)
    (bank : ℕ → Bool) (front : ∀ k < pre.length, bank k = lookup pre k)
    (boxes : List (List Factor)) (cursor : ℕ) :
    (∀ row ∈ reportRows b.header.boxBase b.header.orig b.header.cap b.header.copies cursor b.factors,
        row.Valid boxes bank) ↔
      reportSlice bank cursor b.useBits = List.ofFn (b.useChoice pre) := by
  have rows := reportRows_valid bank boxes b.header.boxBase b.header.orig b.header.cap b.header.copies cursor b.factors hp.capacity
  have selected (j : Fin (count b.factors)) (i : Fin b.header.copies) :
      bank (b.header.boxBase+i.val*b.header.stride+b.header.orig+j.val) = b.useChoice pre (finProdFinEquiv (j,i)) := by
    rw [front _ (copy_slot_lt b hp i (j.isLt.trans_le hp.capacity)),b.useChoice_pair]
    exact ((stage_pass (lookup pre) _ i.val b.header.orig b.factors).mp (hp.staged i)).2 j
  constructor
  · intro pass
    apply congrArg List.ofFn
    funext k
    obtain ⟨⟨j,i⟩,rfl⟩ := (finProdFinEquiv (m := count b.factors) (n := b.header.copies)).surjective k
    have h := rows.mp pass i.val i.isLt j.val (j.isLt.trans_le hp.capacity)
    rw [stageValue,ite_eq_left j.isLt,← hp.stride] at h
    exact (congrArg bank (pair_index cursor j i)).trans (h.symm.trans (selected j i))
  · intro same
    have reads := List.ofFn_injective same
    apply rows.mpr
    intro i hi t ht
    rw [← hp.stride]
    by_cases used : t < count b.factors
    · rw [stageValue,ite_eq_left used]
      let r : Fin (count b.factors) := ⟨t,used⟩
      let j : Fin b.header.copies := ⟨i,hi⟩
      have hr := congrFun reads (finProdFinEquiv (r,j))
      change bank (cursor+(finProdFinEquiv (r,j)).val) = _ at hr
      rw [pair_index] at hr
      exact (selected r j).trans hr.symm
    · rw [stageValue,ite_eq_right used,front _ (copy_slot_lt b hp ⟨i,hi⟩ ht)]
      have hz := hp.zero ⟨i,hi⟩ (t-count b.factors) (by omega)
      convert hz using 2
      omega

/-- The true stable list of owned bundles has one passing compact use slice.
The preceding count payload may be arbitrary when applying this equivalence. -/
theorem supplements_iff_useSlice (pre : List Bool) (bs : List Bundle)
    (core : ∀ b ∈ bs, b.CorePass pre) (bank : ℕ → Bool) (front : ∀ k < pre.length, bank k = lookup pre k)
    (boxes : List (List Factor)) (cursor : ℕ) :
    (∀ row ∈ supplements cursor bs, row.Valid boxes bank) ↔
      reportSlice bank cursor (bs.map Bundle.useBits).sum = useTape pre bs := by
  induction bs generalizing cursor with
  | nil => simp [supplements,useTape,reportSlice]
  | cons b bs ih =>
    rw [supplements,List.forall_mem_append,b.reportRows_iff_useChoice pre (core b List.mem_cons_self) bank front boxes cursor,
      ih (fun x hx => core x (.tail _ hx)) (cursor+b.useBits)]
    simp only [List.map_cons,List.sum_cons,← slice_append,useTape,List.flatMap_cons]
    exact ⟨fun h => congrArg₂ List.append h.1 h.2,fun h => List.append_inj h (by simp [reportSlice])⟩

private theorem slice_suffix (front suffix : List Bool) :
    reportSlice (lookup (front++suffix)) front.length suffix.length = suffix := by
  apply List.ext_getElem
  · simp [reportSlice]
  · intro i _ hi
    simp only [reportSlice,List.getElem_ofFn,lookup,List.head?_drop,
      List.getElem?_append_right (Nat.le_add_right front.length i),Nat.add_sub_cancel_left,
      List.getElem?_eq_getElem hi,Option.getD_some]

/-- For a fixed original physical assignment and a tail of the declared width,
supplemental validation is equivalent to equality with its canonical use list.
Count digits occupy the preceding block. -/
theorem supplements_iff_useTape (pre counts uses : List Bool) (bs : List Bundle) (boxes : List (List Factor))
    (core : ∀ b ∈ bs, b.CorePass pre) (width : uses.length = (bs.map Bundle.useBits).sum) :
    (∀ row ∈ supplements (pre.length+counts.length) bs, row.Valid boxes (lookup (pre++counts++uses))) ↔
      uses = useTape pre bs := by
  let bank := lookup (pre++counts++uses)
  have agree (k : ℕ) (hk : k < pre.length) : bank k = lookup pre k := by
    simp only [bank,List.append_assoc,lookup,List.head?_drop,List.getElem?_append_left hk]
  have h := supplements_iff_useSlice pre bs core bank agree boxes (pre.length+counts.length)
  rw [←width,←List.length_append] at h
  rw [show reportSlice bank (pre++counts).length uses.length = uses from slice_suffix _ _] at h
  simpa only [List.length_append,bank] using h

/-- Exactly one fixed-length local use guess passes every physical supplemental
equality and zero check. Its bits are read from the original selected wires. -/
theorem existsUnique_useTape (pre counts : List Bool) (bs : List Bundle) (boxes : List (List Factor))
    (core : ∀ b ∈ bs, b.CorePass pre) :
    ∃! uses : List Bool, uses.length=(bs.map Bundle.useBits).sum ∧
      ∀ row ∈ supplements (pre.length+counts.length) bs, row.Valid boxes (lookup (pre++counts++uses)) := by
  refine ⟨useTape pre bs,⟨useTape_length ..,(supplements_iff_useTape _ _ _ _ _ core (useTape_length ..)).mpr rfl⟩,?_⟩
  intro uses h
  exact (supplements_iff_useTape pre counts uses bs boxes core h.1).mp h.2

end Packing.BottomReports

end BorderVNP
end Computability
end OAI
