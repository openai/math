import OAI.Computability.BorderVNP.DiagonalTallyReportDisjoint
import OAI.Computability.BorderVNP.DiagonalTallyReportAllocation
import OAI.Computability.BorderVNP.RoutingISACellBanks

/-! # Persistent report writes in the actual global-cell and post-task allocations -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open DiagonalTallyAllocation RoutingISA

/-- The actual source and output bank assignments and the physical volume ceilings.
The finite global ordinal is shared by the receive bank, counters, width and supplement. -/
structure ReportAllocation (pre : BeforeTasks) (post : AfterTasks) (banks : CellBanks.Layout)
    (l : ReportLayout) (cs : List (ReportCell l)) (q : ReportCursor) : Prop where
  /-- The receiving banks have one index per physical cell. The later report tables can reserve more rows. -/
  bankCells : banks.cells ≤ pre.bound.cells
  postCells : post.bound.cells=pre.bound.cells
  /-- Public frame, receive banks and earlier source data precede the pre-task scratch. -/
  frameBefore : l.frame+96 ≤ banks.bankStart
  bankBefore : banks.bankStart+banks.cells*banks.stride ≤ pre.start
  /-- Typed call windows fit between the two named partitions. -/
  preBefore : pre.limit ≤ post.start
  /-- Actual pre-task pointers. -/
  headers : l.headers=pre.six
  table : l.bundleTable=pre.bundleTable
  widths : l.tailWidths=pre.tailWidths
  supplement : l.supplement=pre.supplement
  stride : l.supplementStride=pre.bound.supplementStride
  counters : l.counters=pre.counters
  /-- Fixed dimensional controls and actual initial global cursors. -/
  gadgets : l.gadgets=post.bound.gadgets
  countWidth : l.countWidth=post.bound.countWidth
  initial : q=⟨post.packed,post.descriptors,post.refs,0⟩
  /-- One distinct global cell number per genuine owned row. -/
  owned : ∃ ix : Fin cs.length ↪ Fin banks.cells, ∀ i, cs[i].number=(ix i).val
  /-- Receiving-bank base and true original-plus-guessed width of each row. -/
  receiving : ∀ c∈cs, c.external=banks.bank c.number ∧ c.supplied+c.tailWidth ≤ banks.stride
  /-- Actual supplemental record words of each owned cell. -/
  supplements : ∀ c∈cs, supplementWords c.bundles ≤ pre.bound.supplementStride
  /-- Total genuine original bundle count, maximum one-copy marks, and expanded weighted copies. -/
  bundleCount : (cs.map fun c => c.bundles.length).sum ≤ post.bound.bundles
  marked : ∀ c∈cs, ∀ b∈c.bundles, b.positions.length ≤ post.bound.marked
  uses : teamWeighted cs ≤ post.bound.uses

/-- Restrict the actual finite global cell order to the team's owned subset. -/
theorem ownedIndex_of_equiv {l : ReportLayout} {cs : List (ReportCell l)} {C : ℕ} {Team : Type*}
    (team : Fin C → Team) (t : Team) (cells : Fin cs.length ≃ {c : Fin C // team c=t})
    (num : ∀ i, cs[i].number=(cells i).val.val) :
    ∃ ix : Fin cs.length ↪ Fin C, ∀ i, cs[i].number=(ix i).val :=
  ⟨cells.toEmbedding.trans (Function.Embedding.subtype _),num⟩

private theorem bundle_packed_le (bs : List ReportBundle) (W : ℕ)
    (h : ∀ b∈bs, b.positions.length ≤ W) : packedWords bs ≤ bs.length*(1+3*W) := by
  induction bs with
  | nil => simp [packedWords]
  | cons b bs ih =>
    obtain ⟨head,tail⟩ := List.forall_mem_cons.mp h
    have hb := ih tail
    unfold packedWords at hb ⊢
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    rw [Nat.succ_mul bs.length]
    omega

theorem teamPacked_le {l : ReportLayout} (cs : List (ReportCell l)) (W : ℕ)
    (h : ∀ c∈cs, ∀ b∈c.bundles, b.positions.length ≤ W) :
    teamPacked cs ≤ (cs.map fun c => c.bundles.length).sum*(1+3*W) := by
  induction cs with
  | nil => simp [teamPacked]
  | cons c cs ih =>
    obtain ⟨head,tail⟩ := List.forall_mem_cons.mp h
    have hc := bundle_packed_le c.bundles W head
    have ht := ih tail
    unfold teamPacked at ht ⊢
    simp only [List.map_cons,List.sum_cons,Nat.add_mul]
    omega

variable {pre : BeforeTasks} {post : AfterTasks} {banks : CellBanks.Layout}
    {l : ReportLayout} {cs : List (ReportCell l)} {q : ReportCursor}

theorem ReportAllocation.owned_le (h : ReportAllocation pre post banks l cs q) :
    cs.length ≤ pre.bound.cells := by
  obtain ⟨ix,_⟩ := h.owned
  apply le_trans _ h.bankCells
  simpa using Fintype.card_le_of_injective ix ix.injective

/-- Each actual owned cell has a bank in the physical receive arena. -/
theorem ReportAllocation.bankNumber (h : ReportAllocation pre post banks l cs q)
    (c : ReportCell l) (hc : c∈cs) : c.number < banks.cells := by
  obtain ⟨ix,num⟩ := h.owned
  obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hc
  exact (num ⟨i,hi⟩) ▸ (ix ⟨i,hi⟩).isLt

theorem ReportAllocation.number_lt (h : ReportAllocation pre post banks l cs q)
    (c : ReportCell l) (hc : c∈cs) : c.number < pre.bound.cells := (h.bankNumber c hc).trans_le h.bankCells

/-- Exact terminal packed, reference and descriptor cursors stay in the three real
reservations, including the separating one-word gaps. -/
theorem ReportAllocation.ends (h : ReportAllocation pre post banks l cs q) :
    let e := cs.foldl (fun a c => c.after a) q
    e.packed<post.refs ∧ e.refs<post.descriptors ∧ e.descriptors<post.fresh := by
  have length : cs.length ≤ post.bound.cells := h.postCells ▸ h.owned_le
  have p := (teamPacked_le cs post.bound.marked h.marked).trans (Nat.mul_le_mul_right _ h.bundleCount)
  have g := Nat.mul_le_mul_right post.bound.gadgets length
  have r := Nat.mul_le_mul_right post.bound.countWidth g
  have u := h.uses
  obtain ⟨ep,er,ed⟩ := cells_fold_fields cs q
  rw [h.gadgets,h.countWidth,← Nat.mul_assoc] at er
  rw [h.gadgets] at ed
  simp only [h.initial] at ep er ed ⊢
  have rp : post.refs=post.packed+post.bound.bundles*(1+3*post.bound.marked)+1 := rfl
  have dr : post.descriptors=post.refs+(post.bound.cells*post.bound.gadgets*post.bound.countWidth+post.bound.uses)+1 := rfl
  have fd : post.fresh=post.descriptors+5*(post.bound.cells*post.bound.gadgets+post.bound.uses+post.bound.vertices)+1 := rfl
  omega

/-- Every indexed destination is below the next global physical bank. -/
theorem ReportAllocation.banksOrdered (h : ReportAllocation pre post banks l cs q)
    (c : ReportCell l) (hc : c∈cs) : c.banksOrdered q.packed := by
  have n := h.number_lt c hc
  have sb := h.supplements c hc
  obtain ⟨base,room⟩ := h.receiving c hc
  have ext := Nat.mul_le_mul_right banks.stride (h.bankNumber c hc)
  have su := Nat.mul_le_mul_right pre.bound.supplementStride n
  rw [Nat.succ_mul] at ext su
  have before := h.bankBefore
  have last : pre.counters+2*pre.bound.cells ≤ pre.limit := by
    simp only [BeforeTasks.limit,BeforeTasks.bundleTable,BeforeTasks.ranges,BeforeTasks.six,BeforeTasks.four,
      BeforeTasks.merged]
    omega
  have after : post.start ≤ post.packed := by
    simp only [AfterTasks.packed,AfterTasks.ids,AfterTasks.lookupRefs,AfterTasks.lookupRows]
    omega
  have middle := h.preBefore
  simp only [ReportCell.banksOrdered,base,CellBanks.Layout.bank,h.initial,h.widths,h.supplement,h.stride,h.counters]
  change banks.bankStart+c.number*banks.stride+c.supplied+c.tailWidth ≤ pre.start ∧
    pre.start+c.number+1 ≤ pre.start+pre.bound.cells ∧
    pre.supplement+c.number*pre.bound.supplementStride+supplementWords c.bundles ≤
      pre.supplement+pre.bound.cells*pre.bound.supplementStride ∧ pre.counters+2*c.number+2 ≤ post.packed
  omega

private theorem ReportAllocation.separateRows (h : ReportAllocation pre post banks l cs q)
    (c d : ReportCell l) (hc : c∈cs) (hd : d∈cs) (ne : c.number ≠ d.number) : c.banksApart d := by
  obtain ⟨cbase,cr⟩ := h.receiving c hc
  obtain ⟨dbase,dr⟩ := h.receiving d hd
  have csup := h.supplements c hc
  have dsup := h.supplements d hd
  simp only [ReportCell.banksApart,cbase,dbase,CellBanks.Layout.bank,h.stride]
  rcases lt_or_gt_of_ne ne with hn|hn
  all_goals
    have hr := Nat.mul_le_mul_right banks.stride hn
    have hs := Nat.mul_le_mul_right pre.bound.supplementStride hn
    rw [Nat.succ_mul] at hr hs
    omega

/-- Physical stores for every true owned cell start at or above the receiving arena. -/
theorem ReportAllocation.aboveBankStart (h : ReportAllocation pre post banks l cs q)
    (s : ReportWrite) (hs : s∈cellWrites cs q) : banks.bankStart ≤ s.address := by
  have bb := h.bankBefore
  have ab := h.preBefore
  have ps : pre.start ≤ pre.limit := by rw [pre.footprint]; omega
  have preS : pre.start ≤ pre.supplement := Nat.le_add_right ..
  have preC : pre.supplement ≤ pre.counters := Nat.le_add_right ..
  have lower : post.start ≤ post.packed := by
    simp only [AfterTasks.packed,AfterTasks.ids,AfterTasks.lookupRefs,AfterTasks.lookupRows]
    omega
  have r : post.packed ≤ post.refs := by unfold AfterTasks.refs; omega
  have d : post.refs ≤ post.descriptors := by unfold AfterTasks.descriptors; omega
  rcases cellWrites_range cs q s hs with stream|⟨c,hc,cell⟩
  · simp only [cursorRange,ReportWrite.within,h.initial] at stream
    omega
  · have base := (h.receiving c hc).1
    simp only [cellRange,ReportWrite.within,base,CellBanks.Layout.bank,h.widths,BeforeTasks.tailWidths,
      h.supplement,h.counters] at cell
    omega

/-- Every cell store preserves the earlier shared frame. -/
theorem ReportAllocation.afterFrame (h : ReportAllocation pre post banks l cs q)
    (s : ReportWrite) (hs : s∈cellWrites cs q) : l.frame+96 ≤ s.address :=
  h.frameBefore.trans (h.aboveBankStart s hs)

/-- The low writes stop before the merged counters. High writes stay inside the
actual packed-to-descriptor stream, even when the reserved maxima are larger. -/
theorem ReportAllocation.write_bank_interval (h : ReportAllocation pre post banks l cs q)
    (s : ReportWrite) (hs : s∈cellWrites cs q) :
    s.address+s.data.length ≤ pre.merged ∨
      s.within post.packed (cs.foldl (fun a c => c.after a) q).descriptors := by
  rcases cellWrites_range cs q s hs with streams|⟨c,hc,cell⟩
  · right
    obtain ⟨ep,er,_⟩ := h.ends
    obtain ⟨_,_,ed⟩ := cells_fold_fields cs q
    have r : post.packed ≤ post.refs := by unfold AfterTasks.refs; omega
    have d : post.refs ≤ post.descriptors := by unfold AfterTasks.descriptors; omega
    simp only [cursorRange,ReportWrite.within,h.initial] at streams ep er ed ⊢
    omega
  · left
    obtain ⟨ext,width,supp,_⟩ := h.banksOrdered c hc
    have n := h.number_lt c hc
    have wc : pre.tailWidths ≤ pre.supplement := Nat.le_add_right ..
    have sc : pre.supplement ≤ pre.counters := Nat.le_add_right ..
    simp only [cellRange,ReportWrite.within,h.widths,h.supplement,h.counters] at cell ext width supp
    change s.address+s.data.length ≤ pre.counters+2*pre.bound.cells
    omega

/-- Cell writes leave untouched the task windows and cube lookup banks. -/
theorem ReportAllocation.outsideMiddle (h : ReportAllocation pre post banks l cs q)
    (s : ReportWrite) (hs : s∈cellWrites cs q) : s.address+s.data.length ≤ pre.merged ∨ post.packed ≤ s.address :=
  (h.write_bank_interval s hs).imp_right And.left

/-- Every report store ends before the typed call windows or lies between the
post-task packed base and the true terminal five-word descriptor cursor. -/
theorem ReportAllocation.write_zone (h : ReportAllocation pre post banks l cs q)
    (s : ReportWrite) (hs : s∈cellWrites cs q) :
    s.address+s.data.length ≤ pre.limit ∨
      post.packed ≤ s.address ∧ s.address+s.data.length ≤ (cs.foldl (fun a c => c.after a) q).descriptors := by
  apply (h.write_bank_interval s hs).imp_left
  intro low
  simp only [BeforeTasks.limit,BeforeTasks.bundleTable,BeforeTasks.ranges,BeforeTasks.six,BeforeTasks.four]
  omega

/-- All native store blocks, including the final frame-35 count, are pairwise
disjoint in the allocated receiving, pre-task and post-task banks. -/
theorem ReportAllocation.prepareWrites_pairwise (h : ReportAllocation pre post banks l cs q) :
    (prepareWrites cs q).Pairwise ReportWrite.apart := by
  have distinct : cs.Pairwise ReportCell.banksApart := by
    obtain ⟨ix,num⟩ := h.owned
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj lt
    apply h.separateRows _ _ (List.getElem_mem ..) (List.getElem_mem ..)
    change cs[(⟨i,hi⟩ : Fin cs.length)].number ≠ cs[(⟨j,hj⟩ : Fin cs.length)].number
    rw [num,num]
    intro eq
    have x := ix.injective (Fin.ext eq)
    exact (Nat.ne_of_lt lt) (congrArg Fin.val x)
  obtain ⟨p,r,_⟩ := h.ends
  rw [prepareWrites,List.pairwise_append]
  refine ⟨cellWrites_pairwise cs q h.banksOrdered distinct ?_,by simp,?_⟩
  · have qr : q.refs=post.refs := h.initial ▸ rfl
    have qd : q.descriptors=post.descriptors := h.initial ▸ rfl
    exact ⟨p.le.trans qr.ge,r.le.trans qd.ge⟩
  · intro s hs t ht
    obtain rfl := List.mem_singleton.mp ht
    right
    have a := h.afterFrame s hs
    simp
    omega

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
