import OAI.Computability.BorderVNP.DiagonalTallyAllocatedInputsCell
import OAI.Computability.BorderVNP.DiagonalTallyReportAllocatedWrites

/-! # The native owned-cell scanner on its allocated physical inputs -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open DiagonalTallyAllocation RoutingISA

variable {pre : BeforeTasks} {post : AfterTasks} {banks : CellBanks.Layout}
    {l : ReportLayout} {cs : List (ReportCell l)} {q : ReportCursor}

/-- Opaque site strings live after the supplied and report words in their own
fixed-stride receive bank, at the address named by their genuine six-word row. -/
def SiteIntervals {l : ReportLayout} (cs : List (ReportCell l)) (description stride : ℕ) :=
  ∀ c ∈ cs, ∀ b ∈ c.bundles, c.external+c.supplied+c.tailWidth ≤ b.header.siteSlot ∧
    b.header.siteSlot+description ≤ c.external+stride

private theorem number_inj (h : ReportAllocation pre post banks l cs q)
    {c d : ReportCell l} (hc : c∈cs) (hd : d∈cs) (eqn : c.number=d.number) : c=d := by
  obtain ⟨ix,num⟩ := h.owned
  obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hc
  obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hd
  have e := ix.injective (Fin.ext ((num ⟨i,hi⟩).symm.trans (eqn.trans (num ⟨j,hj⟩))))
  have ij : i=j := congrArg Fin.val e
  subst j
  rfl

private theorem bank_past_le (h : ReportAllocation pre post banks l cs q) {c : ReportCell l}
    (hc : c∈cs) : c.external+banks.stride ≤ pre.start := by
  have n : c.number < banks.cells := h.bankNumber c hc
  have upper := Nat.mul_le_mul_right banks.stride n
  rw [Nat.succ_mul] at upper
  have before := h.bankBefore
  rw [(h.receiving c hc).1,CellBanks.Layout.bank]
  omega

private theorem guess_apart_site (h : ReportAllocation pre post banks l cs q) {description : ℕ}
    (site : SiteIntervals cs description banks.stride)
    {c d : ReportCell l} (hc : c∈cs) (hd : d∈cs) {b : ReportBundle} (hb : b∈c.bundles) :
    d.external+d.supplied+d.tailWidth ≤ b.header.siteSlot ∨
    b.header.siteSlot+description ≤ d.external+d.supplied := by
  obtain ⟨afterTail,within⟩ := site c hc b hb
  obtain ⟨dcap,droom⟩ := h.receiving d hd
  have cbase := (h.receiving c hc).1
  rcases lt_trichotomy c.number d.number with lt|same|gt
  · have bound := Nat.mul_le_mul_right banks.stride lt
    rw [Nat.succ_mul] at bound
    simp only [cbase,dcap,CellBanks.Layout.bank] at *
    omega
  · exact (number_inj h hc hd same) ▸ Or.inl afterTail
  · have bound := Nat.mul_le_mul_right banks.stride gt
    rw [Nat.succ_mul] at bound
    simp only [cbase,dcap,CellBanks.Layout.bank] at *
    omega

private def inputAddresses {l : ReportLayout} (cs : List (ReportCell l)) (banks : CellBanks.Layout)
    (pre : BeforeTasks) (description a : ℕ) : Prop :=
  a < banks.bankStart ∨ (pre.six ≤ a ∧ a < pre.limit) ∨
    ∃ c∈cs, ∃ b∈c.bundles, b.header.siteSlot ≤ a ∧ a < b.header.siteSlot+description

private theorem partitions (h : ReportAllocation pre post banks l cs q) :
    banks.bankStart ≤ pre.start ∧ pre.start ≤ pre.supplement ∧ pre.supplement ≤ pre.counters ∧
      pre.counters+2*pre.bound.cells ≤ pre.six ∧ pre.six+6*pre.bound.cells ≤ pre.bundleTable ∧
      pre.bundleTable+6*pre.bound.bundles ≤ pre.limit ∧ pre.limit ≤ post.start ∧
      post.start ≤ post.packed ∧ post.packed < post.refs ∧ post.refs < post.descriptors ∧ post.descriptors < post.fresh := by
  have bb := h.bankBefore
  have ab := h.preBefore
  simp only [BeforeTasks.supplement,BeforeTasks.tailWidths,BeforeTasks.counters,BeforeTasks.six,BeforeTasks.four,
    BeforeTasks.merged,BeforeTasks.bundleTable,BeforeTasks.ranges,BeforeTasks.limit,AfterTasks.packed,AfterTasks.ids,
    AfterTasks.lookupRefs,AfterTasks.lookupRows,AfterTasks.refs,AfterTasks.descriptors,AfterTasks.fresh] at ab ⊢
  omega

/-- Every original control, owned and grouped header, and delivered site remains readable
through every prefix of the chronological writes, including writes to another cell's bank. -/
private theorem readsClear (h : ReportAllocation pre post banks l cs q) {description : ℕ}
    (site : SiteIntervals cs description banks.stride) :
    ReportReadsClear (inputAddresses cs banks pre description) (cellWrites cs q) := by
  intro a ha s hs
  have parts := partitions h
  have aBound : a<pre.limit := by
    rcases ha with small|interval|⟨c,hc,b,hb,_,hi⟩
    · omega
    · exact interval.2
    · have within := (site c hc b hb).2
      have bound := bank_past_le h hc
      omega
  rcases cellWrites_range cs q s hs with stream|⟨d,hd,cell⟩
  · simp only [cursorRange,ReportWrite.within,h.initial] at stream
    omega
  · have db := h.banksOrdered d hd
    have dn := h.number_lt d hd
    have dx := (h.receiving d hd).1
    simp only [ReportCell.banksOrdered,h.widths,BeforeTasks.tailWidths,h.supplement,h.stride,h.counters] at db
    simp only [cellRange,ReportWrite.within,h.widths,BeforeTasks.tailWidths,h.supplement,h.stride,h.counters] at cell
    have dxLow : banks.bankStart ≤ d.external := by rw [dx,CellBanks.Layout.bank]; omega
    rcases ha with small|interval|⟨c,hc,b,hb,lo,hi⟩
    · omega
    · omega
    · have bEnd := (site c hc b hb).2.trans (bank_past_le h hc)
      have apart := guess_apart_site h site hc hd hb
      omega

private theorem prior_le_descriptor {l : ReportLayout} (cs : List (ReportCell l)) (q : ReportCursor)
    (hq : 5*q.prior ≤ q.descriptors) :
    let e := cs.foldl (fun a c => c.after a) q
    5*e.prior ≤ e.descriptors := by
  induction cs generalizing q with
  | nil => exact hq
  | cons c cs ih =>
    apply ih (c.after q)
    rw [c.after_prior,(cell_after_fields c q).2.2]
    simp only [ReportCell.operands,List.length_append,List.length_ofFn,bundleOperands_length,ReportCell.countFrame]
    omega

/-- Physical preconditions for every native iteration, starting with the actual initial
cursors of the pre- and post-task allocations. All memory hypotheses are on the original
memory, before the first scanner instruction. -/
theorem ReportAllocation.cellInputs (h : ReportAllocation pre post banks l cs q) (w description : ℕ)
    (m : ℕ → ℕ) (controls : l.ScannerControls m)
    (headers : CellPacket.WordsAt m l.headers (cs.flatMap ReportCell.headerWords))
    (received : ∀ c ∈ cs, c.Received w description m)
    (site : SiteIntervals cs description banks.stride) (controlBefore : l.control+28 ≤ banks.bankStart)
    (range : ∀ c ∈ cs, c.first+c.bundles.length ≤ pre.bound.bundles)
    (privateEnd : ∀ c ∈ cs, c.privateWires+c.supplied+c.tailWidth<2^w)
    (width : l.fieldWidth ≤ w) (coords : l.parameters+l.gadgets<2^w) (room : post.fresh<2^w) :
    cellInputs w description cs q l.headers m := by
  have parts := partitions h
  have n := h.owned_le
  have heads : l.headers+6*cs.length ≤ pre.limit := by rw [h.headers]; omega
  have ep := h.ends
  have prior := prior_le_descriptor cs q (by simp [h.initial])
  refine cellInputs_of_received cs q w description l.headers m m (inputAddresses cs banks pre description)
      (fun _ _ => rfl) (readsClear h site) headers ?_ received ?_ controls ?_
      (by omega) (by rw [h.counters]; omega) width coords (by omega) ?_ ?_
  · intro i hi
    exact Or.inr (.inl ⟨by rw [h.headers]; omega,by omega⟩)
  · intro c hc
    constructor
    · intro i hi
      have bound := range c hc
      rw [h.table]
      exact Or.inr (.inl ⟨by omega,by omega⟩)
    · intro b hb j
      exact Or.inr (.inr ⟨c,hc,b,hb,by omega,by have := j.isLt; omega⟩)
  · intro j hj
    exact Or.inl (by omega)
  · intro c hc
    have g := h.banksOrdered c hc
    simp only [ReportCell.banksOrdered] at g
    have lim := range c hc
    have raw (b : ReportBundle) (hb : b∈c.bundles) :=
      (site c hc b hb).2.trans (bank_past_le h hc)
    have pq : q.packed=post.packed := h.initial ▸ rfl
    have w0 : l.tailWidths=pre.start := h.widths
    refine ⟨by rw [h.table]; omega,by omega,privateEnd c hc,by omega,by omega,?_,fun b hb => ?_⟩
    · rw [h.widths]
      have num := h.number_lt c hc
      change pre.start+c.number < 2^w
      have same : pre.supplement=pre.start+pre.bound.cells := rfl
      omega
    · exact (raw b hb).trans (by omega)
  · obtain ⟨p,r,d⟩ := ep
    refine ⟨?_,?_,d.trans room,?_⟩
    · exact h.initial ▸ p
    · exact h.initial ▸ r
    · omega

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
