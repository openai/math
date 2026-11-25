import OAI.Computability.BorderVNP.DiagonalTallyReportBundleLoop

/-! # Preparing all actual descriptors before sampling the owned cell's reports -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open VPVNP.BurstRAM RoutingISA DiagonalTallyOperandArray

/-- The physical local state after emitting the fixed gadget count descriptors. -/
def ReportCell.localStart {l : ReportLayout} (c : ReportCell l) (q : ReportCursor) : LocalReportCursor :=
  ⟨q.afterCounts l,c.external+c.supplied+l.gadgets*l.countWidth,
    c.privateWires+c.supplied+l.gadgets*l.countWidth,l.supplement+c.number*l.supplementStride,0⟩

/-- Exact terminal local cursors once all bundles of the cell have been visited. -/
def ReportCell.localEnd {l : ReportLayout} (c : ReportCell l) (q : ReportCursor) : LocalReportCursor :=
  c.bundles.foldl LocalReportCursor.advance (c.localStart q)

/-- Numeric effect of the two array writes for counts and every subsequent bundle write. -/
def ReportCell.prefixImage {l : ReportLayout} (c : ReportCell l) (q : ReportCursor) (m : ℕ → ℕ) :=
  bundleImages l c.bundles (c.localStart q) ((c.countFrame q).image .count m)

/-- Every live physical input of one owned cell, including the zero-bundle case. -/
structure ReportCell.PrefixInput {l : ReportLayout} (c : ReportCell l) (q : ReportCursor)
    (w p description : ℕ) (m : ℕ → ℕ) : Prop where
  /-- Public header emitted for this genuine owned cell. -/
  row : CellPacket.WordsAt m p c.headerWords
  /-- Header array and canonical count-and-use start addresses fit the machine word. -/
  headerFit : c.headerFits p w
  /-- The two actual public allocation controls used for its supplemental row stream. -/
  supplement : m (l.control+12)=l.supplement ∧ m (l.control+13)=l.supplementStride
  /-- The count pointer arrays and their updates fit. -/
  countFit : (c.countFrame q).Fits .count w
  /-- Genuine grouped physical inputs for the later bottom-bundle scan. -/
  bundles : bundleInputs w l description c.bundles (c.localStart q) (l.bundleTable+6*c.first)
    ((c.countFrame q).image .count m)

/-- Cursor state immediately before publishing the two counters and guessing the compact tail. -/
def ReportCell.prepared {l : ReportLayout} (c : ReportCell l) (q : ReportCursor) (p : ℕ) (r : Reg → ℕ) :=
  let endPtr := l.bundleTable+6*(c.first+c.bundles.length)
  (c.localEnd q).ready l endPtr endPtr r ∧ r 0=p+6 ∧ r 7=c.number ∧
    r 4=c.external+c.supplied ∧ r 8=l.supplement+c.number*l.supplementStride

/-- Tick cost of the count and variable-size use descriptor preparations in this cell. -/
def ReportCell.prefixCost {l : ReportLayout} (c : ReportCell l) (q : ReportCursor) :=
  enterCell.slots+(c.countFrame q).cost .count+bundleTicks l c.bundles (c.localStart q)

/-- Native execution of the complete owned-cell prefix, with the actual memory image and
end cursors used by the width publisher and outer branch guesses. -/
theorem ReportCell.prefix_runs {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (l : ReportLayout) (c : ReportCell l) (q : ReportCursor)
    (p description : ℕ) (hs : l.stable (readings s)) (hq : q.loaded (readings s))
    (cursor : (s 0).val=p) (input : c.PrefixInput q w p description (readings m)) :
    ∃ es t mt, Runs pub mac cellPrefix s m es t mt ∧ traceCost es ≤ c.prefixCost q ∧
      c.prepared q p (readings t) ∧ readings mt=c.prefixImage q (readings m) := by
  obtain ⟨a,t₁,r₁,c₁,enter⟩ := enterCell_runs pub mac s m l c p cursor hs input.headerFit
    input.supplement.1 input.supplement.2 input.row
  obtain ⟨step,number,start,_,first,last,ext,use,sbase,supp,rows,copies⟩ := enter
  have k₁ (j : Reg) (h : enterCell.keeps j=true) : readings t₁ j=readings s j := congrArg Fin.val (r₁.keepsReg h)
  have st₁ := l.stable_after r₁ hs (by decide)
  obtain ⟨_,_,par,g,H,zero,_,_⟩ := st₁
  obtain ⟨pack,desc,refs,prior⟩ := hq
  let f := c.countFrame q
  have lf : f.Loaded (readings t₁) := ⟨par,g,H,zero,(k₁ 20 (by decide)).trans pack,copies,ext,
    (k₁ 30 (by decide)).trans desc,(k₁ 31 (by decide)).trans refs,(k₁ 32 (by decide)).trans prior⟩
  obtain ⟨b,t₂,m₂,r₂,c₂,mimg,ext₂,desc₂,ref₂,prior₂⟩ := writer_runs f .count pub mac t₁ m lf input.countFit trivial
  have k₂ (j : Reg) (h : (writer .count).keeps j=true) : readings t₂ j=readings t₁ j :=
    congrArg Fin.val (r₂.keepsReg h)
  have stop : l.bundleTable+6*(c.first+c.bundles.length)=(l.bundleTable+6*c.first)+6*c.bundles.length := by omega
  have ready : (c.localStart q).ready l (l.bundleTable+6*c.first)
      ((l.bundleTable+6*c.first)+6*c.bundles.length) (readings t₂) :=
    ⟨l.stable_after (r₁.seq r₂) hs (by decide),
    ⟨(k₂ 20 (by decide)).trans ((k₁ 20 (by decide)).trans pack),desc₂,ref₂,prior₂⟩,
    (k₂ 5 (by decide)).trans first,(k₂ 6 (by decide)).trans (last.trans stop),ext₂,
    (k₂ 24 (by decide)).trans use,(k₂ 28 (by decide)).trans supp,(k₂ 29 (by decide)).trans rows⟩
  obtain ⟨e,t,mt,r₃,c₃,ending,img⟩ := bundleLoop_runs pub mac l description c.bundles (c.localStart q)
    (l.bundleTable+6*c.first) t₂ m₂ ready (mimg ▸ input.bundles)
  have rest := r₂.seq r₃
  refine ⟨_,t,mt,r₁.seq rest,?_,?_,?_⟩
  · unfold traceCost
    simp only [VPVNP.RAMBuckets.cost_append]
    change traceCost a+(traceCost b+traceCost e) ≤ _
    rw [prefixCost,Nat.add_assoc]
    exact Nat.add_le_add c₁ (Nat.add_le_add c₂ c₃)
  · rw [← stop] at ending
    have k₃ (j : Reg) (h : (Code.seq (writer .count) (.whileLt 5 6 bundleReports)).keeps j=true) :
        readings t j=readings t₁ j := congrArg Fin.val (rest.keepsReg h)
    exact ⟨ending,(k₃ 0 (by decide)).trans step,(k₃ 7 (by decide)).trans number,
      (k₃ 4 (by decide)).trans start,(k₃ 8 (by decide)).trans sbase⟩
  · rw [img,mimg,ReportCell.prefixImage]

/-- The publisher derives the precise guess count by subtracting the physical first-bit
address from the advancing actual output cursor. -/
theorem ReportCell.external_end {l : ReportLayout} (c : ReportCell l) (q : ReportCursor) :
    (c.localEnd q).external=c.external+c.supplied+c.tailWidth := by
  rw [localEnd,local_fold_external]
  simp [localStart,tailWidth,Nat.add_assoc]

theorem ReportCell.global_end {l : ReportLayout} (c : ReportCell l) (q : ReportCursor) :
    (c.localEnd q).toReportCursor=c.after q := local_fold_global c.bundles (c.localStart q)

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
