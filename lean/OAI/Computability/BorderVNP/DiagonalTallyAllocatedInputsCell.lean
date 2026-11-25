import OAI.Computability.BorderVNP.DiagonalTallyAllocatedInputsBundle
import OAI.Computability.BorderVNP.DiagonalTallyReportRanges

/-! # Persistence of the true grouped headers and opaque sites across owned cells -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open RoutingISA Packing.BottomReports

/-- The per-cell read controls installed in the original frame-92 directory. -/
structure ReportLayout.ScannerControls (l : ReportLayout) (m : ℕ → ℕ) : Prop where
  supplement : m (l.control+12)=l.supplement
  stride : m (l.control+13)=l.supplementStride
  counters : m (l.control+14)=l.counters
  widths : m (l.control+7)=l.tailWidths

/-- Original grouped six-word rows and the literal one-copy private strings. -/
structure ReportCell.Received {l : ReportLayout} (c : ReportCell l) (w description : ℕ) (m : ℕ → ℕ) : Prop where
  headers : CellPacket.WordsAt m (l.bundleTable+6*c.first) (c.bundles.flatMap fun b => b.header.words)
  sites : ∀ b ∈ c.bundles, b.delivered l description m ∧ b.SiteRoom l w description

/-- Bounds on an individual global cell's actual private assignment and public arenas.
All these refer to the static input, before traversing any owned cell. -/
structure ReportCell.ScanRoom {l : ReportLayout} (c : ReportCell l) (w description packed : ℕ) : Prop where
  bundleEnd : l.bundleTable+6*(c.first+c.bundles.length)<2^w
  external : c.external+c.supplied+c.tailWidth<2^w
  privateWires : c.privateWires+c.supplied+c.tailWidth<2^w
  supplement : l.supplement+c.number*l.supplementStride+supplementWords c.bundles ≤ packed
  counterEnd : l.counters+2*c.number+1 < 2^w
  widthEnd : l.tailWidths+c.number < 2^w
  sites : ∀ b ∈ c.bundles, b.header.siteSlot+description ≤ packed

/-- Terminal cursors in the three global scratch streams. -/
structure CellScanRoom {l : ReportLayout} (cs : List (ReportCell l)) (q : ReportCursor) (w : ℕ) : Prop where
  packed : (cs.foldl (fun a c => c.after a) q).packed < q.refs
  refs : (cs.foldl (fun a c => c.after a) q).refs < q.descriptors
  descriptors : (cs.foldl (fun a c => c.after a) q).descriptors < 2^w
  prior : (cs.foldl (fun a c => c.after a) q).prior < 2^w

private theorem private_fold (bs : List ReportBundle) (q : LocalReportCursor) :
    (bs.foldl LocalReportCursor.advance q).privateUse=q.privateUse+weightedCopies bs := by
  induction bs generalizing q with
  | nil => simp [weightedCopies]
  | cons b bs ih => simp [ih,LocalReportCursor.advance,weightedCopies,Nat.add_assoc]

private theorem rows_fold_le (bs : List ReportBundle) (q : LocalReportCursor) (h : q.previousRows ≤ q.supplement) :
    (bs.foldl LocalReportCursor.advance q).previousRows ≤ (bs.foldl LocalReportCursor.advance q).supplement := by
  induction bs generalizing q with
  | nil => exact h
  | cons b bs ih => exact ih (q.advance b) (by simp only [LocalReportCursor.advance]; omega)

/-- Every native scanner input at its actual chronological memory image is determined by
the original owned rows, grouped bundle headers, private receipts and address reservations. -/
theorem cellInputs_of_received {l : ReportLayout} (cs : List (ReportCell l)) (q : ReportCursor)
    (w description p : ℕ) (original m : ℕ → ℕ) (live : ℕ → Prop)
    (read : ∀ a, live a → m a=original a) (clear : ReportReadsClear live (cellWrites cs q))
    (headers : CellPacket.WordsAt original p (cs.flatMap ReportCell.headerWords))
    (headerLive : ∀ i < 6*cs.length, live (p+i))
    (received : ∀ c ∈ cs, c.Received w description original)
    (sourceLive : ∀ c ∈ cs, (∀ i < 6*c.bundles.length, live (l.bundleTable+6*c.first+i)) ∧
      ∀ b ∈ c.bundles, ∀ j : Fin description, live (b.header.siteSlot+j.val))
    (controls : l.ScannerControls original) (ctlLive : ∀ j < 28, live (l.control+j))
    (controlEnd : l.control+27<2^w) (belowCounters : l.control+27<l.counters)
    (width : l.fieldWidth ≤ w) (coords : l.parameters+l.gadgets < 2^w)
    (headEnd : p+6*cs.length<2^w) (cellRoom : ∀ c ∈ cs, c.ScanRoom w description q.packed)
    (room : CellScanRoom cs q w) : cellInputs w description cs q p m := by
  induction cs generalizing q p m with
  | nil => trivial
  | cons c cs ih =>
    let e := cs.foldl (fun a c => c.after a) (c.after q)
    obtain ⟨ep,er,ed,en⟩ := room
    change e.packed < q.refs at ep
    change e.refs < q.descriptors at er
    change e.descriptors < 2^w at ed
    change e.prior < 2^w at en
    obtain ⟨dp,dr,dd⟩ := cell_after_fields c q
    obtain ⟨tep,ter,ted⟩ := cells_fold_fields cs (c.after q)
    have ten := cellOperands_count cs (c.after q)
    change e.packed=_ at tep
    change e.refs=_ at ter
    change e.descriptors=_ at ted
    change e.prior=_ at ten
    have cn : (c.after q).prior=q.prior+l.gadgets+weightedCopies c.bundles := by
      simp [c.after_prior,ReportCell.operands,bundleOperands_length,ReportCell.countFrame,Nat.add_assoc]
    have hlocal := c.global_end q
    have hpack := congrArg ReportCursor.packed hlocal
    have href := congrArg ReportCursor.refs hlocal
    have hdesc := congrArg ReportCursor.descriptors hlocal
    have hprior := congrArg ReportCursor.prior hlocal
    obtain ⟨_,_,_,hsupp⟩ := bundle_fold_fields c.bundles (c.localStart q)
    change (c.localEnd q).supplement=l.supplement+c.number*l.supplementStride+supplementWords c.bundles at hsupp
    have hprivate := private_fold c.bundles (c.localStart q)
    change (c.localEnd q).privateUse=c.privateWires+c.supplied+l.gadgets*l.countWidth+weightedCopies c.bundles at hprivate
    have hrows := rows_fold_le c.bundles (c.localStart q) (Nat.zero_le _)
    change (c.localEnd q).previousRows ≤ (c.localEnd q).supplement at hrows
    have ext := c.external_end q
    have tail : c.tailWidth=l.gadgets*l.countWidth+weightedCopies c.bundles := rfl
    have g := cellRoom c List.mem_cons_self
    obtain ⟨bh,ex,pr,sup,ce,we,raw⟩ := g
    obtain ⟨rows,sites⟩ := received c List.mem_cons_self
    obtain ⟨bhLive,rawLive⟩ := sourceLive c List.mem_cons_self
    simp only [List.flatMap_cons] at headers
    simp only [List.length_cons,Nat.mul_succ] at headEnd headerLive
    have hc := clear.sublist (ss := c.writes q) (fun _ h => List.mem_append_left _ h)
    have hprefix := hc.sublist (ss := operandWrites (c.countFrame q) .count ++
        bundleWrites l c.bundles (c.localStart q)) (fun _ h => List.mem_append_left _ h)
    have hcount := hprefix.sublist (ss := operandWrites (c.countFrame q) .count)
      (fun _ h => List.mem_append_left _ h)
    have countRead (a : ℕ) (ha : live a) : (c.countFrame q).image .count m a=original a := by
      rw [operandWrites_image,hcount.read _ ha,read a ha]
    have prefixRead (j : ℕ) (hj : j<28) : c.prefixImage q m (l.control+j)=original (l.control+j) := by
      rw [ReportCell.prefixImage,bundleWrites_image,operandWrites_image]
      rw [← show ∀ x y, applyWrites m (x ++ y)=applyWrites (applyWrites m x) y from
        fun x y => by simp [applyWrites,List.foldl_append]]
      rw [hprefix.read _ (ctlLive j hj),read _ (ctlLive j hj)]
    refine ⟨⟨?_,?_⟩,?_⟩
    · refine ⟨?_,?_,?_,?_,?_⟩
      · intro i
        rw [read _ (headerLive i.val (by have h : i.val<6 := i.isLt; omega))]
        exact headers.left i
      · unfold ReportCell.headerFits
        omega
      · rw [read _ (ctlLive 12 (by decide)),read _ (ctlLive 13 (by decide))]
        exact ⟨controls.supplement,controls.stride⟩
      · constructor
        all_goals try simp only [ReportCell.countFrame,DiagonalTallyOperandArray.Frame.nrefs,
          DiagonalTallyOperandArray.Frame.nrows,Nat.mul_zero,Nat.add_zero]
        all_goals omega
      · apply bundleInputs_of_received w l description c.bundles (c.localStart q) _ original _ live countRead
          (hprefix.sublist (fun _ h => List.mem_append_right _ h)) rows bhLive
          (fun b hb => ⟨(sites b hb).1,(sites b hb).2,raw b hb,rawLive b hb⟩) width coords (by omega)
        constructor
        · change (c.localEnd q).packed < q.refs+l.gadgets*l.countWidth
          omega
        · change (c.localEnd q).refs < q.descriptors+5*l.gadgets
          omega
        · change (c.localEnd q).descriptors < 2^w
          omega
        · change (c.localEnd q).prior < 2^w
          omega
        · change (c.localEnd q).external < 2^w
          omega
        · change (c.localEnd q).privateUse < 2^w
          omega
        · change (c.localEnd q).supplement ≤ q.packed
          omega
        · change (c.localEnd q).previousRows < 2^w
          omega
    · refine ⟨(prefixRead 14 (by decide)).trans controls.counters,(prefixRead 7 (by decide)).trans controls.widths,
        by omega,ce,we,by omega,by omega,by omega,by omega⟩
    · apply ih (c.after q) (p+6) (c.image q m)
      · intro a ha
        rw [c.writes_image,hc.read _ ha,read _ ha]
      · exact clear.sublist (fun _ h => List.mem_append_right _ h)
      · exact headers.right
      · intro i hi
        simpa only [Nat.add_assoc] using headerLive (6+i) (by omega)
      · exact fun d hd => received d (.tail _ hd)
      · exact fun d hd => sourceLive d (.tail _ hd)
      · omega
      · intro d hd
        obtain ⟨bh',ex',pr',su',ce',we',raw'⟩ := cellRoom d (.tail _ hd)
        exact ⟨bh',ex',pr',by omega,ce',we',fun b hb => (raw' b hb).trans (by omega)⟩
      · exact ⟨by change e.packed < (c.after q).refs; omega,by change e.refs < (c.after q).descriptors; omega,ed,en⟩

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
