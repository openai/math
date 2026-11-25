import OAI.Computability.BorderVNP.DiagonalTallyReportMemory

/-! # Consuming a real retained-site header and its delivered private payload -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open VPVNP.BurstRAM RoutingISA DiagonalTallyBits TallySidecar Packing.BottomReports

/-- Registers with fixed input data throughout the cell traversal. -/
def stableRegs : List Reg := [2,3,9,10,11,12,17,23]

/-- The layout-wide input registers remain available across native fragments that do not write them. -/
theorem ReportLayout.stable_after {w : ℕ} (l : ReportLayout) {pub : Arg → Word w}
    {mac : TeamOpcode.Macros w 8} {c : Code} {s m es t mt} (r : Runs pub mac c s m es t mt)
    (hs : l.stable (readings s)) (kept : stableRegs.all c.keeps=true) : l.stable (readings t) := by
  have eq (j : Reg) (hj : j∈stableRegs) : readings t j=readings s j :=
    congrArg Fin.val (r.keepsReg ((List.all_eq_true.mp kept) j hj))
  simpa only [ReportLayout.stable,eq 2 (by decide),eq 3 (by decide),eq 9 (by decide),eq 10 (by decide),
    eq 11 (by decide),eq 12 (by decide),eq 17 (by decide),eq 23 (by decide)] using hs

/-- Explicit tick allowance charged to one source description and its actual weighted copies. -/
def ReportBundle.cost (b : ReportBundle) (l : ReportLayout) (q : LocalReportCursor) :=
  enterBundle.slots + (TallySidecar.headerSetup.slots+DiagonalTallyBits.ticks 1 l.fieldWidth+rowsSetup.slots+
  DiagonalTallyBits.ticks (3*b.positions.length) l.fieldWidth + (28*b.positions.length+23)+
  (b.frame l q.toReportCursor q.external).cost .unary+advancePacked.slots)

/-- One whole bundle iteration consumes the genuine six-word geometry row and opaque site
string. The next cursor state and numerical memory image contain no predicted reads. -/
theorem ReportBundle.runs {w : ℕ} (b : ReportBundle) (l : ReportLayout) (q : LocalReportCursor)
    (p stop description : ℕ) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    (ready : q.ready l p stop (readings s)) (input : b.Input (w := w) l q p description (readings m)) :
    ∃ es t mt, Runs pub mac bundleReports s m es t mt ∧ traceCost es ≤ b.cost l q ∧
      (q.advance b).ready l (p+6) stop (readings t) ∧ readings mt=b.image l q (readings m) := by
  obtain ⟨stable,loaded,ptr,stopReg,ext,priv,supp,rows⟩ := ready
  obtain ⟨ctrl,tab,params,gadgets,width,zero,H,skip⟩ := stable
  obtain ⟨packed,descs,refs,prior⟩ := loaded
  have data := input.descriptionRoom
  have rawEnd := input.rawEnd
  obtain ⟨a,t₁,r₁,c₁,next,site,copies,base,stride,cap,orig⟩ :=
    enterBundle_runs pub mac s m b.header p _ ptr skip input.headerEnd (by omega) input.header
  let f := b.frame l q.toReportCursor q.external
  let g := b.header.writer q.packed q.privateUse q.supplement q.previousRows
  have keep (j : Reg) (hj : enterBundle.keeps j=true) : readings t₁ j=readings s j :=
    congrArg Fin.val (r₁.keepsReg hj)
  have lf : f.Loaded (readings t₁) := ⟨(keep 9 (by decide)).trans params,(keep 10 (by decide)).trans gadgets,
    (keep 11 (by decide)).trans width,(keep 12 (by decide)).trans zero,(keep 20 (by decide)).trans packed,
    copies,(keep 22 (by decide)).trans ext,(keep 30 (by decide)).trans descs,(keep 31 (by decide)).trans refs,
    (keep 32 (by decide)).trans prior⟩
  have lg : g.loaded (.ofWords t₁ m) := ⟨⟨orig,(keep 20 (by decide)).trans packed,copies,base,stride,cap⟩,
    (keep 24 (by decide)).trans priv,(keep 28 (by decide)).trans supp,(keep 29 (by decide)).trans rows⟩
  have raw := delivered_words m b.header.siteSlot l.fieldWidth l.bodyCap b.factors b.positions
    input.bodyRoom input.descriptionRoom input.received
  have len := bits_length l.fieldWidth b.positions
  have rawRoom : b.header.siteSlot+l.fieldWidth+l.bodyCap+(1+3*b.positions.length)*l.fieldWidth<2^w := by
    rw [← Nat.mul_comm,← len]; omega
  have sideRoom := input.operandFit.sideEnd
  change q.packed+1+3*b.positions.length<2^w at sideRoom
  have apart := input.rawPacked
  have rawSep : b.header.siteSlot+l.fieldWidth+l.bodyCap+(1+3*b.positions.length)*l.fieldWidth ≤ q.packed ∨
      q.packed+(1+3*b.positions.length) ≤ b.header.siteSlot+l.fieldWidth+l.bodyCap := by
    rw [← Nat.mul_comm,← len]; omega
  obtain ⟨e,t,mt,r₂,c₂,img,post⟩ := bundleKernel_runs pub mac t₁ m f g _ _ b.positions b.relative lf lg
    input.operandFit input.rowFit rfl (by simpa [Nat.add_assoc] using site) ((keep 17 (by decide)).trans H)
    input.width rawRoom (by change q.packed+(1+3*b.positions.length)<2^w; omega)
    rawSep
    input.values raw (fun i hi => by simp [ReportBundle.relative,List.getElem?_eq_getElem hi])
    input.outputAfter.1 input.outputAfter.2
  have run := r₁.seq r₂
  refine ⟨_,t,mt,run,?_,?_,?_⟩
  · rw [show traceCost (a++e)=traceCost a+traceCost e from VPVNP.RAMBuckets.cost_append ..]
    exact Nat.add_le_add c₁ c₂
  · refine ⟨l.stable_after run ⟨ctrl,tab,params,gadgets,width,zero,H,skip⟩ (by decide),
      ⟨post.packed,post.descriptors,post.refs,post.operands⟩,?_,?_,post.external,
      post.privateUse,post.supplement,post.supplementCount⟩
    · exact (congrArg Fin.val (r₂.keepsReg (by decide))).trans next
    · exact (congrArg Fin.val (run.keepsReg (by decide))).trans stopReg
  · rw [img]
    unfold bundleImage ReportBundle.image
    rw [packed_readings _ _ _ _ input.width input.values]
    rfl

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
