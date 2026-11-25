import OAI.Computability.BorderVNP.DiagonalTallyReportModel

/-! # Native reads of the six-word cell and bottom-bundle headers -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open VPVNP.BurstRAM RoutingISA Packing.BottomReports

/-- The invariant frame-wide operands of the two nested scans. -/
def ReportLayout.stable (l : ReportLayout) (r : Reg → ℕ) : Prop :=
  r 2=l.control ∧ r 3=l.bundleTable ∧ r 9=l.parameters ∧ r 10=l.gadgets ∧
  r 11=l.countWidth ∧ r 12=l.zeroAddr ∧ r 17=l.fieldWidth ∧ r 23=l.fieldWidth+l.bodyCap

/-- The four output cursors at the beginning of a cell or bundle. -/
def ReportCursor.loaded (q : ReportCursor) (r : Reg → ℕ) : Prop :=
  r 20=q.packed ∧ r 30=q.descriptors ∧ r 31=q.refs ∧ r 32=q.prior

/-- The independently populated common directory and sparse-writer control scalars. -/
def ReportLayout.seed (l : ReportLayout) (q : ReportCursor) (owned : ℕ) (m : ℕ → ℕ) : Prop :=
  m (l.frame+92)=l.control ∧ m (l.frame+90)=owned ∧ m (l.frame+95)=l.parameters ∧
  m (l.frame+81)=l.zeroAddr ∧ m (l.frame+44)=q.descriptors ∧
  m (l.control+17)=l.headers ∧ m (l.control+19)=l.bundleTable ∧
  m (l.control+22)=l.countWidth ∧ m (l.control+23)=l.fieldWidth ∧ m (l.control+24)=l.bodyCap ∧
  m (l.control+25)=q.packed ∧ m (l.control+26)=q.refs ∧ m (l.control+27)=l.gadgets

/-- The compact header traversal starts with zero prior cell operands. -/
theorem prepareSetup_runs {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w)
    (m : Memory w) (l : ReportLayout) (q : ReportCursor) (owned : ℕ) (fp : (pub 0).val=l.frame)
    (zero : q.prior=0) (seed : l.seed q owned (readings m))
    (frame : l.frame+95<2^w) (ctl : l.control+27<2^w) (data : l.headers+6*owned<2^w)
    (raw : l.fieldWidth+l.bodyCap<2^w) :
    ∃ es t, Runs pub mac prepareSetup s m es t m ∧ traceCost es ≤ prepareSetup.slots ∧
      l.stable (readings t) ∧ q.loaded (readings t) ∧
      (t 0).val=l.headers ∧ (t 1).val=l.headers+6*owned := by
  obtain ⟨ctrl,num,pars,zaddr,desc,heads,bundles,hc,field,body,packed,refs,u⟩ := seed
  simp only [readings] at ctrl num pars zaddr desc heads bundles hc field body packed refs u
  have safe : prepareSetup.safeReadOnly w (readings pub) (readings m) (readings s) := by
    simp (config := {decide := true}) [prepareSetup,readControl,readFrame,Code.block,Code.safeReadOnly,
      Code.evalNat,Function.update,addressOpFits,addressOp,readings,fp,ctrl,num,heads,field,body]
    omega
  obtain ⟨es,t,r,cost,eq⟩ := prepareSetup.runReadOnly pub mac m s safe
  refine ⟨es,t,r,cost,?_⟩
  change l.stable (readings t) ∧ q.loaded (readings t) ∧ readings t 0=_ ∧ readings t 1=_
  rw [eq]
  simp (config := {decide := true}) [prepareSetup,readControl,readFrame,Code.block,Code.evalNat,
    Function.update,addressOp,readings,fp,ctrl,num,pars,zaddr,desc,heads,bundles,hc,field,body,packed,
    refs,u,ReportLayout.stable,ReportCursor.loaded,zero,Nat.mul_comm 6]

/-- Local cursors immediately after reading the genuine owned header. -/
def ReportCell.entered {l : ReportLayout} (c : ReportCell l) (p : ℕ) (r : Reg → ℕ) : Prop :=
  r 0=p+6 ∧ r 7=c.number ∧ r 4=c.external+c.supplied ∧ r 15=c.privateWires ∧
  r 5=l.bundleTable+6*c.first ∧ r 6=l.bundleTable+6*(c.first+c.bundles.length) ∧
  r 22=c.external+c.supplied ∧ r 24=c.privateWires+c.supplied+l.gadgets*l.countWidth ∧
  r 8=l.supplement+c.number*l.supplementStride ∧ r 28=l.supplement+c.number*l.supplementStride ∧
  r 29=0 ∧ r 21=0

/-- All header arithmetic and native array cursors fit in this cell. -/
def ReportCell.headerFits {l : ReportLayout} (c : ReportCell l) (p w : ℕ) : Prop :=
  l.control+13<2^w ∧ p+6<2^w ∧ c.external+c.supplied<2^w ∧
  c.privateWires+c.supplied+l.gadgets*l.countWidth<2^w ∧
  l.bundleTable+6*(c.first+c.bundles.length)<2^w ∧ l.supplement+c.number*l.supplementStride<2^w

/-- Reading the actual compact row, without consulting the later typed task's extent,
provides the canonical private and external addresses for its own supplement. -/
theorem enterCell_runs {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w)
    (m : Memory w) (l : ReportLayout) (c : ReportCell l) (p : ℕ)
    (hp : (s 0).val=p) (hs : l.stable (readings s)) (fit : c.headerFits p w)
    (supp : (m (l.control+12)).val=l.supplement) (stride : (m (l.control+13)).val=l.supplementStride)
    (row : CellPacket.WordsAt (readings m) p c.headerWords) :
    ∃ es t, Runs pub mac enterCell s m es t m ∧ traceCost es ≤ enterCell.slots ∧ c.entered p (readings t) := by
  obtain ⟨ctl,btable,_,u,Hc,_,_,_⟩ := hs
  simp only [readings] at ctl btable u Hc
  obtain ⟨hctl,hend,hext,hprivate,hpast,hsupp⟩ := fit
  have r0 := row ⟨0,by simp [ReportCell.headerWords]⟩
  have r1 := row ⟨1,by simp [ReportCell.headerWords]⟩
  have r2 := row ⟨2,by simp [ReportCell.headerWords]⟩
  have r3 := row ⟨3,by simp [ReportCell.headerWords]⟩
  have r4 := row ⟨4,by simp [ReportCell.headerWords]⟩
  have r5 := row ⟨5,by simp [ReportCell.headerWords]⟩
  simp [ReportCell.headerWords,readings] at r0 r1 r2 r3 r4 r5
  have hw : w≠0 := by rintro rfl; simp at hend
  have safe : enterCell.safeReadOnly w (readings pub) (readings m) (readings s) := by
    simp (config := {decide := true}) [enterCell,consume,readControl,Code.block,Code.safeReadOnly,Code.evalNat,
      Function.update,addressOpFits,addressOp,readings,hp,ctl,btable,u,Hc,r0,r1,r2,r3,r4,r5,supp,stride,hw,
      Nat.add_assoc,Nat.mul_comm _ 6]
    omega
  obtain ⟨es,t,r,cost,eq⟩ := enterCell.runReadOnly pub mac m s safe
  refine ⟨es,t,r,cost,?_⟩
  rw [eq]
  simp (config := {decide := true}) [ReportCell.entered,enterCell,consume,readControl,Code.block,Code.evalNat,
    Function.update,addressOp,readings,hp,ctl,btable,u,Hc,r0,r1,r2,r3,r4,r5,supp,stride,Nat.add_assoc,
    Nat.mul_comm _ 6]

/-- The public six-word bundle row supplies exactly the addresses and dimensions used by the
private row writer. Its sidecar is at the fixed offset from the *delivered* site address. -/
theorem enterBundle_runs {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w)
    (m : Memory w) (b : BundleHeader) (p skip : ℕ) (hp : (s 5).val=p) (hs : (s 23).val=skip)
    (hend : p+6<2^w) (hraw : b.siteSlot+skip<2^w) (row : CellPacket.WordsAt (readings m) p b.words) :
    ∃ es t, Runs pub mac enterBundle s m es t m ∧ traceCost es ≤ enterBundle.slots ∧
      (t 5).val=p+6 ∧ (t 16).val=b.siteSlot+skip ∧ (t 21).val=b.copies ∧
      (t 25).val=b.boxBase ∧ (t 26).val=b.stride ∧ (t 27).val=b.cap ∧ (t 19).val=b.orig := by
  have r0 := row ⟨0,by simp [BundleHeader.words]⟩
  have r1 := row ⟨1,by simp [BundleHeader.words]⟩
  have r2 := row ⟨2,by simp [BundleHeader.words]⟩
  have r3 := row ⟨3,by simp [BundleHeader.words]⟩
  have r4 := row ⟨4,by simp [BundleHeader.words]⟩
  have r5 := row ⟨5,by simp [BundleHeader.words]⟩
  simp [BundleHeader.words,readings] at r0 r1 r2 r3 r4 r5
  have hw : w≠0 := by rintro rfl; simp at hend
  have safe : enterBundle.safeReadOnly w (readings pub) (readings m) (readings s) := by
    simp [enterBundle,consume,Code.block,Code.safeReadOnly,Code.evalNat,Function.update,addressOpFits,addressOp,
      readings,hw,hp,hs,r0,Nat.add_assoc]; omega
  obtain ⟨es,t,r,cost,eq⟩ := enterBundle.runReadOnly pub mac m s safe
  refine ⟨es,t,r,cost,?_⟩
  change readings t 5=_ ∧ readings t 16=_ ∧ readings t 21=_ ∧ readings t 25=_ ∧
    readings t 26=_ ∧ readings t 27=_ ∧ readings t 19=_
  rw [eq]
  simp (config := {decide := true}) [enterBundle,consume,Code.block,Code.evalNat,Function.update,
    addressOp,readings,hp,hs,r0,r1,r2,r3,r4,r5,Nat.add_assoc]

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
