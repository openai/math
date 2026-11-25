import OAI.Computability.BorderVNP.DiagonalTallyReportCell

/-! # Complete native report preparation over the true owned-cell array -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open VPVNP.BurstRAM RoutingISA DiagonalResidueRAM

/-- Physical memory after preparing the actual owned cells, in their stable order. -/
def cellImages {l : ReportLayout} : List (ReportCell l) → ReportCursor → (ℕ → ℕ) → ℕ → ℕ
  | [],_,m => m
  | c::cs,q,m => cellImages cs (c.after q) (c.image q m)

/-- Numeric and address conditions on the actual chronological intermediate memory,
including every private site literal and the checker's supplemental arena. -/
def cellInputs {l : ReportLayout} (w description : ℕ) :
    List (ReportCell l) → ReportCursor → ℕ → (ℕ → ℕ) → Prop
  | [],_,_,_ => True
  | c::cs,q,p,m => c.Input q w p description m ∧ cellInputs w description cs (c.after q) (p+6) (c.image q m)

/-- Sum of the actual variable cell charges and loop tests. -/
def cellTicks {l : ReportLayout} : List (ReportCell l) → ReportCursor → ℕ
  | [],_ => 1
  | c::cs,q => 1+c.work q+cellTicks cs (c.after q)

/-- Chronological order of the private report-bit choices. -/
def reportBits {l : ReportLayout} (cs : List (ReportCell l)) : List Bool := cs.flatMap ReportCell.bits

/-- The descriptor pointer and count advance together over all weighted copies. -/
theorem bundleOperands_length (bs : List ReportBundle) (q : ReportCursor) (p : ℕ) :
    (bundleOperands bs q p).length=weightedCopies bs := by
  induction bs generalizing q p with
  | nil => rfl
  | cons b bs ih => simp [bundleOperands,weightedCopies,ih]

private theorem fold_prior (bs : List ReportBundle) (q : ReportCursor) :
    (bs.foldl ReportCursor.afterBundle q).prior=q.prior+weightedCopies bs := by
  induction bs generalizing q with
  | nil => simp [weightedCopies]
  | cons b bs ih => simp [List.foldl_cons,ih,ReportCursor.afterBundle,weightedCopies,Nat.add_assoc]

/-- Number of five-word descriptors at the end of one cell. -/
theorem ReportCell.after_prior {l : ReportLayout} (c : ReportCell l) (q : ReportCursor) :
    (c.after q).prior=q.prior+(c.operands q).length := by
  simp [after,fold_prior,operands,ReportCursor.afterCounts,bundleOperands_length,Nat.add_assoc,countFrame]

/-- The aggregate count passed in frame slot 35 is the true emitted list length. -/
theorem cellOperands_count {l : ReportLayout} (cs : List (ReportCell l)) (q : ReportCursor) :
    (cs.foldl (fun a c => c.after a) q).prior=q.prior+(cellOperands cs q).length := by
  induction cs generalizing q with
  | nil => simp [cellOperands]
  | cons c cs ih => simp [cellOperands,List.foldl_cons,ih,c.after_prior,Nat.add_assoc]

private theorem cells_run {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (l : ReportLayout) (cs : List (ReportCell l)) (q : ReportCursor) (p description : ℕ) (s : Bank w) (m : Memory w)
    (stable : l.stable (readings s)) (loaded : q.loaded (readings s)) (ptr : (s 0).val=p)
    (stop : (s 1).val=p+6*cs.length) (input : cellInputs w description cs q p (readings m)) :
    ∃ es t mt, Runs pub mac (.whileLt 0 1 cellReports) s m es t mt ∧ TraceOK es (reportBits cs) es.length ∧
      traceCost es ≤ cellTicks cs q ∧ (cs.foldl (fun a c => c.after a) q).loaded (readings t) ∧
      readings mt=cellImages cs q (readings m) := by
  induction cs generalizing q p s m with
  | nil =>
    simp only [List.length_nil,Nat.mul_zero,Nat.add_zero] at stop
    have guard : ¬s 0<s 1 := by change ¬(s 0).val<(s 1).val; rw [ptr,stop]; omega
    exact ⟨_,s,m,.whileDone guard,by simp [TraceOK,tick,reportBits],
      by simp [cellTicks,traceCost,tick,VPVNP.RAMBuckets.cost,TeamTranscript.Action.extra],loaded,rfl⟩
  | cons c cs ih =>
    have endAddr : p+6*(c::cs).length=(p+6)+6*cs.length := by simp; omega
    have guard : s 0<s 1 := by change (s 0).val<(s 1).val; rw [ptr,stop,endAddr]; omega
    obtain ⟨a,u,mu,r₁,tr₁,c₁,st,ld,p',m₁⟩ := c.runs pub mac s m l q p description stable loaded ptr input.1
    have stp : (u 1).val=(p+6)+6*cs.length := (congrArg Fin.val (r₁.keepsReg (by decide))).trans (stop.trans endAddr)
    obtain ⟨b,t,mt,r₂,tr₂,c₂,final,image⟩ := ih (c.after q) (p+6) u mu st ld p' stp (m₁ ▸ input.2)
    refine ⟨_,t,mt,.whileStep guard r₁ r₂,?_,?_,final,?_⟩
    · simpa only [reportBits,List.flatMap_cons,List.length_cons,List.length_append] using (tr₁.append tr₂).cons_tick
    · change 1+traceCost (a++b) ≤ 1+c.work q+cellTicks cs (c.after q)
      rw [show traceCost (a++b)=traceCost a+traceCost b from VPVNP.RAMBuckets.cost_append ..]; omega
    · rw [image,m₁,cellImages]

/-- The actual pre-call owner traversal installs the true operand count and every physically
addressed report bit, private checker binding and tally descriptor. Only the represented
cell bits are guessed. All arithmetic and delivery preconditions refer to real input words
and the explicitly given intermediate memory writes. -/
theorem prepareCellReports_runs {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (l : ReportLayout) (cs : List (ReportCell l)) (q : ReportCursor)
    (description : ℕ) (fp : (pub 0).val=l.frame) (zero : q.prior=0)
    (seed : l.seed q cs.length (readings m)) (frame : l.frame+95<2^w) (ctl : l.control+27<2^w)
    (headerRoom : l.headers+6*cs.length<2^w) (raw : l.fieldWidth+l.bodyCap<2^w)
    (input : cellInputs w description cs q l.headers (readings m)) :
    ∃ es t mt, Runs pub mac prepareCellReports s m es t mt ∧ TraceOK es (reportBits cs) es.length ∧
      traceCost es ≤ prepareSetup.slots+cellTicks cs q+(writeFrame 32 60 61 35).slots ∧
      readings mt=Function.update (cellImages cs q (readings m)) (l.frame+35) (cellOperands cs q).length := by
  obtain ⟨a,u,r₁,c₁,st,ld,ptr,stop⟩ := prepareSetup_runs pub mac s m l q cs.length fp zero seed frame ctl headerRoom raw
  obtain ⟨b,y,my,r₂,tr₂,c₂,final,img⟩ := cells_run pub mac l cs q l.headers description u m st ld ptr stop input
  let z := NatState.ofWords y my
  have count : z.reg 32=(cellOperands cs q).length := by
    have he := final.2.2.2
    change readings y 32=(cellOperands cs q).length
    simpa [cellOperands_count,zero] using he
  have safe : (writeFrame 32 60 61 35).fixedSafe w (readings pub) z := by
    simp [writeFrame,Code.block,Code.fixedSafe,Code.fixedEval,Code.safeReadOnly,Code.evalNat,
      Function.update,addressOpFits,readings,fp]; omega
  obtain ⟨d,t,mt,r₃,c₃,e₃⟩ := (writeFrame 32 60 61 35).runFixed pub mac y my safe
  have plain {code : Code} {s₀ m₀ xs s₁ m₁} (r : Runs pub mac code s₀ m₀ xs s₁ m₁) (h : code.unsigned=true) :
      TraceOK xs [] xs.length :=
    ⟨rfl,List.flatMap_eq_nil_iff.mpr fun e he => (r.unsigned_events h e he).1,fun e he => (r.unsigned_events h e he).2⟩
  refine ⟨_,t,mt,r₁.seq (r₂.seq r₃),?_,?_,?_⟩
  · simpa only [List.length_append,List.nil_append,List.append_nil] using
      (plain r₁ (by decide)).append (tr₂.append (plain r₃ (by decide)))
  · unfold traceCost
    simp only [VPVNP.RAMBuckets.cost_append]
    change traceCost a+(traceCost b+traceCost d) ≤ _
    omega
  · have he := congrArg NatState.mem e₃
    change readings mt=((writeFrame 32 60 61 35).fixedEval (readings pub) z).mem at he
    rw [he]
    have hm : z.mem=cellImages cs q (readings m) := img
    simp [writeFrame,Code.block,Code.fixedEval,Code.evalNat,Function.update,addressOp,readings,fp,count,hm]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
/-- Once the actual report stream is fixed, two native returns are identical in every
event, register and shared-memory word, including all original load/store histories. -/
theorem prepareCellReports_unique {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {s m a t mt b u mu} (ra : Runs pub mac prepareCellReports s m a t mt)
    (rb : Runs pub mac prepareCellReports s m b u mu)
    (choice : a.flatMap TeamRAM.Event.choices=b.flatMap TeamRAM.Event.choices) :
    a=b ∧ t=u ∧ mt=mu :=
  unique_returns (c := prepareCellReports) (by decide) ra rb
    (tail := []) (tail' := []) (by simpa using choice)

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
