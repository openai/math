import OAI.Computability.BorderVNP.DiagonalTallyReportChoices

/-! # Exhausting every native path of the sparse cell report preparation -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open VPVNP.BurstRAM RoutingISA DiagonalResidueRAM

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
/-- Every terminating native path has exactly the prescribed shape of choices, writes
the count and use bits from that very tape, and pays the sparse stage clock. The
arithmetic input condition is evaluated for each possible report tape. -/
theorem prepareCellReports_cover {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (l : ReportLayout) (cs : List (ReportCell l)) (q : ReportCursor)
    (description : ℕ) (fp : (pub 0).val=l.frame) (zero : q.prior=0)
    (seed : l.seed q cs.length (readings m)) (frame : l.frame+95<2^w) (ctl : l.control+27<2^w)
    (headerRoom : l.headers+6*cs.length<2^w) (raw : l.fieldWidth+l.bodyCap<2^w)
    (input : ∀ a : ℕ → Bool, cellInputs w description (tapeCells a 0 cs) q l.headers (readings m))
    {es t mt} (run : Runs pub mac prepareCellReports s m es t mt) :
    ∃ a : ℕ → Bool, let rows := tapeCells a 0 cs
      TraceOK es (reportBits rows) es.length ∧
      traceCost es ≤ prepareSetup.slots+cellTicks rows q+(writeFrame 32 60 61 35).slots ∧
      readings mt=Function.update (cellImages rows q (readings m)) (l.frame+35) (cellOperands rows q).length := by
  let n := (reportBits cs).length
  let stream := es.flatMap TeamRAM.Event.choices++List.replicate n false
  let a : ℕ → Bool := fun i => stream[i]?.getD false
  have long : n ≤ stream.length := by simp [stream]
  have exactBits : reportBits (tapeCells a 0 cs)=stream.take n := by
    rw [tapeCells_bits]
    apply List.ext_getElem
    · simp [reportSlice,n,long]
    · intro i hi hj
      have fit : i<stream.length := by simp [reportSlice] at hi; omega
      simp [reportSlice,a,fit]
  obtain ⟨fs,u,mu,r,tr,cost,mem⟩ := prepareCellReports_runs pub mac s m l (tapeCells a 0 cs) q description
    fp zero (by simpa using seed) frame ctl (by simpa using headerRoom) raw (input a)
  have same : es.flatMap TeamRAM.Event.choices++List.replicate n false=fs.flatMap TeamRAM.Event.choices++stream.drop n := by
    rw [tr.2.1,exactBits,List.take_append_drop]
  obtain ⟨rfl,_,rfl⟩ := unique_returns (c := prepareCellReports) (by decide) run r same
  exact ⟨a,tr,cost,mem⟩

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
