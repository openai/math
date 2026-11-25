import OAI.Computability.BorderVNP.FiniteEvaluatorPrepareReportsRun
import OAI.Computability.BorderVNP.DiagonalTallyReportBatch

/-! # Complete traversal and exact tape replay of native finite report preparation -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.Reports

open VPVNP.BurstRAM RoutingISA DiagonalResidueRAM TeamRAM
open TeamContraction

/-- All memory updates, in true owned-row order. -/
def image (l : Layout) (rows : List Row) (m : ℕ → ℕ) := rows.foldl (fun mem row => row.image l mem) m

/-- The public three header reads and address bounds at their actual
chronological locations. The recursively computed memory is the preceding
row's explicit counter and bit image. -/
def Inputs (l : Layout) (w : ℕ) : List Row → ℕ → (ℕ → ℕ) → Prop
  | [],_,_ => True
  | r::rs,p,m => r.Stored p m ∧ r.Fits l w p ∧ Inputs l w rs (p+6) (r.image l m)

/-- All report guesses, and all deterministic work for exactly those rows. -/
def ticks : List Row → ℕ
  | [] => 1
  | r::rs => 1+(beginCell.slots+publish.slots+6*r.bits.length+6)+ticks rs

private theorem loop_run {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (l : Layout) (rows : List Row) (s : Bank w) (m : Memory w) (p : ℕ)
    (loaded : l.Loaded (readings s)) (ptr : (s 0).val=p) (stop : (s 1).val=p+6*rows.length)
    (inputs : Inputs l w rows p (readings m)) :
    ∃ es t mt, Runs pub mac (.whileLt 0 1 cell) s m es t mt ∧
      TraceOK es (rows.flatMap Row.bits) (ticks rows) ∧ traceCost es=ticks rows ∧ readings mt=image l rows (readings m) := by
  induction rows generalizing s m p with
  | nil =>
    have endLoop : ¬s 0<s 1 := by change ¬(s 0).val<(s 1).val; simp [ptr,stop]
    exact ⟨_,s,m,.whileDone endLoop,by simp [TraceOK,tick,ticks],
      by simp [traceCost,tick,ticks,VPVNP.RAMBuckets.cost,TeamTranscript.Action.extra],rfl⟩
  | cons r rs ih =>
    have advance : p+6*(r::rs).length=p+6+6*rs.length := by simp; omega
    have runLoop : s 0<s 1 := by change (s 0).val<(s 1).val; rw [ptr,stop,advance]; omega
    obtain ⟨es,u,mu,one,trace,cost,mem,pos,limit,keep⟩ :=
      cell_run pub mac s m l r p ptr loaded inputs.1 inputs.2.1
    obtain ⟨fs,t,mt,rest,tail,bound,final⟩ := ih u mu (p+6) keep pos (limit.trans (stop.trans advance)) (mem ▸ inputs.2.2)
    refine ⟨_,_,_,.whileStep runLoop one rest,?_,?_,?_⟩
    · rw [ticks,show 1+(beginCell.slots+publish.slots+6*r.bits.length+6)+ticks rs =
        (beginCell.slots+publish.slots+6*r.bits.length+6+ticks rs)+1 by omega]
      exact (trace.append tail).cons_tick
    · change 1+traceCost (es++fs)=_
      rw [show traceCost (es++fs)=traceCost es+traceCost fs from VPVNP.RAMBuckets.cost_append ..,cost,bound,ticks]
      omega
    · rw [final,mem]; rfl

/-- A complete native preparation for any chosen chronological field report
bits. The final image covers all report tails and all supplement counters,
and every prefix bit is consumed at its real owned-cell address. -/
theorem prepare_run {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    (l : Layout) (rows : List Row) (ptr : (pub 0).val=l.frame) (seed : l.Seed rows.length (readings m))
    (frame : l.frame+92 < 2^w) (control : l.control+27 < 2^w) (room : l.headers+6*rows.length < 2^w)
    (inputs : Inputs l w rows l.headers (readings m)) :
    ∃ es t mt, Runs pub mac prepareReports s m es t mt ∧ TraceOK es (rows.flatMap Row.bits) es.length ∧
      traceCost es ≤ setup.slots+ticks rows ∧ readings mt=image l rows (readings m) := by
  obtain ⟨as,u,init,head,hcost,loaded,pos,stop⟩ := setup_run pub mac s m l rows.length ptr seed frame control room
  obtain ⟨bs,t,mt,run,body,bcost,mem⟩ := loop_run pub mac l rows u m l.headers loaded pos stop inputs
  refine ⟨_,_,_,init.seq run,?_,?_,mem⟩
  · simpa only [List.nil_append,List.length_append,← body.1] using head.append body
  · rw [show traceCost (as++bs)=traceCost as+traceCost bs from VPVNP.RAMBuckets.cost_append ..,bcost]
    omega

/-- A second native run using the same supplied choices must have the same
return, memory and chronological execution. This rules out surplus private
branch traces in the report preparer. -/
theorem prepare_unique {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {s : Bank w} {m : Memory w}
    {es fs t u mt mu} (first : Runs pub mac prepareReports s m es t mt)
    (second : Runs pub mac prepareReports s m fs u mu)
    (bits : es.flatMap Event.choices=fs.flatMap Event.choices) : es=fs ∧ t=u ∧ mt=mu :=
  unique_returns (c := prepareReports) (by decide) first second (tail := []) (tail' := []) (by simpa using bits)

end FiniteEvaluator.Reports

end BorderVNP
end Computability
end OAI
