import OAI.Hierarchy.TaggedWideEmissionFrame
import OAI.Hierarchy.ProtocolRAMPruneFlag
import OAI.Hierarchy.TaggedWideControlDense
import OAI.Hierarchy.TaggedWideNativeSeries

namespace OAI
/-! # The dense observed CPU for genuine format publications and the last pruning word -/

noncomputable section
namespace Hierarchy.Tagged.WideControlJoin.Gate
open ThreeFlat Routing Diagonal
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMMemory
open ProtocolRAM ProtocolRAMEmit TaggedPrune CorrectionFrame
open scoped Classical BigOperators Fin.CommRing

variable {W n h w k M den S f U formats : ℕ} {b : Fin k→ℕ}

/-- The previous physical procedure runs the genuine booted paid calendar, its dated
widths, and chronological site/turn fields. The next format programs run in distinct
forward-only windows. Last, the observed CPU computes the unsigned retention bit. -/
theorem formats_pruned {D : Layout h w b} {rows : Fin n → ProtocolRAMEmit.Row} (G : Geometry D M den rows)
    (dst code scratch ticks floor : ℕ) (ends metrics layers : Bank) (head : ℕ → Word W)
    (paid : Procedure W) (first : ℕ) (m₀ raw : Memory W)
    (prefixExec : paid.Exec (initialMemory S head) m₀ first)
    (report : ∀j,dst ≤ j → j<dst+9*n → m₀ j=emitted dst rows raw j) (kept : dst+9*n ≤ floor)
    (pool : Fin (formats+1)→ℕ) (stages : Fin (formats+1) → Procedure W) (time : Fin (formats+1)→ℕ)
    (board : Fin (formats+1)→ℕ → Prop) (cell : Fin (formats+1)→ℕ → Word W → Prop)
    (inside : ∀j u,board j u → u<WindowSeries.start floor pool j+pool j)
    (step : ∀j s,(∀u<floor,s u=m₀ u)→∃t,(stages j).Exec s t (time j) ∧
      (∀u,board j u → cell j u (t u)) ∧ ∀u<WindowSeries.start floor pool j,t u=s u)
    (later : WindowSeries.finish floor pool ≤ scratch)
    (hw : 0<w) (hd : 0<den) (ep : ends.base=dst) (mt : metrics.base=dst+3*n)
    (es : 3*n ≤ ends.size) (ms : 3*n ≤ metrics.size) (ir : 3*n<2^W) (cap : code<2^W)
    (codes : ∀i,(rows i).lengthCode ≤ code) (loc : Fintype.card (Location k)<2^W)
    (layerFits : layers.base+layers.size ≤ floor)
    (advice : ∀i,∀s∈[(rows i).endpoint,(rows i).opposite],layers.read m₀ (s:Word W)=(PruneFlag.layerCode D s:Word W))
    (fit : (PruneFlag.term ends metrics layers code).Fits W scratch) (room : scratch+(n+1)<2^W)
    (threshold : 2*M*(∑j,b j)*den-ticks*w*den<2^W) (sumroom : (∑i,PruneFlag.charge D (rows i))<2^W)
    (ret state : Word W) (m : ℕ) (word : 3 ≤ W+1) (extent : U≤2^W)
    (headerRoom : S≤2^W) (traceClock : f+U≤2^(W+1)) :
    let bound := 2*M*(∑j,b j)*den-ticks*w*den
    let expr := PruneFlag.term ends metrics layers code
    let P := (paid.seq (ProcedureBank.program formats stages)).seq (SumScores.procedure W scratch n bound expr)
    ∀ labels : P.labels+3≤2^(W+1),first+(∑j,time j)+(4+(n+1)*(42+2*expr.work))+2<f →
      ∃ final,(denseProcedure P ret state extent m word labels headerRoom traceClock).Ran head final ∧
        (∀j u,board j u → cell j u (final u)) ∧ (∀u<floor,final u=m₀ u) ∧
        final (scratch+n)=(if G.links.Keep ticks then 1 else 0) := by
  intro bound expr P labels clock
  obtain ⟨mem,run,stored,frame⟩ := WindowSeries.run floor pool stages time m₀ board cell inside step
  have native := TaggedShorterControlHistory.emitted_of_frame dst rows raw mem
    (fun j lo hi=>(frame j (hi.trans_le kept)).trans (report j lo hi))
  have table : ∀ i,∀s∈[(rows i).endpoint,(rows i).opposite],
      layers.read (emitted dst rows mem) (s:Word W)=(PruneFlag.layerCode D s:Word W) := by
    intro i s seen
    rw [native]
    refine Eq.trans ?_ (advice i s seen)
    apply frame
    exact (Nat.add_lt_add_left (Nat.mod_lt (s:Word W).val (Nat.two_pow_pos layers.bits)) layers.base).trans_le layerFits
  obtain ⟨scan,bit⟩ := PruneFlag.run_exact G mem dst code scratch ticks ends metrics layers hw hd ep mt es ms ir cap codes
    loc table fit room threshold sumroom
  rw [native] at scan bit
  let final := PruneFlag.output D rows scratch bound mem
  refine ⟨final,ofProcedure_run P ret state (denseAddr extent) m word labels headerRoom traceClock head final _ clock
    (Procedure.Exec.then (Procedure.Exec.then prefixExec run) scan),?_,?_,bit⟩
  · intro j u hu
    have upper := (inside j u hu).trans_le ((WindowSeries.within floor pool j).trans later)
    change cell j u (PruneFlag.output D rows scratch bound mem u)
    rw [PruneFlag.output_below _ _ _ _ _ upper]
    exact stored j u hu
  · intro u hu
    have firstWindow : floor ≤ WindowSeries.finish floor pool := Nat.le_add_right _ _
    change PruneFlag.output D rows scratch bound mem u=_
    rw [PruneFlag.output_below _ _ _ _ _ (hu.trans_le (firstWindow.trans later))]
    exact frame u hu

end Hierarchy.Tagged.WideControlJoin.Gate

end
end OAI
