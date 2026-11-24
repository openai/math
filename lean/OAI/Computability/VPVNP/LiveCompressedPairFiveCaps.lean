import OAI.Computability.VPVNP.LiveCompressedPairSourceCaps
import OAI.Computability.VPVNP.PairSimulationTerminalFive

/-! # Resource bounds for the actual five-phase terminal controller -/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.CompressedPair

open BurstRAM Compression CursorNetwork NetworkKernel PairSimulation CompressorRecords LocalHistory

variable {w : ℕ}

/-- Replay the joined bootstrap, online and five terminal phases. The only
dynamic communication estimates are the individual descriptor and vertex
estimates of this selected history. The geometric estimate is uniform in
the choice of that history. -/
theorem five_execution_caps {A : Type*} {a b g h : ℕ}
    (X : State a g) (Y : State b h) (chain : TermChain A X.network Y.network)
    (pub : Fin 11 → Word w) (boot : Bootstrap) (B n base : ℕ) (startMem : Memory w)
    (initial phases d : ℕ) (onlineBase : Word w) (onlineMem : Memory w) (online : List (Report w))
    {workers : TerminalLink.Stage → PairTable} {termClock : ℕ} {termMem : Memory w}
    (trace : TerminalLink.FiveTrace workers pub termClock termMem)
    (S H fuel : ℕ) (hS : 128 ≤ S) (hH : 16 ≤ H) (clock : 136 ≤ fuel)
    (hstart : ∀ p ∈ cursorStartupSources boot pub B n base startMem initial phases d,
      ∃ i : Fin 8, p.2.probes < sourceFuel boot initial phases n i ∧ p.2.events.length < sourceFuel boot initial phases n i)
    (hburst : ∀ i, sourceFuel boot initial phases n i+5 ≤ H)
    (hfuel : ∀ i, sourceFuel boot initial phases n i+77 ≤ fuel)
    (onlineRow : ∀ r ∈ online, r.probes+11 ≤ H ∧ r.events.length+101 ≤ fuel)
    (onlineTotal : 64*RAMBuckets.cost Report.probes online ≤ S*H)
    (bootstrap close : Report w) (bootBound closeBound : ℕ)
    (initialRow : trace.bootstrap.logs.map Prod.snd = [bootstrap])
    (bootData : bootstrap.probes ≤ bootBound ∧ bootstrap.probes+9 ≤ H ∧ bootstrap.events.length+107 ≤ fuel)
    (closeData : close.probes ≤ closeBound ∧ close.probes+9 ≤ H ∧ close.events.length+107 ≤ fuel)
    {dir : IncidenceDirectory w} {prefixBase : Word w} {prefixMemory : Memory w}
    (scan : TerminalPrefix.Segment.Run pub Y dir prefixBase prefixMemory (trace.prefixRows.logs.map Prod.snd))
    (steps limit T : ℕ)
    (arenaTotal : RAMBuckets.cost Report.probes (trace.traversalRows.logs.map Prod.snd) ≤
      (2*limit+1294)*(((steps+1)*T+1)*X.positions))
    (arenaRow : ∀ r ∈ trace.traversalRows.logs.map Prod.snd, r.probes+9 ≤ H ∧ r.events.length+107 ≤ fuel)
    (bitMemory : Memory w) (bits : Fin Y.totalWidth → Bool)
    (bitData : trace.sharedBits.logs.map Prod.snd = FinalBits.Worker.reports pub 0 bitMemory bits)
    (vertex : Y.network.Site → Report w)
    (vertexData : trace.vertices.logs.map Prod.snd = (List.ofFn fun i => vertex ((siteOrder Y).entries i)) ++ [close])
    (site q : ℕ) (hq : 1 ≤ q) (hT : T ≤ n.log2+1)
    (siteRow : ∀ v, 1+(vertex v).probes ≤ siteAccesses Y chain site q n v ∧ (vertex v).events.length+107 ≤ fuel)
    (allSites : ∀ v, siteAccesses Y chain site q n v+9 ≤ H)
    (share : 320*branchAccesses X Y chain (terminalCoefficient (2^b) steps limit bootBound closeBound site) q n ≤ S*H) :
    let rs := cursorStartupLogs boot pub B n base startMem initial phases d ++
      ((OnlineWorkspace.framed onlineBase onlineMem online).map (report pub Stage.online) ++
        (TerminalLink.reports (TerminalLink.header pub) trace.logs).map (report pub Stage.terminal))
    (∀ r ∈ rs, r.events.length+4 ≤ fuel) ∧ 4*RAMBuckets.cost Report.probes rs ≤ S*H ∧
      ∀ r ∈ rs, 3+r.probes ≤ H := by
  intro rs
  let arena := trace.traversalRows.logs.map Prod.snd
  let prefixRows := trace.prefixRows.logs.map Prod.snd
  let visits := List.ofFn fun i => vertex ((siteOrder Y).entries i)
  let raw := [bootstrap] ++ prefixRows ++ arena ++ FinalBits.Worker.reports pub 0 bitMemory bits ++ visits ++ [close]
  have actual : trace.logs.map Prod.snd = raw := by
    simp only [TerminalLink.FiveTrace.logs,List.map_append,raw,prefixRows,arena,visits,initialRow,bitData,
      vertexData,List.append_assoc]
  refine cursor_execution_caps pub (TerminalLink.header pub) boot B n base startMem initial phases d onlineBase onlineMem
    online trace.logs S H fuel hS hstart hburst hfuel onlineRow ?_ onlineTotal ?_
  · rw [actual]
    apply terminal_source_rows Y pub bootstrap close H fuel bootData.2 closeData.2 scan arena arenaRow bitMemory
      bits vertex _ hH clock
    intro v
    obtain ⟨p,t⟩ := siteRow v
    have h := allSites v
    exact ⟨by omega,t⟩
  · rw [actual]
    exact (Nat.mul_le_mul_left 320 (terminal_source_charge X Y chain pub bootstrap close bootBound closeBound
      bootData.1 closeData.1 scan arena steps limit T arenaTotal bitMemory bits vertex site q n hq hT
      (fun v => (siteRow v).1))).trans share

end LiveProgram.CompressedPair

end VPVNP
end Computability
end OAI
