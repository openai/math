import OAI.Computability.VPVNP.PairTraversalControllerMemory
import OAI.Computability.VPVNP.PairTerminalPrefixSegment
import OAI.Computability.VPVNP.PairSimulationFinalBitScan
import OAI.Computability.VPVNP.CursorBranchCommunication

/-!
# Communication of the five native terminal stages

The final outgoing-arc prefix scan, tagged history-directory construction,
shared-bit guesses, and vertex evaluations all run on the same selected
network. This calculation includes the closing reports and the two complete
passes over the history directories, including their repeated operand reads.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.CompressedPair

open BurstRAM Compression CursorNetwork NetworkKernel PairSimulation CompressorRecords
open LocalHistory

variable {w : ℕ}

private theorem ofFn_cost {n : ℕ} (rs : Fin n → Report w) :
    RAMBuckets.cost Report.probes (List.ofFn rs) = ∑ i, (1+(rs i).probes) := by
  induction n with
  | zero => simp [RAMBuckets.cost]
  | succ n ih => rw [List.ofFn_succ,RAMBuckets.cost,Fin.sum_univ_succ,ih]

theorem arc_count_positions {a g : ℕ} (Y : State a g) : TerminalPrefix.arcCount Y = Y.positions*2^a := by
  have h : (siteOrder Y).length = Y.positions := by
    change (siteOrder Y).length = Fintype.card Y.network.Site
    simpa only [Fintype.card_fin] using Fintype.card_congr (siteOrder Y).entries
  exact congrArg (· * 2^a) h

/-- Fixed coefficient for the initial header, both row-building passes,
the wire-prefix and shared-bit scans, and all vertex reports. -/
def terminalCoefficient (degree steps recordLimit bootstrap close site : ℕ) :=
  bootstrap+close+9+8*degree+(2*recordLimit+1294)*(steps+2)+4+site

private theorem terminalEstimate {xp yp wt occ l q degree steps term limit boot close site : ℕ}
    (hx : 1 ≤ xp) (hl : 1 ≤ l) (ht : term ≤ l) (hq : 1 ≤ q) :
    boot+close+9+8*(yp*degree)+(2*limit+1294)*(((steps+1)*term+1)*xp)+4*wt+
      site*(xp*l^q+3*wt+yp+occ*l^q) ≤
      terminalCoefficient degree steps limit boot close site*(xp*l^q+3*wt+yp+occ*l^q) := by
  let total := xp*l^q+3*wt+yp+occ*l^q
  have hlq := Nat.pow_le_pow_right hl hq
  rw [pow_one] at hlq
  have x : 1 ≤ total := by
    have hp := Nat.mul_le_mul hx (hl.trans hlq)
    dsimp only [total]; omega
  have t : (steps+1)*term+1 ≤ (steps+2)*l := by
    have := Nat.mul_le_mul_left (steps+1) ht
    nlinarith only [this,hl]
  have hc := Nat.mul_le_mul_right xp t
  rw [show ((steps+2)*l)*xp = (steps+2)*(xp*l) by ring] at hc
  have hxl : xp*l ≤ total := by
    exact (Nat.mul_le_mul_left _ hlq).trans (by dsimp [total]; omega)
  have hstage := Nat.mul_le_mul_left (2*limit+1294) (hc.trans (Nat.mul_le_mul_left _ hxl))
  rw [← Nat.mul_assoc (2*limit+1294) (steps+2) total] at hstage
  have hy : yp ≤ total := by dsimp [total]; omega
  have hw : wt ≤ total := by dsimp [total]; omega
  have hb := Nat.mul_le_mul_left (boot+close+9) x
  have hp := Nat.mul_le_mul_left (8*degree) hy
  have hf := Nat.mul_le_mul_left 4 hw
  change _ ≤ terminalCoefficient degree steps limit boot close site*total
  calc
    _ ≤ (boot+close+9)*total+(8*degree)*total+((2*limit+1294)*(steps+2))*total+4*total+site*total := by
      rw [show 8*(yp*degree)=(8*degree)*yp by ring]
      exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
        (by simpa only [Nat.mul_one] using hb) hp) hstage) hf) _
    _ = _ := by unfold terminalCoefficient; ring

/-- Bound the actual bootstrap, wire-prefix, history-table, final-bit and
per-vertex report lists by the compressed branch's geometric charge. The
history constructor supplies its two-pass charge and the vertex routines
supply their own occurrence-by-occurrence charges. -/
theorem terminal_source_charge {A : Type*} {a b g h : ℕ}
    (X : State a g) (Y : State b h) (chain : TermChain A X.network Y.network)
    (pub : Fin 11 → Word w) (bootstrap close : Report w) (bootBound closeBound : ℕ)
    (hboot : bootstrap.probes ≤ bootBound) (hclose : close.probes ≤ closeBound)
    {dir : IncidenceDirectory w} {base : Word w} {prefixMemory : Memory w} {prefixRows : List (Report w)}
    (scan : TerminalPrefix.Segment.Run pub Y dir base prefixMemory prefixRows)
    (arena : List (Report w)) (steps limit T : ℕ)
    (ha : RAMBuckets.cost Report.probes arena ≤ (2*limit+1294)*(((steps+1)*T+1)*X.positions))
    (bitMemory : Memory w) (bits : Fin Y.totalWidth → Bool)
    (vertex : Y.network.Site → Report w) (site q n : ℕ) (hq : 1 ≤ q) (hT : T ≤ n.log2+1)
    (hsite : ∀ v, 1+(vertex v).probes ≤ siteAccesses Y chain site q n v) :
    let visits := List.ofFn fun i => vertex ((siteOrder Y).entries i)
    let rs := [bootstrap] ++ prefixRows ++ arena ++ FinalBits.Worker.reports pub 0 bitMemory bits ++ visits ++ [close]
    RAMBuckets.cost Report.probes rs ≤
      branchAccesses X Y chain (terminalCoefficient (2^b) steps limit bootBound closeBound site) q n := by
  intro visits rs
  have hv : RAMBuckets.cost Report.probes visits ≤ ∑ v, siteAccesses Y chain site q n v := by
    change RAMBuckets.cost _ (List.ofFn _) ≤ _
    rw [ofFn_cost]
    calc
      _ ≤ ∑ i, siteAccesses Y chain site q n ((siteOrder Y).entries i) :=
        Finset.sum_le_sum (fun _ _ => hsite _)
      _ = _ := (siteOrder Y).entries.sum_comp _
  have sub : (∑ v, siteAccesses Y chain site q n v) ≤ branchAccesses X Y chain site q n :=
    Nat.le_add_left ..
  have verts := hv.trans sub
  rw [branchAccesses_eq] at verts ⊢
  have pref := scan.charge
  rw [arc_count_positions] at pref
  have wire := (FinalBits.Worker.scan_cost pub _ 0 bitMemory bits).2.1
  simp only [rs,RAMBuckets.cost_append,RAMBuckets.cost, Nat.add_zero]
  rw [pref,wire]
  have estimate := @terminalEstimate X.positions Y.positions Y.totalWidth (totalOccurrences chain)
    (n.log2+1) q (2^b) steps T limit bootBound closeBound site X.positions_pos (Nat.succ_pos _) hT hq
  apply le_trans _ estimate
  omega

/-- The local cap on the same chronological reports, including both
guard closures and all external reads from the history directories. -/
theorem terminal_source_rows {a g : ℕ} (Y : State a g) (pub : Fin 11 → Word w)
    (bootstrap close : Report w) (H fuel : ℕ)
    (hboot : bootstrap.probes+9 ≤ H ∧ bootstrap.events.length+107 ≤ fuel)
    (hclose : close.probes+9 ≤ H ∧ close.events.length+107 ≤ fuel)
    {dir : IncidenceDirectory w} {base : Word w} {prefixMemory : Memory w} {prefixRows : List (Report w)}
    (scan : TerminalPrefix.Segment.Run pub Y dir base prefixMemory prefixRows)
    (arena : List (Report w)) (arenaBound : ∀ r ∈ arena, r.probes+9 ≤ H ∧ r.events.length+107 ≤ fuel)
    (bitMemory : Memory w) (bits : Fin Y.totalWidth → Bool) (vertex : Y.network.Site → Report w)
    (siteBound : ∀ v, (vertex v).probes+9 ≤ H ∧ (vertex v).events.length+107 ≤ fuel)
    (hH : 16 ≤ H) (hfuel : 136 ≤ fuel) :
    let visits := List.ofFn fun i => vertex ((siteOrder Y).entries i)
    let rs := [bootstrap] ++ prefixRows ++ arena ++ FinalBits.Worker.reports pub 0 bitMemory bits ++ visits ++ [close]
    ∀ r ∈ rs, r.probes+9 ≤ H ∧ r.events.length+107 ≤ fuel := by
  intro visits rs r hr
  simp only [rs,List.mem_append,List.mem_singleton] at hr
  rcases hr with ((((rfl | h) | h) | h) | h) | rfl
  · exact hboot
  · have ⟨p,t⟩ := scan.bounds r h
    exact ⟨by omega,by omega⟩
  · exact arenaBound r h
  · have ⟨p,t⟩ := (FinalBits.Worker.scan_cost pub _ 0 bitMemory bits).2.2 r h
    exact ⟨by omega,by omega⟩
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp h
    exact siteBound _
  · exact hclose

end LiveProgram.CompressedPair

end VPVNP
end Computability
end OAI
