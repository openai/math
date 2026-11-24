import OAI.Computability.VPVNP.LiveVirtualPairStartupBudget
import OAI.Computability.VPVNP.PairSimulationTerminalReports

/-!
# Burst and private-clock bounds on the complete native compressed pair

The bootstrap, online calendar, and terminal worker report streams below
are the three consecutive stages of the actual fixed pair instruction
table. We charge the controller's phase and cursor writes on terminal
returns, the six online pointer reads, and both enclosing tag switches.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.CompressedPair

open BurstRAM CompressorRecords PairSimulation

variable {w : ℕ} (addr : Word w)

/-- The terminal controller adds the phase reads and exit writes to each worker report. -/
abbrev terminalWorkers (src : List (TerminalLink.Entry w × Report w)) :=
  src.map (fun p => TerminalLink.report addr p.1 p.2)

theorem terminal_worker_cost (src : List (TerminalLink.Entry w × Report w)) :
    RAMBuckets.cost Report.probes (terminalWorkers addr src) ≤
      5 * RAMBuckets.cost Report.probes (src.map Prod.snd) := by
  induction src with
  | nil => rfl
  | cons a rest ih =>
    have h := TerminalLink.report_probes_le addr a.1 a.2
    change 1+(TerminalLink.report addr a.1 a.2).probes + RAMBuckets.cost _ (terminalWorkers addr rest) ≤
      5*(1+a.2.probes+RAMBuckets.cost _ (rest.map Prod.snd))
    omega

/-- The physical report stream consumed by the enclosing live row has
exactly the two resource bounds of a first-half `PairCall`. Its private
clock is bounded on the same reports. -/
theorem cursor_run_caps (E : UniversalMachine.Program) (outer : Word w) (b : Bootstrap)
    (pub : Fin 11 → Word w) (B n base : ℕ) (startMem : Memory w)
    (initial phases d : ℕ) (onlineBase : Word w) (onlineMem : Memory w)
    (online : List (Report w)) (terminal : List (TerminalLink.Entry w × Report w))
    (S H cap : ℕ) (hS : 32 ≤ S) (hH : 2 ≤ H)
    (hs : ∀ p ∈ cursorStartupSources b pub B n base startMem initial phases d,
      ∃ i : Fin 8, p.2.probes < sourceFuel b initial phases n i ∧
        p.2.events.length < sourceFuel b initial phases n i)
    (hb : ∀ i, sourceFuel b initial phases n i+5 ≤ H)
    (hf : ∀ i, sourceFuel b initial phases n i+77 ≤ cap)
    (ho : ∀ r ∈ online, r.probes+11 ≤ H ∧ r.events.length+101 ≤ cap)
    (ht : ∀ r ∈ terminal.map Prod.snd, r.probes+9 ≤ H ∧ r.events.length+107 ≤ cap)
    (oc : 64*RAMBuckets.cost Report.probes online ≤ S*H)
    (tc : 320*RAMBuckets.cost Report.probes (terminal.map Prod.snd) ≤ S*H) :
    let rs := (cursorStartupLogs b pub B n base startMem initial phases d ++
      ((OnlineWorkspace.framed onlineBase onlineMem online).map (report pub Stage.online) ++
        (terminalWorkers addr terminal).map (report pub Stage.terminal))).map
          (LiveStageLink.linkedReport (LiveProgram.next E) outer LiveProgram.Stage.pair)
    RAMBuckets.cost Report.probes rs ≤ S*(H-1) ∧
      ∀ r ∈ rs, 1+r.probes ≤ H ∧ r.events.length ≤ cap := by
  intro rs
  let startup := cursorStartupSources b pub B n base startMem initial phases d
  have bound : rs = logs pub E outer onlineBase onlineMem startup online (terminalWorkers addr terminal) := by
    simp only [rs,startup,cursorStartupLogs_eq,List.map_append,List.map_map,logs,
      wrappedStartup,onlineLogs,terminalLogs,List.append_assoc]
    rfl
  rw [bound]
  refine linked_caps pub E outer onlineBase onlineMem startup online (terminalWorkers addr terminal)
    S H cap hS hH ?_ (startup_rows_le b initial phases n H cap startup hs hb hf) ho ?_ oc ?_
  · simp [startup,cursorStartupSources]
  · intro r hr
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hr
    have ⟨p₁,p₂⟩ := ht p.2 (List.mem_map_of_mem hp)
    have hl := TerminalLink.report_length_le addr p.1 p.2
    have hc := TerminalLink.report_probes_le addr p.1 p.2
    omega
  · have := terminal_worker_cost addr terminal
    omega

/-- Convert the little-o estimates of the cursor geometry to the integer
charges of the two finite traversals. -/
theorem integer_cost_share {k charge S H : ℕ} (hk : 0 < k)
    (h : (charge : ℝ) < (1/(k : ℝ))*(S : ℝ)*H) : k*charge ≤ S*H := by
  have kp : (0 : ℝ) < k := by exact_mod_cast hk
  rw [show (1/(k : ℝ))*(S : ℝ)*H = ((S : ℝ)*H)/(k : ℝ) by ring] at h
  have := (lt_div_iff₀ kp).mp h
  rw [mul_comm] at this
  exact_mod_cast this.le

end LiveProgram.CompressedPair

end VPVNP
end Computability
end OAI
