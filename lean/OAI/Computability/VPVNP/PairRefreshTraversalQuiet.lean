import OAI.Computability.VPVNP.PairRefreshTraversalAction

/-! # Choice and external-memory frames of the canonical refresh action

Only the preceding child reader consumes the guessed half-wire bits. The
selected local action consumes no further choices and only reads external RAM.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh.TraversalPlan

open BurstRAM BurstRAM.PrivateRAM Compression Compression.Refresh Compression.DegreeRefresh
open PhaseRecipe PairSimulation VertexImage NodeArguments NewSlots RefreshMapOperands NetworkKernel
open MotifConversion MotifEntry MotifDemandPadding MotifSelector LocalHistory
open scoped Fin.CommRing
open private guessed_addFuel from OAI.Computability.VPVNP.PairSimulationDFSDecode

variable {k : Type} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) {t hist bits g : ℕ}
  (ties : Fin t ≃ Tie (2^S.portExponent)) (stride : ℕ) (order : B.Entry ≃ Fin hist)
  (X : State S.portExponent (S.portExponent+g))
  (choice : DyadicRefreshChoice X S.graph (Nat.two_pow_pos _) (And.left (S.port_bound.connected_and_pos S.port_order)) B.refresh)
  (v : (X.Base × BitWord g) × Fin (2^S.portExponent)) (degree n rowEnd child parent : ℕ)

variable (room : Room B X choice v degree n rowEnd child parent hist bits)
  (old : X.network.Half (oldSite X v))
  (new : (dyadicRefreshNext X S.graph (Nat.two_pow_pos _) (And.left (S.port_bound.connected_and_pos S.port_order))
    B.refresh S.port_order S.degree_bounds.2 choice).network.Half (promotedSites v))
  (m : Memory bits) (oldHead newHead : ℕ) (G : W bits)

local notation "events" => canonicalEvents B ties stride order X choice v degree n rowEnd child parent room old new m oldHead newHead G
local notation "T" => plan B ties stride order
local notation "action" => canonicalAction B ties stride order X choice v degree n rowEnd child parent room old new m oldHead newHead G

theorem canonicalEvents_noChoices : choiceBits events = [] := by
  rw [canonicalEvents,PrimedInputRAM.Flow.choiceBits_append,(T).successEvents_noChoices]
  rfl

theorem canonicalEvents_noWrites : SourceTransport.Writes (fun _ => False) events := by
  intro a value h
  rcases List.mem_append.mp h with tick | visit
  · cases List.eq_of_mem_replicate tick
  · exact (T).successEvents_noWrites X choice v m old new room.tableWidth _ _ a value visit

variable {endAddr : ℕ} {s updated : DFS.Scratch bits endAddr} {es : List (Event bits)}

theorem canonicalAction_events (h : action s = some (es,updated)) : es = events := by
  unfold canonicalAction at h
  split at h
  · exact (Prod.mk.inj (Option.some.inj h)).1.symm
  · contradiction

theorem canonicalAction_noChoices (h : action s = some (es,updated)) : choiceBits es = [] := by
  rw [canonicalAction_events B ties stride order X choice v degree n rowEnd child parent room old new m oldHead newHead G h]
  exact canonicalEvents_noChoices B ties stride order X choice v degree n rowEnd child parent room old new m oldHead newHead G

theorem canonicalAction_noWrites (h : action s = some (es,updated)) :
    SourceTransport.Writes (fun _ => False) es := by
  rw [canonicalAction_events B ties stride order X choice v degree n rowEnd child parent room old new m oldHead newHead G h]
  exact canonicalEvents_noWrites B ties stride order X choice v degree n rowEnd child parent room old new m oldHead newHead G

theorem after_canonicalAction (h : action s = some (es,updated)) : after m es = m :=
  funext fun _ => SourceTransport.after_outside m
    (canonicalAction_noWrites B ties stride order X choice v degree n rowEnd child parent room old new m oldHead newHead G h) id

/-- Every successful complete report factors at the certified local prefix, including
reports obtained at an arbitrary fuel bound. All its external updates occur in the suffix. -/
theorem canonicalAction_report {pcs regs params fuel : ℕ} {M : Machine bits pcs regs params}
    {c out : Config bits pcs regs} {tape : List Bool} {report : Report bits}
    (h : action s = some (es,updated)) (pre : ChildScan.Prefix M m c out [] es)
    (returned : execute M.program fuel c m tape = some report) :
    ∃ rest, execute M.program fuel out m tape = some rest ∧ report.events = es ++ rest.events ∧
      report.result = rest.result ∧ after m report.events = after m rest.events := by
  obtain ⟨guessed,correct,choices⟩ := execute_iff.mp returned
  have more := execute_iff.mpr ⟨guessed_addFuel guessed es.length,correct,choices⟩
  have tail := pre fuel tape
  rw [List.nil_append] at tail
  rw [Nat.add_comm es.length fuel,tail] at more
  obtain ⟨rest,run,eq⟩ := Option.map_eq_some_iff.mp more
  have eventsEq := congrArg Report.events eq.symm
  have resultEq := congrArg Report.result eq.symm
  have unchanged := after_canonicalAction B ties stride order X choice v degree n rowEnd child parent room old new m
    oldHead newHead G h
  refine ⟨rest,run,eventsEq,resultEq,?_⟩
  rw [eventsEq]
  exact (show after m (es++rest.events) = after (after m es) rest.events from List.foldl_append).trans
    (congrArg (fun mem => after mem rest.events) unchanged)

end CompressorRecords.PortRefresh.TraversalPlan

end VPVNP
end Computability
end OAI
