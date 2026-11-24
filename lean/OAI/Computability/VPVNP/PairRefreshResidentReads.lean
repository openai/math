import OAI.Computability.VPVNP.PairRefreshResidentFrontExact
import OAI.Computability.VPVNP.PairSimulationMapHandlerAction

/-! # The chronological reads of a successful resident refresh visit

A fixed list of setup events and private ticks precedes the selected map.
Each external read, including a nested load used to compute another address,
belongs to a diagonal, route or argument-writer expression.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh.RefreshResidentImage.Plan

open BurstRAM Compression Compression.Refresh Compression.DegreeRefresh
open PhaseRecipe PairSimulation MotifConversion NewSlots RefreshMapOperands MotifEntry LocalHistory
open private no_choices from OAI.Computability.VPVNP.CompressorRecordRegisterSetup
open private eval_no_writes from OAI.Computability.VPVNP.CompressorFormulaFootprint

variable {bits g t hist shared : ℕ} {k : Type} [_root_.Field k] {S : BlockSchedule k} {B : S.Templates}
  (T : Plan B t hist shared) (X : State S.portExponent (S.portExponent+g))
  (choice : DyadicRefreshChoice X S.graph (Nat.two_pow_pos _)
    (And.left (S.port_bound.connected_and_pos S.port_order)) B.refresh)
  (v : (X.Base × BitWord g) × Fin (2^S.portExponent)) (m : Memory bits)
  (old : X.network.Half (oldSite X v)) (new : (dyadicRefreshNext X S.graph (Nat.two_pow_pos _)
    (And.left (S.port_bound.connected_and_pos S.port_order)) B.refresh S.port_order S.degree_bounds.2 choice
    ).network.Half (promotedSites v))

local notation "E₀" => entryInput B X choice v old new
local notation "z" => demandGrid B.refresh (fun _ => zero_lt_one) (EntryInput.demand E₀)
local notation "idx" => (z,Prod.snd v)
local notation "Wfields" => MapHandlerImage.Family.fields (Plan.family T) idx

/-- Chronological trace on a successful diagonal and motif selection. -/
noncomputable def successEvents (hw : MapConstants.widthThreshold B.refresh ≤ bits)
    (pub : Fin 5 → W bits) (state : W bits) : List (Event bits) :=
  T.frontEvents X choice v m old new pub state ++
    T.family.successEvents (fun _ => zero_lt_one) E₀ hw pub state m

private theorem append_reads {data : ℕ → Prop} {a b : List (Event bits)}
    (ha : SourceTransport.Reads data a) (hb : SourceTransport.Reads data b) :
    SourceTransport.Reads data (a++b) :=
  fun q w h => (List.mem_append.mp h).elim (ha q w) (hb q w)

private theorem tick_reads (data : ℕ → Prop) (n : ℕ) :
    SourceTransport.Reads data (List.replicate n (.tick : Event bits)) := by
  intro q value h
  cases List.eq_of_mem_replicate h

theorem successEvents_readsFrom (hw : MapConstants.widthThreshold B.refresh ≤ bits)
    (pub : Fin 5 → W bits) (state : W bits) (data : ℕ → Prop)
    (diagSafe : ∀ j, (T.diagonal j).ReadsFrom data pub state m)
    (routeSafe : ∀ j, (T.route j).ReadsFrom data pub state m)
    (writerSafe : ∀ j, ((MapArgumentWriter.recipes T.directory Wfields) j).ReadsFrom data pub state m) :
    SourceTransport.Reads data (T.successEvents X choice v m old new hw pub state) := by
  apply append_reads
  · exact append_reads (append_reads (RegisterSetup.lines_reads T.diagonal data pub state m diagSafe _) (tick_reads _ _))
      (append_reads (RegisterSetup.lines_reads T.route data pub state m routeSafe _) (tick_reads _ _))
  · apply T.family.successEvents_readsFrom (fun _ => zero_lt_one) E₀ hw pub state m data
    · change T.directory.ReadsFrom data pub state m
      simpa only [MapArgumentWriter.recipes,Fin.snoc_last] using writerSafe (Fin.last _)
    · intro a
      change (T.family.field idx a).ReadsFrom data pub state m
      have h := writerSafe (((T.family.layout idx).args a).castSucc)
      simpa only [MapArgumentWriter.recipes,Fin.snoc_castSucc,MapHandlerImage.Family.fields,
        Function.comp_apply,Equiv.symm_apply_apply] using h

private theorem tick_choices (n : ℕ) : choiceBits (List.replicate n (.tick : Event bits)) = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [List.replicate_succ,choiceBits] using ih

theorem successEvents_noChoices (hw : MapConstants.widthThreshold B.refresh ≤ bits)
    (pub : Fin 5 → W bits) (state : W bits) :
    choiceBits (T.successEvents X choice v m old new hw pub state) = [] := by
  simp only [successEvents,frontEvents,PrimedInputRAM.Flow.choiceBits_append,setupEvents,no_choices,tick_choices,
    List.nil_append]
  exact T.family.successEvents_noChoices (fun _ => zero_lt_one) E₀ hw pub state m

/-- The setup instructions and private loops leave every external memory cell intact. -/
theorem successEvents_noWrites (hw : MapConstants.widthThreshold B.refresh ≤ bits)
    (pub : Fin 5 → W bits) (state : W bits) :
    SourceTransport.Writes (fun _ => False) (T.successEvents X choice v m old new hw pub state) := by
  intro a value h
  rcases List.mem_append.mp h with front | selected
  · rcases List.mem_append.mp front with diagonal | route
    · rcases List.mem_append.mp diagonal with setup | ticks
      · exact eval_no_writes (fun _ => False) pub state m (RegisterSetup.lines T.diagonal) _ a value setup
      · cases List.eq_of_mem_replicate ticks
    · rcases List.mem_append.mp route with setup | ticks
      · exact eval_no_writes (fun _ => False) pub state m (RegisterSetup.lines T.route) _ a value setup
      · cases List.eq_of_mem_replicate ticks
  · exact T.family.successEvents_noWrites (fun _ => zero_lt_one) E₀ hw pub state m a value selected

theorem after_successEvents (hw : MapConstants.widthThreshold B.refresh ≤ bits)
    (pub : Fin 5 → W bits) (state : W bits) :
    after m (T.successEvents X choice v m old new hw pub state) = m :=
  funext fun _ => SourceTransport.after_outside m (T.successEvents_noWrites X choice v m old new hw pub state) id

end CompressorRecords.PortRefresh.RefreshResidentImage.Plan

end VPVNP
end Computability
end OAI
