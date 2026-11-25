import OAI.Computability.BorderVNP.CubeLabelStageCache
import OAI.Computability.BorderVNP.CubeLabelStageScan
import OAI.Computability.BorderVNP.LabelIndexChooserFit
import OAI.Computability.BorderVNP.CubeLabelResources
import OAI.Computability.BorderVNP.CubeLabelDirectoryTicks
import OAI.Computability.BorderVNP.RoutingISATableEvents
import OAI.Computability.BorderVNP.RoutingISALink

/-! # Reading all §8.1 labels back from the initialized native directory

The fixed program receives only the original compressed cable and delivery tables
and their allocation frame. It reconstructs the sparse index, tries every legal label,
commits the least minimizer, and writes the same codes as the mathematical label scan.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.LabelIndex

open RoutingISA RoutingISA.LabelTrial VPVNP.BurstRAM

/-- The three quantities used by the physical bin pass are exactly the old mean
and old and new incident subtotals on the assigned prefix. -/
theorem indexed_means (l : Layout) (m : ℕ → ℕ) (ep : Endpoints l m) (al : Allocated l)
    (lab z : ℕ) (hz : l.labels = z+1) (sep : lab+l.cells ≤ l.heads) :
    IndexedBinMeans l m ep lab z (image l m).mem := by
  intro c v p rows t b traffic
  let s := cellsBefore l.cells c.val
  let x := stage traffic z c.val
  have view := image_view l m al ep
  have old := stage_cache l m ep al (image l m) view lab z hz sep c.val c.isLt.le
  have prior (o : Fin l.cells) : o ∈ s ↔ o < c := by
    change o ∈ cellsBefore l.cells c.val ↔ o.val < c.val
    simp only [cellsBefore,Finset.mem_filter,Finset.mem_univ,true_and]
  have demand : t (p.demands+c.val) = sumWidth
      (fun i => if (deliveryAt l m i).1 = c.val then (deliveryAt l m i).2 else 0) l.deliveryCount := by
    have ah := al.heads
    have an := al.nodes
    have ad := al.data
    exact (old.inputs _ (show l.heads ≤ l.data+c.val by omega)
      (show l.data+c.val < l.cableMean by have := c.isLt; omega)).trans (view.data c.val c.isLt)
  have weights (j) := p.incident_tables l m ep t c s x v hz prior (fun o ho => old.labels o ho) demand j
  exact ⟨s,x,old.means,fun j => congrArg Prod.fst (weights j),fun j => congrArg Prod.snd (weights j)⟩

/-- Every native probe and arithmetic operation on the reachable tables is justified by
the initial public allocation and a single polynomial envelope on the input widths. -/
theorem fitted_tables (l : Layout) (m : ℕ → ℕ) (ep : Endpoints l m) (al : Allocated l)
    (lab z w : ℕ) (hz : l.labels = z+1) (sep : lab+l.cells ≤ l.heads)
    (addresses : l.dataMean+l.labels ≤ 2^w) (cap : wordEnvelope l.labels (inputWidth l m) < 2^w) :
    (l.trialFrame lab).Fitted w z (directoryRows l m) (image l m).mem := by
  obtain ⟨count,cab,dat,means,score⟩ := wordCaps l m ep w cap
  have ah := al.heads
  have an := al.nodes
  have ad := al.data
  have ac := al.cableMean
  have space : ChooserSpace l m lab w := ⟨addresses,by omega,cab,dat⟩
  rw [hz] at means score
  exact indexed_frame_fitted (image_view l m al ep) al ep (Or.inl sep) space hz count means score
    (indexed_means l m ep al lab z hz sep)

/-- Execute the deterministic public §8.1 chooser on the actual compressed arrays.
Every output word equals its least-minimizer code, including in empty or singleton
cell layouts. The trace bound includes index construction, every bin trial and commit,
and the cost of addressing each output. Words below both the heads and the label array
retain their original values. -/
theorem native_table_codes {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (z : ℕ) (s : Bank w) (m : Memory w) :
    let before := readings m
    let base := (pub 0).val
    let l := layout base before
    let lab := before (base+48)
    ∀ (ep : Endpoints l before), Allocated l → l.labels = z+1 → lab+l.cells ≤ l.heads →
    base+56 < l.heads → l.dataMean+l.labels ≤ 2^w →
    wordEnvelope l.labels (inputWidth l before) < 2^w →
    ∃ tr t mt, Runs pub macros directoryProgram s m tr t mt ∧ traceCost tr ≤ directoryTicks l z before ∧
      (t 1).val = l.cells ∧
      (∀ c : Fin l.cells, (mt (lab+c.val)).val = (Physical.tableCodes l before ep z c).val) ∧
      ∀ addr < lab, mt addr = m addr := by
  intro before base l lab ep al hz sep frame addresses cap
  have fit := Fits.of_envelope l before ep w (hz ▸ Nat.zero_lt_succ _) addresses cap
  have chooser := fitted_tables l before ep al lab z w hz sep addresses cap
  have ah := al.heads
  have an := al.nodes
  have ad := al.data
  have ac := al.cableMean
  have hf : base+56 < 2^w := by omega
  obtain ⟨tr,t,mt,run,cost,done,mem,_⟩ := directoryProgram_run pub macros z s m frame hf al ep fit chooser
  let rows := directoryRows l before
  let p := l.trialFrame lab
  let init := (image l before).mem
  change readings mt = p.prefix z rows init l.cells at mem
  have view := image_view l before al ep
  have last := stage_cache l before ep al _ view lab z hz sep l.cells le_rfl
  refine ⟨_,_,_,run,cost,done,?_,?_⟩
  · intro c
    change readings mt (lab+c.val) = _
    rw [mem,← stage_tables l before ep z]
    exact last.labels c c.isLt
  · intro addr h
    apply Fin.ext
    change readings mt addr = before addr
    rw [mem]
    have sepCache : p.cables+p.Z^2 ≤ p.data := by simpa only [p,Layout.trialFrame,pow_two] using ac
    rw [p.prefix_off z rows init l.cells addr]
    · exact view.input _ (by omega)
    · intro i _ eq
      have low := p.cacheAddr_lower sepCache i
      change l.cableMean ≤ p.cacheAddr i at low
      omega
    · intro j _; change addr ≠ lab+j; omega

/-- The ordinary team dispatcher fetches precisely the events of the constructed run.
Each event consumes zero guess bits, has positive sign and costs one ordinary tick. -/
theorem directory_dispatch {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {s m tr t mt} (r : Runs pub macros directoryProgram s m tr t mt) :
    TeamRAM.execute (directoryProgram.program.fetch pub macros) ⟨0,s⟩ m (tr.map TeamRAM.Event.choices) = some tr ∧
    traceCost tr = tr.length ∧ ∀ e ∈ tr, e.choices = [] ∧ e.sign = .plus :=
  ⟨r.execute,r.deterministic_cost directoryProgram_deterministic,r.unsigned_events (by decide)⟩

end Cube.LabelIndex

end BorderVNP
end Computability
end OAI
