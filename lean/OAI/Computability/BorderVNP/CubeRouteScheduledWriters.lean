import OAI.Computability.BorderVNP.RoutingISASignedAssembly
import OAI.Computability.BorderVNP.RoutingISABlockAppend
import OAI.Computability.BorderVNP.RoutingISACubeArenaPreserve

/-! # The two descriptor writers reached by the actual signed schedule -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open BorderVNP.Cube RoutingISA.Transmission VPVNP.BurstRAM

/-- The native schedule preceding the two transmission writers, through the installation of the pair directory. -/
def beforeWriters (n bits : ℕ) : List Code := [LabelIndex.directoryProgram, NativeIntervals.prepare, CubePowers.install,
  CubeHeaderInstall.install n bits, HeaderDecode.program, CubeLengths.minimum, GroupWeights.checkedSchedule,
  CellBanks.install, PairDirectory.directory]

variable {w n bits : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
variable {r t : Bank w} {m mt : Memory w} {es : List (TeamRAM.Event w)}

/-- A decomposition of the actual signed schedule at the two writer entry states. -/
structure WriterHistory (n bits : ℕ) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (r : Bank w) (m : Memory w)
    (es : List (TeamRAM.Event w)) (t : Bank w) (mt : Memory w) where
  /-- Registers on entering the data-demand writer. -/
  dataRegs : Bank w
  /-- RAM after installation of the receiving-cell and label-pair directories. -/
  dataInput : Memory w
  /-- Registers after publishing the data prefix. -/
  sharedRegs : Bank w
  /-- RAM containing the seven-word data records before appending shared rows. -/
  sharedInput : Memory w
  /-- Events through the final pair-directory installation. -/
  prefixTrace : List (TeamRAM.Event w)
  /-- Events that lower and publish the data-demand prefix. -/
  dataTrace : List (TeamRAM.Event w)
  /-- Events that append the strict-pair records and publish the total count. -/
  sharedTrace : List (TeamRAM.Event w)
  prefixRun : Runs pub mac (.block (beforeWriters n bits)) r m prefixTrace dataRegs dataInput
  dataRun : Runs pub mac DataWriter.program dataRegs dataInput dataTrace sharedRegs sharedInput
  sharedRun : Runs pub mac SharedRows.program sharedRegs sharedInput sharedTrace t mt
  chronological : es = prefixTrace ++ (dataTrace ++ sharedTrace)

/-- Any real return of the entire scheduling program decomposes at these actual boundaries. -/
theorem scheduleGroups_writerHistory (run : Runs pub mac (scheduleGroups n bits) r m es t mt) :
    Nonempty (WriterHistory n bits pub mac r m es t mt) := by
  change Runs pub mac (.block ((beforeWriters n bits) ++ [DataWriter.program,SharedRows.program])) r m es t mt at run
  obtain ⟨u,mu,fs,gs,et,prefixRun,tail⟩ := Runs.seq_iff.mp
    ((Runs.block_append_iff (List.cons_ne_nil _ _ : beforeWriters n bits ≠ []) (by decide : [DataWriter.program,SharedRows.program] ≠ [])).mp run)
  obtain ⟨v,mv,ds,ss,ts,dataRun,sharedRun⟩ := Runs.seq_iff.mp tail
  exact ⟨⟨u,mu,v,mv,fs,ds,ss,prefixRun,dataRun,sharedRun,ts ▸ et⟩⟩

/-- Conversely these native returns give the return of the entire public schedule with its exact trace. -/
theorem WriterHistory.runs (H : WriterHistory n bits pub mac r m es t mt) : Runs pub mac (scheduleGroups n bits) r m es t mt := by
  rw [H.chronological]
  apply (Runs.block_append_iff (List.cons_ne_nil _ _ : beforeWriters n bits ≠ []) (by decide : [DataWriter.program,SharedRows.program] ≠ [])).mpr
  exact H.prefixRun.seq (H.dataRun.seq H.sharedRun)

/-- The native data compiler's address and width constraints on its genuine input image. -/
structure DataReady (pub : Arg → Word w) (m : Memory w) : Prop where
  frame : (pub 0).val+72 < 2^w
  teams : 0 < (DataWriter.layout (readings pub) (readings m)).pins.teams
  stride : (DataWriter.layout (readings pub) (readings m)).pins.stride < 2^w
  output : let d := DataWriter.layout (readings pub) (readings m)
           d.output+d.count*7 < 2^w
  separate : DataWriter.Separate (DataWriter.layout (readings pub) (readings m)) (readings m)
  rows : let d := DataWriter.layout (readings pub) (readings m)
         ∀ i < d.count, DataWriter.RowFits w d (readings m) i

/-- The actual compiler return is the complete seven-word record prefix, plus its published row count. -/
theorem WriterHistory.dataImage (H : WriterHistory n bits pub mac r m es t mt) (ok : DataReady pub H.dataInput) :
    H.sharedInput = DataWriter.publish (DataWriter.layout (readings pub) (readings H.dataInput)) pub H.dataInput := by
  obtain ⟨_,_,run,_⟩ := DataWriter.program_runs pub mac H.dataRegs H.dataInput ok.frame ok.teams ok.stride ok.output ok.separate ok.rows
  exact (H.dataRun.unique_of_deterministic (by decide) run).2.2

/-- The real completed schedule contains the shared suffix written directly after the populated data prefix. -/
theorem WriterHistory.emitted (H : WriterHistory n bits pub mac r m es t mt) (ok : DataReady pub H.dataInput)
    (g : SharedRows.Layout) (base : (pub 0).val = g.frame)
    (fit : g.Fits w (readings (DataWriter.publish (DataWriter.layout (readings pub) (readings H.dataInput)) pub H.dataInput)))
    (fields : g.Fields (readings (DataWriter.publish (DataWriter.layout (readings pub) (readings H.dataInput)) pub H.dataInput))) :
    g.Emitted (readings (DataWriter.publish (DataWriter.layout (readings pub) (readings H.dataInput)) pub H.dataInput)) (readings mt) := by
  have eqn := H.dataImage ok
  rw [← eqn] at fit fields ⊢
  exact (((SharedRows.run_program pub mac g H.sharedRegs H.sharedInput fit base fields).asTest (by decide)).sound H.sharedRun).2

/-- The matching forward construction. The inputs are measured at the real return of the prefix;
both descriptor writers then run with no additional choices. -/
theorem scheduleGroups_complete_writers {u : Bank w} {mu : Memory w} {ps : List (TeamRAM.Event w)}
    (prefixRun : Runs pub mac (.block (beforeWriters n bits)) r m ps u mu) (ok : DataReady pub mu)
    (g : SharedRows.Layout) (base : (pub 0).val = g.frame)
    (fit : g.Fits w (readings (DataWriter.publish (DataWriter.layout (readings pub) (readings mu)) pub mu)))
    (fields : g.Fields (readings (DataWriter.publish (DataWriter.layout (readings pub) (readings mu)) pub mu))) :
    ∃ es t mt, Runs pub mac (scheduleGroups n bits) r m es t mt ∧
      g.Emitted (readings (DataWriter.publish (DataWriter.layout (readings pub) (readings mu)) pub mu)) (readings mt) := by
  obtain ⟨ds,v,rd,_⟩ := DataWriter.program_runs pub mac u mu ok.frame ok.teams ok.stride ok.output ok.separate ok.rows
  obtain ⟨ss,t,mt,rs,_,image⟩ := SharedRows.run_program pub mac g v _ fit base fields
  exact ⟨_,t,mt,(WriterHistory.mk u mu v _ ps ds ss prefixRun rd rs rfl).runs,image⟩

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
