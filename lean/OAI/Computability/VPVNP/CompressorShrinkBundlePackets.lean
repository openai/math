import OAI.Computability.VPVNP.CompressorBlockIndex
import OAI.Computability.VPVNP.CompressorScriptWindow
import OAI.Computability.VPVNP.CompressorSourceScanned
import OAI.Computability.VPVNP.CompressorShrinkBundleCertificates

/-!
# Dense shrinking packets at their global block-program ordinals

The window starts after the three header visits and six greedy visits of
the selected shrinking substep. Each packet uses the corresponding worker
table, physical bank and number of empty choice tapes from the native run.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkBundlePackets

open BurstRAM BlockPlanner Compression ShrinkBundlePlan SourceOnline DescriptorSpace
open ShrinkBundlePlan.Scheduled (Stage)
open scoped Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)

/-- The fixed block-program geometry used to locate the shrinking bundle's level headers and
operand tables. -/
abbrev shape := BlockProgram.geometry B
/-- The scratch-table-zero address expression used as the origin of bundle preparation in this
substep. -/
abbrev origin := BlockProgram.arena B i.val 0
/-- The input degree exponent selecting the dimensions of this substep's bundle workers. -/
abbrev exponent := ShrinkBlockInputs.a i
/-- The planned catalog visits for the eleven dense bundle stages at this shrinking substep. -/
abbrev entries := ShrinkBundlePlan.Scheduled.order.map (Stage.visit (shape B) i.val (exponent i) (origin B i))
private abbrev earlier := BlockHeaderPlan.substep (shape B) i.val (.shrink (exponent i) (ShrinkBlockInputs.b i)) ++
  GreedyLevelPlan.visits (shape B) i.val (exponent i) (origin B i)

private theorem substep_split : ∃ suffix, BlockProgram.shrink B i = earlier B i ++ entries B i ++ suffix := by
  unfold BlockProgram.shrink ShrinkBlockInputs.beforeSlices earlier entries
  rw [ShrinkBundlePlan.Scheduled.order_visits]
  simp only [List.append_assoc]
  exact ⟨_,rfl⟩

/-- Locate all dense bundle visits together in the fixed block, after the header and greedy
passes and before later shrinking work. -/
def window : Window (BlockProgram.script B) (entries B i) where
  before := BlockIndex.earlier B i ++ earlier B i
  after := (substep_split B i).choose ++ BlockIndex.later B i
  block := by
    have h := congrArg (fun xs ↦ BlockIndex.earlier B i ++ xs ++ BlockIndex.later B i) (substep_split B i).choose_spec
    exact (BlockIndex.split_block B i).trans (h.trans (by simp only [List.append_assoc]))

/-- The ordered bundle stages from preliminary placement to the absolute motif-ID scan. -/
abbrev stages := ShrinkBundlePlan.Scheduled.order
local notation "A" => BlockProgram.script B

/-- Reindex a stage's position in the bundle order as a position in the matching visit list. -/
abbrev localIndex (j : Fin stages.length) : Fin (entries B i).length := Fin.cast (by simp [entries,stages]) j

/-- The global script index of the bundle stage at the given position in this substep's window. -/
def index (j : Fin stages.length) : Fin (A).size := (window B i).index (localIndex B i j)

theorem index_visit (j : Fin stages.length) : (A).visit (index B i j) =
    (stages[j.val]).visit (shape B) i.val (exponent i) (origin B i) := by
  simpa only [index,localIndex,entries,List.getElem_map,Fin.val_cast] using (window B i).visit (localIndex B i j)

theorem ordinal (block : ℕ) (j : Fin stages.length) :
    let ord := (A).initial.length+block*(A).block.length+(BlockIndex.earlier B i).length+9+j.val
    (Schedule.Online.calendar (A).plan).phase ord = (index B i j).val ∧
    (Schedule.Online.calendar (A).plan).level ord = block := by
  have nine : (earlier B i).length = 9 := rfl
  have pos : ((window B i).position (localIndex B i j)).val = (BlockIndex.earlier B i).length+9+j.val := by
    change (BlockIndex.earlier B i ++ earlier B i).length+j.val = _
    rw [List.length_append,nine]
  have he := (A).block_phase block ((window B i).position (localIndex B i j))
  rw [pos] at he
  simpa only [index,Window.index,Nat.add_assoc] using he

variable {g w : ℕ} (X : State (exponent i) (packingLaneBits (exponent i) g)) (T : IncidenceDirectory w) (start : ℕ)
local notation "Z" => ShrinkInput.plan X start
local notation "worker" => Stage.visit (shape B) i.val (exponent i) (origin B i)

/-- Build the source packet for one bundle stage with its global worker index, physical operand
bank, cursor range and empty choice tapes. -/
def visit (j : Fin stages.length) : SourceOnline.Visit A w :=
  let s := stages[j.val]
  let v := worker s
  SourceOnline.Visit.ofWorker (index B i j) v.worker (congrArg BlockPlanner.Visit.worker (index_visit B i j))
    (v.worker.pcs-1) 0 (s.limit X start : Word w)
    (s.bank X T start ∘ Fin.cast (s.params (shape B) i.val (exponent i) (origin B i))) (List.replicate (s.limit X start) [])

theorem runs (j : Fin stages.length) (mem : Memory w) (rs : List (Report w))
    (h : ShrinkBundlePlan.Scheduled.Source X T start (shape B) i.val (origin B i) stages[j.val] mem rs) :
    (visit B i X T start j).Runs mem rs := by
  unfold visit
  exact (SourceOnline.Visit.ofWorker_runs _ _ (congrArg BlockPlanner.Visit.worker (index_visit B i j)) _ _ _ _ _ mem rs).mpr h

/-- Runtime expressions for the global occurrence give the physical packet's
two cursors and operand bank, including the cast from the catalog arity. -/
theorem field_values (j : Fin stages.length) {pub : Fin 5 → Word w} {state : Word w} {mem : Memory w}
    (h : ShrinkBundlePlan.Reads X (shape B) i.val (origin B i) pub state mem start T) (fit : (Z).stop < 2^w) :
    let v := visit B i X T start j
    let raw := (A).visit (index B i j)
    raw.initial.eval pub state mem = v.start ∧ raw.stop.eval pub state mem = v.stop ∧
      ∀ u, (raw.params u).eval pub state mem = v.params u := by
  let s := stages[j.val]
  let raw := worker s
  have eq := index_visit B i j
  have hstart : raw.initial.eval pub state mem = 0 := by cases hs : s <;> simp only [raw,hs] <;> rfl
  have hstop := s.stop X h
  have operands := s.operands X h fit
  dsimp only
  refine ⟨(congrArg (fun z : BlockPlanner.Visit ↦ z.initial.eval pub state mem) eq).trans hstart,
    (congrArg (fun z : BlockPlanner.Visit ↦ z.stop.eval pub state mem) eq).trans hstop,?_⟩
  intro u
  have atParam {v z : BlockPlanner.Visit} (eqn : v = z) (n : Fin v.worker.params) :
      v.params n = z.params (Fin.cast (congrArg (fun x : BlockPlanner.Visit ↦ x.worker.params) eqn) n) := by
    subst z; rfl
  rw [atParam eq u]
  exact congrFun operands _

private theorem limit_fit (j : Stage) (fit : (Z).stop < 2^w) : j.limit X start < 2^w := by
  have scalars := (Z).scalarFits Fintype.card_pos fit
  have sum := BundleKeys.bundle_rows_total (Fintype.card X.Base) (exponent i) g
  change (Z).B*thickCount (exponent i)+(Z).B*(Z).Q = (Z).A at sum
  have hf := scalars.1
  have hb := scalars.2.1
  cases j <;> first
    | exact hf | exact hb | exact (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)).trans_lt hf
    | change (Z).B*thickCount (exponent i) < 2^w; omega | change (Z).B*(Z).Q < 2^w; omega

/-- A finite worker-fuel cap for this substep, independent of input length. -/
def maxFuel : ℕ := Finset.univ.sup fun j : Fin stages.length ↦ (worker stages[j.val]).worker.pcs-1

theorem visit_checked (L : DescriptorSpace.Layout) (j : Fin stages.length) (mem : Memory w) (rs : List (Report w))
    (fit : (Z).stop < 2^w) (before : levelStart L 0 ≤ start) {cap : ℕ}
    (clock : SourceOnline.scanCap A (maxFuel B i) ≤ cap)
    (cert : ShrinkBundlePlan.Scheduled.Certified X T start (levelStart L 0) (shape B) i.val (origin B i)
      stages[j.val] mem rs) :
    SourceOnline.Checked A L cap ⟨visit B i X T start j,mem,rs⟩ := by
  let stage := stages[j.val]
  let pkt : SourceWalk.Packet (SourceOnline.Visit A w) w := ⟨visit B i X T start j,mem,rs⟩
  have fuel : pkt.stage.fuel = (worker stage).worker.pcs-1 := rfl
  have positive : 0 < pkt.stage.fuel := by
    rw [fuel]; cases stage <;> change 0 < _ + 2 - 1 <;> omega
  have budget : pkt.stage.fuel ≤ maxFuel B i := Finset.le_sup (f := fun l : Fin stages.length ↦ (worker stages[l.val]).worker.pcs-1)
    (Finset.mem_univ j)
  obtain ⟨rc,dc⟩ := SourceOnline.scanCap_clocks (p := pkt) (maxFuel B i) budget clock
  exact SourceOnline.Checked.ofScanned (p := pkt) positive rc dc (first := 0) rfl rfl (limit_fit i X start stage fit)
    cert.2.1 cert.2.2.1 cert.2.2.2 (fun _ hx ↦ hx.1) (fun _ hx ↦ before.trans hx.1)

theorem checked_walk (L : DescriptorSpace.Layout) {cap : ℕ} (clock : SourceOnline.scanCap A (maxFuel B i) ≤ cap)
    {m : Memory w} (r : ShrinkInput.Run X T start m) {abs : List (Report w)} (last : AbsoluteRun r abs)
    (room : ShrinkInput.stop X start < 2^w) (low : ∀ c, levelStart L 0 ≤ (T.column c).val) :
    SourceWalk (fun v mem rs ↦ v.Runs mem rs ∧ SourceOnline.Checked A L cap ⟨v,mem,rs⟩ ∧
      SourceTransport.Writes (fun x ↦ start ≤ x ∧ x < ShrinkInput.stop X start) (eventLog rs))
      (List.ofFn (visit B i X T start)) r.greedy.post
      (ShrinkBundlePlan.Scheduled.preparationReports X T start r ++ abs) := by
  have raw := ShrinkBundlePlan.Scheduled.certified_sources r (shape B) i.val (origin B i) last (levelStart L 0) low room
  have before : levelStart L 0 ≤ start := (low 5).trans ((Nat.le_add_right ..).trans (r.greedy.old 5))
  have fit := (ShrinkInput.range_bounds X start).2.2.2.trans_lt room
  apply raw.mapAt
  intro j mem rs h
  exact ⟨runs B i X T start j mem rs h.1, visit_checked B i X T start L j mem rs fit before clock h,h.2.2.2⟩

private theorem packet_chain {script : Script} (L : DescriptorSpace.Layout) (cap low top : ℕ)
    (first raw : Memory w) (ps : List (SourceWalk.Packet (SourceOnline.Visit script w) w))
    (prior : ∀ j < low, raw j = first j)
    (chain : SourceWalk.Chronological (fun v mem rs ↦ v.Runs mem rs ∧
      SourceOnline.Checked script L cap ⟨v,mem,rs⟩ ∧ SourceTransport.Writes (fun j ↦ low ≤ j ∧ j < top) (eventLog rs))
      raw ps) :
    SourceWalk.Chronological SourceOnline.Visit.Runs raw ps ∧
      ∀ p ∈ ps, SourceOnline.Checked script L cap p ∧ ∀ j < low, p.input j = first j := by
  induction ps generalizing raw with
  | nil => exact ⟨trivial,by simp⟩
  | cons p ps ih =>
    obtain ⟨atEntry,⟨run,check,writes⟩,tail⟩ := chain
    have entry (j : ℕ) (hj : j < low) : p.input j = first j := (congrFun atEntry j).trans (prior j hj)
    have next (j : ℕ) (hj : j < low) : p.output j = first j :=
      (SourceTransport.after_outside p.input writes (by omega : ¬ (low ≤ j ∧ j < top))).trans (entry j hj)
    obtain ⟨chron,checked⟩ := ih p.output next tail
    refine ⟨⟨atEntry,run,chron⟩,?_⟩
    intro pkt hp
    rcases List.mem_cons.mp hp with rfl | h
    · exact ⟨check,entry⟩
    · exact checked _ h

/-- All global packets run on consecutive data memories. Each packet retains
the physical header, row-count cell and pitch whenever they precede the arena. -/
theorem packets (L : DescriptorSpace.Layout) (cap : ℕ) (clock : SourceOnline.scanCap A (maxFuel B i) ≤ cap)
    {m : Memory w} (r : ShrinkInput.Run X T start m) (abs : List (Report w)) (last : AbsoluteRun r abs)
    (room : ShrinkInput.stop X start < 2^w) (low : ∀ c, levelStart L 0 ≤ (T.column c).val) :
    ∃ ps : List (SourceWalk.Packet (SourceOnline.Visit A w) w),
      ps.map SourceWalk.Packet.stage = List.ofFn (visit B i X T start) ∧
      ps.flatMap SourceWalk.Packet.reports = ShrinkBundlePlan.Scheduled.preparationReports X T start r ++ abs ∧
      SourceWalk.Chronological SourceOnline.Visit.Runs r.greedy.post ps ∧
      (∀ p ∈ ps, SourceOnline.Checked A L cap p ∧ ∀ j < start, p.input j = r.greedy.post j) ∧
      after r.greedy.post (eventLog (ps.flatMap SourceWalk.Packet.reports)) = after r.post (eventLog abs) := by
  obtain ⟨ps,order,logs,chain⟩ := (checked_walk B i X T start L clock r last room low).packets
  obtain ⟨chron,check⟩ := packet_chain L cap start (ShrinkInput.stop X start) r.greedy.post r.greedy.post ps
    (fun _ _ ↦ rfl) chain
  refine ⟨ps,order,logs,chron,check,?_⟩
  rw [logs,SourceWalk.after_append,ShrinkBundlePlan.Scheduled.preparation_post]

end CompressorRecords.ShrinkBundlePackets

end

end VPVNP
end Computability
end OAI
