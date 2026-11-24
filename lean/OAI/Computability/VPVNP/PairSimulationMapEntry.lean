import OAI.Computability.VPVNP.PairSimulationMapEntryProgram
import OAI.Computability.VPVNP.PairSimulationMapNativeClock
import OAI.Computability.VPVNP.PairSimulationMapDriverExact
import OAI.Computability.VPVNP.PairSimulationPrivateScratch

/-!
# Executing an entire grouped motif entry in private RAM

All incident half-wires may be arbitrary. The native program checks selectors,
loads each selected matrix row, compares the full width vector, and increments
one counter per output label. The rejecting paths leave every counter intact.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapEntry.Program

open BurstRAM BurstRAM.PrivateRAM PrimedCounter.GuessWord MotifSelector MotifEntry
open MotifBlocks MotifGrid MotifConversion MapPortAgreement MapResidentAgreement
open scoped Fin.CommRing

variable {K J D E : Type} [Field K] [Fintype J] [DecidableEq J] [Fintype D] [Fintype E]
  {src dst : D → J} {G : Supply J E} {p₀ : D → ℚ} {q₀ : E → ℚ} {H H' : ℝ}
  {B : FixedBlock K src dst G (realWidths p₀) (realWidths q₀) H H'}
  {z : B.grid.demands} {j : J} {w p r k u t : ℕ} (P : Program B z j p r k)

/-- All per-call numerical locations, including separate selector and label arrays. -/
structure Workspace (P : Program B z j p r k) (demand : D → ℕ) (v : E → ℕ)
    (d : DemandBits src dst demand j) (x : Half G (fun e ↦ Fin (v e + u * B.selectorBits) → Bool) j)
    (t w : ℕ) where
  /-- Private word address of each incident supply half-wire's first bit, used with its payload
  width to locate the selector suffix. -/
  portBase : Port G j → BurstRAM.Word w
  /-- Private base address of the incident-port directory whose entries point to the selector
  suffixes. -/
  directory : BurstRAM.Word w
  /-- Private base address of each demand or supply endpoint's bit slice, used when reading a
  selected matrix row. -/
  base : MapLookup.LabelField D E → ℕ
  /-- Start address of the private selector ordinal array written by the decoder and read by
  the row driver. -/
  source : ℕ
  /-- Start address of the private parameter label array written by the row driver and read by
  the histogram loop. -/
  target : ℕ
  /-- Base address of the private counters indexed by parameter ordinal. -/
  hist : ℕ
  portsFit : (ports G j P.edgeOrder).length < 2 ^ w
  tagFit : u * B.selectorBits < 2 ^ w
  anchorFit :
    (portBase (anchorPort G j)).val + (v (edge (anchorPort G j)) + u * B.selectorBits) < 2 ^ w
  anchorApart :
    (portBase (anchorPort G j)).val + (v (edge (anchorPort G j)) + u * B.selectorBits) ≤ source ∨
    source + u ≤ (portBase (anchorPort G j)).val
  ordinalFit : source + u < 2 ^ w
  labelFit : target + u < 2 ^ w
  histogramFit : hist + t ≤ 2 ^ w
  ordinalsBefore : source + u ≤ target
  sourceHistApart : source + u ≤ hist ∨ hist + t ≤ source
  targetHistApart : target + u ≤ hist ∨ hist + t ≤ target
  inputApart : ∀ (θ : Fin u → Selector B) f
    (l : Fin ((MapRowLoop.buffers B z j demand v d x base θ 0).len f)),
    ((base f + l.val : ℕ) : BurstRAM.Word w).val < source
  fieldsFit : ∀ (θ : Fin u → Selector B) (i : Fin u), MapRowFields.Fits MapRow.group
    (Sum.elim (baseDemand B z) (basePayload B (θ i)))
    (MapRowLoop.buffers B z j demand v d x base θ i.val) w
  totalsFit : ∀ (θ : Fin u → Selector B) e, totalWidth (basePayload B) θ e < 2 ^ w

variable {demand : D → ℕ} {v : E → ℕ} {d : DemandBits src dst demand j}
  {x : Half G (fun e ↦ Fin (v e + u * B.selectorBits) → Bool) j}
  (X : Workspace P demand v d x t w)

/-- Resident pointers, bit data, zero offsets and full-vector comparison targets.
Every deterministic stage may now execute even if the incident data are invalid. -/
structure Ready (c : Config w p r) : Prop where
  selector : P.selector.Ready P.edgeOrder x X.portBase X.directory X.source c
  row : ∀ θ,
    MapRowFields.Resident P.bank.rowReg (MapRowLoop.buffers B z j demand v d x X.base θ 0) c
  source : c.reg (P.driver.reg 0) = (X.source : BurstRAM.Word w)
  stop : c.reg (P.driver.reg 1) = ((X.source + u : ℕ) : BurstRAM.Word w)
  target : c.reg (P.driver.reg 2) = (X.target : BurstRAM.Word w)
  one : c.reg (P.driver.reg 3) = 1
  expected : ∀ e, (c.reg (P.expected e)).val = v e
  histogram : MapFinish.HistogramReady (u := u) P.histReg X.target X.hist c

omit [DecidableEq J] in
private theorem selector_reg {sel lab : ℕ} {c m : Config w p r}
    (frame : P.selector.Frame sel lab c m) {a : Fin r} (save : P.SelectorSaved a) :
    m.reg a = c.reg a := frame.regs a save.1 (save.2 0) (save.2 1) (save.2 2) (save.2 5) (save.2 6)

/-- The exit and the value of each histogram cell on this particular path. -/
def Effect (c out : Config w p r) (hist : ℕ) : Option (List (Fin t)) → Prop
  | none => out.pc = P.bad ∧ ∀ l : Fin t, out.privateMem ((hist + l.val : ℕ) : BurstRAM.Word w) =
      c.privateMem ((hist + l.val : ℕ) : BurstRAM.Word w)
  | some names => out.pc = P.done ∧ ∀ l : Fin t,
      out.privateMem ((hist + l.val : ℕ) : BurstRAM.Word w) =
        c.privateMem ((hist + l.val : ℕ) : BurstRAM.Word w) + (names.count l : BurstRAM.Word w)

/-- Value and histogram effect of the entire map entry, on the very same
machine for all inputs, up to its success or failure continuation. -/
structure Runs (M : Machine w p r k) (c : Config w p r) (hist cap : ℕ)
    (value : Option (List (Fin t))) : Prop where
  path : ∃ n out, n ≤ cap ∧ Prefix M c (List.replicate n .tick) out ∧
    out.persistent = c.persistent ∧ P.Effect c out hist value

/-- The same path both executes the map and preserves each saved private cell. -/
structure RunsFramed (M : Machine w p r k) (c : Config w p r) (hist cap : ℕ)
    (save : BurstRAM.Word w → Prop) (value : Option (List (Fin t))) : Prop where
  path : ∃ n out, n ≤ cap ∧ Prefix M c (List.replicate n .tick) out ∧
    out.persistent = c.persistent ∧ (∀ a, save a → out.privateMem a = c.privateMem a) ∧
    P.Effect c out hist value

omit [DecidableEq J] in
theorem RunsFramed.forget {M : Machine w p r k} {c : Config w p r} {hist cap : ℕ}
    {save : BurstRAM.Word w → Prop} {value : Option (List (Fin t))}
    (h : P.RunsFramed M c hist cap save value) : P.Runs M c hist cap value := by
  obtain ⟨n, out, bound, pre, per, _, effect⟩ := h.path
  exact ⟨n, out, bound, pre, per, effect⟩

/-- The map writes only the selector, label and histogram arrays. -/
def Outside (a : BurstRAM.Word w) : Prop :=
  (a.val < X.source ∨ X.source + u ≤ a.val) ∧
  (a.val < X.target ∨ X.target + u ≤ a.val) ∧
  ∀ l : Fin t, a ≠ ((X.hist + l.val : ℕ) : BurstRAM.Word w)

/-- Exact postconditions and the exterior frame hold on the same native prefix. -/
structure RunsPost (M : Machine w p r k) (c : Config w p r) (hist cap : ℕ)
    (save : BurstRAM.Word w → Prop) (value : Option (List (Fin t)))
    (post : PrivateScratch.Memory w → Prop) : Prop where
  path : ∃ n out, n ≤ cap ∧ Prefix M c (List.replicate n .tick) out ∧
    out.persistent = c.persistent ∧ (∀ a, save a → out.privateMem a = c.privateMem a) ∧
    P.Effect c out hist value ∧ post out.privateMem

omit [DecidableEq J] in
theorem RunsPost.framed {M : Machine w p r k} {c : Config w p r} {hist cap : ℕ}
    {save : BurstRAM.Word w → Prop} {value : Option (List (Fin t))}
    {post : PrivateScratch.Memory w → Prop} (h : P.RunsPost M c hist cap save value post) :
    P.RunsFramed M c hist cap save value := by
  obtain ⟨n, out, bound, pre, per, frame, effect, _⟩ := h.path
  exact ⟨n, out, bound, pre, per, frame, effect⟩

/-- Exact memory on a successful map: selector ordinals and labels are stored in
copy order before each emitted label increments its histogram bin. -/
noncomputable def successMemory (selector : Selector B ↪ BurstRAM.Word w)
    (ord : (parameterData B).Entry → Fin t) (θ : Fin u → Selector B)
    (old : PrivateScratch.Memory w) : PrivateScratch.Memory w :=
  let labels := fun i ↦ ord (MapStream.readRow src dst (baseDemand B z) demand G
    (basePayload B) (lookup B z) v j d x i (θ i)
    (fun e ↦ offset (fun l ↦ basePayload B (θ l) e) i))
  PrivateLabels.accumulate X.hist (List.ofFn labels)
    (PrivateScratch.write (X.target : BurstRAM.Word w) (fun i ↦ ((labels i).val : BurstRAM.Word w))
      (PrivateScratch.write (X.source : BurstRAM.Word w) (fun i ↦ selector (θ i)) old))

/-- The successful selector and its complete width vector determine every written word. -/
def Success (selector : Selector B ↪ BurstRAM.Word w) (ord : (parameterData B).Entry → Fin t)
    (old new : PrivateScratch.Memory w) : Prop :=
  ∀ θ : Fin u → Selector B, (selectorRun G (selectorTable B) (selectorCode B) v j x).1 = some θ →
    (∀ e, v e = totalWidth (basePayload B) θ e) → new = P.successMemory X selector ord θ old

theorem successMemory_congr_at (selector : Selector B ↪ BurstRAM.Word w)
    (ord : (parameterData B).Entry → Fin t) (θ : Fin u → Selector B)
    {old old' : PrivateScratch.Memory w} (a : BurstRAM.Word w) (ha : old a = old' a) :
    P.successMemory X selector ord θ old a = P.successMemory X selector ord θ old' a :=
  PrivateScratch.accumulate_congr_at _ _ a
    (PrivateScratch.write_congr_at _ _ a (PrivateScratch.write_congr_at _ _ a ha))

/-- The exact row-driver clock depends on input bits, decoded selectors, and the fixed
public table. The argument bases and the contents of exterior memory play no role. -/
noncomputable def driverTicks (d : DemandBits src dst demand j)
    (x : Half G (fun e ↦ Fin (v e + u * B.selectorBits) → Bool) j) (θ : Fin u → Selector B)
    (fd : ∀ e, baseDemand B z e ≤ w) (fs : ∀ s e, basePayload B s e ≤ w)
    (words : Fin k → BurstRAM.Word w) : ℕ :=
  P.driver.exactSteps θ (MapRowLoop.rowSteps B z j demand v d x θ fd fs P.bank.keyPort words)

set_option maxHeartbeats 1200000 in
-- The dependent register and memory types unfold through each fixed row-bank phase.
/-- Run the selected rows once and expose the private labels, widths, and histogram operands
together with the exact number of executed instructions. -/
theorem runSelectedRows (M : Machine w p r k) (linked : P.Linked M) (separate : P.Separate)
    (selector : Selector B ↪ BurstRAM.Word w) (ordinal : (parameterData B).Entry → Fin t)
    (fb : B.selectorBits ≤ w) (fd : ∀ e, baseDemand B z e ≤ w) (fs : ∀ s e, basePayload B s e ≤ w)
    (pub : P.Public M selector (fun s ↦ ((ordinal s).val : BurstRAM.Word w)) fb fd fs)
    (c : Config w p r) (ready : P.Ready X c) (θ : Fin u → Selector B)
    (m : Config w p r) (frame : P.selector.Frame X.source u c m)
    (hm : m.pc = P.selector.decoder.done)
    (hselWords : ∀ i : Fin u, m.privateMem ((X.source + i.val : ℕ) : BurstRAM.Word w) =
      M.publicData (P.selector.decoder.name (θ i))) :
    let labels := fun i ↦ ordinal (MapStream.readRow src dst (baseDemand B z) demand G
      (basePayload B) (lookup B z) v j d x i (θ i)
      (fun e ↦ offset (fun l ↦ basePayload B (θ l) e) i))
    let ticks := P.driverTicks d x θ fd fs M.publicData
    ∃ mid, ticks ≤ P.driver.visitCap (MapRowLoop.rowCap B z j) * u + 1 ∧
      Prefix M m (List.replicate ticks .tick) mid ∧ mid.pc = P.driver.checkWidths ∧
      (∀ e, (mid.reg (P.bank.rowReg (.offset (.inr e)))).val = totalWidth (basePayload B) θ e) ∧
      (∀ e, (mid.reg (P.expected e)).val = v e) ∧
      MapFinish.HistogramReady (u := u) P.histReg X.target X.hist mid ∧
      (∀ i : Fin u, mid.privateMem ((X.target + i.val : ℕ) : BurstRAM.Word w) =
        ((labels i).val : BurstRAM.Word w)) ∧
      (∀ a : BurstRAM.Word w, a.val < X.target ∨ X.target + u ≤ a.val →
        mid.privateMem a = m.privateMem a) ∧ mid.persistent = m.persistent := by
  classical
  dsimp only
  let A := P.bank
  let drive := P.driver
  let inv : ℕ → Config w p r → Prop := fun n ↦
    MapRowFields.Resident A.rowReg (MapRowLoop.buffers B z j demand v d x X.base θ n)
  let labels := fun i ↦ ordinal (MapStream.readRow src dst (baseDemand B z) demand G
    (basePayload B) (lookup B z) v j d x i (θ i)
    (fun e ↦ offset (fun l ↦ basePayload B (θ l) e) i))
  let names := fun i ↦ ((labels i).val : BurstRAM.Word w)
  let save := fun a ↦ (∃ e, a = P.expected e) ∨ (∃ i, a = P.histReg i)
  have ext (a) (h : save a) (b) : a ≠ A.register b := by
    rcases h with ⟨e, rfl⟩ | ⟨i, rfl⟩
    · exact separate.expectedRow e b
    · exact separate.histRow i b
  have rowFrame : MapRowLoop.OutsideRowWrites A.rowReg save := fun a ha ↦
    ⟨ext a ha _, fun _ ↦ ext a ha _, ext a ha _, ext a ha _, ext a ha _, fun _ ↦ ext a ha _⟩
  have driveFrame : drive.OutsideWrites save := fun a ha ↦
    ⟨ext a ha _, ext a ha _, ext a ha _, ext a ha _⟩
  obtain ⟨dlink, rlink⟩ := A.linked P.loc M linked.body
  obtain ⟨inj, widths, keys, output⟩ := A.public_spec fd fs selector _ M pub.rows
  have run := MapRowLoop.rowRunsExactFramed B z j demand v d x X.base θ drive A.rowReg
    (A.registerLayout P.loc) (fun s ↦ ((ordinal s).val : BurstRAM.Word w)) A.widthPort
    A.keyPort A.namePort (A.sites P.loc) M drive.bad
    (fun _ ↦ rfl) rlink fd fs widths keys output (X.fieldsFit θ) save rowFrame
  have stable := MapRowLoop.stable B z j demand v d x X.base θ drive A.rowReg
    (A.registerLayout P.loc) X.target (fun f l ↦ .inl ((X.inputApart θ f l).trans_le
      ((Nat.le_add_right _ _).trans X.ordinalsBefore)))
  have kept (a) : m.reg (A.register a) = c.reg (A.register a) :=
    selector_reg P frame (separate.bank a)
  have start : inv 0 m := by
    let h := ready.row θ
    exact ⟨(kept _).trans h.one, fun f ↦ (kept _).trans (h.base f),
      fun f ↦ (kept _).trans (h.dataEnd f), fun g ↦ (kept _).trans (h.offset g),
      fun f l ↦ (frame.memory _ (.inl (X.inputApart θ f l))).trans (h.data f l)⟩
  have dready : drive.Ready M θ names X.source X.target 0 m :=
    ⟨hm.trans linked.selectorExit, (kept _).trans ready.source, (kept _).trans ready.stop,
      (kept _).trans ready.target, (kept _).trans ready.one, fun i ↦
        (hselWords i).trans (pub.name _), fun i hi ↦ (Nat.not_lt_zero _ hi).elim⟩
  obtain ⟨mid, h₂, rows, widthPC, endInv, saved, labelWords, memory, hp⟩ :=
    MapDriver.Program.native_exact_framed θ
      (MapRowLoop.rowSteps B z j demand v d x θ fd fs A.keyPort M.publicData) dlink inj
      (fun i ↦ Finset.mem_toList.mpr (Finset.mem_univ _)) names
      inv X.source X.target (MapRowLoop.rowCap B z j) stable save driveFrame run X.ordinalFit
      X.labelFit (.inl X.ordinalsBefore) m dready start
  have totals (e) : (mid.reg (A.rowReg (.offset (.inr e)))).val =
      totalWidth (basePayload B) θ e := by
    rw [endInv.offset]
    simp only [MapRowLoop.buffers, Sum.elim_inr, MapRowLoop.prefix_last]
    exact Nat.mod_eq_of_lt (X.totalsFit θ e)
  have he (e) : (mid.reg (P.expected e)).val = v e := by
    rw [saved _ (.inl ⟨e, rfl⟩), selector_reg P frame (separate.expected e), ready.expected]
  have hh (i) : mid.reg (P.histReg i) = c.reg (P.histReg i) :=
    (saved _ (.inr ⟨i, rfl⟩)).trans (selector_reg P frame (separate.histogram i))
  have hready : MapFinish.HistogramReady (u := u) P.histReg X.target X.hist mid :=
    ⟨(hh 0).trans ready.histogram.cursor, (hh 1).trans ready.histogram.stop,
      (hh 2).trans ready.histogram.base, (hh 3).trans ready.histogram.one⟩
  exact ⟨mid, h₂, rows, widthPC, totals, he, hready, labelWords, memory, hp⟩

set_option maxHeartbeats 1200000 in
-- The public keys and memory slices of the same grouped matrix reduce in four dependent phases.
/-- Every path uses genuine finite-table instructions and its cap includes
the rejecting paths on disagreement, unused tags and false payload totals. -/
theorem native_post (M : Machine w p r k) (linked : P.Linked M) (separate : P.Separate)
    (selector : Selector B ↪ BurstRAM.Word w) (ordinal : (parameterData B).Entry → Fin t)
    (fb : B.selectorBits ≤ w) (fd : ∀ e, baseDemand B z e ≤ w) (fs : ∀ s e, basePayload B s e ≤ w)
    (pub : P.Public M selector (fun s ↦ ((ordinal s).val : BurstRAM.Word w)) fb fd fs)
    (c : Config w p r) (ready : P.Ready X c) :
    P.RunsPost M c X.hist (MapNativeClock.cap B z j u) (P.Outside X)
      ((MotifEntry.run src dst (baseDemand B z) demand G (basePayload B) (lookup B z)
        (selectorTable B) (selectorCode B) v j d x).1.map (List.map ordinal))
      (P.Success X selector ordinal c.privateMem) := by
  classical
  obtain ⟨n₁, m, h₁, pre, frame, res⟩ :=
    (P.selector.native linked.selector P.edgeOrder fb (selectorCode B) pub.key x X.portBase
      X.directory X.source c ready.selector X.portsFit X.tagFit X.anchorFit X.ordinalFit
      X.anchorApart).path
  let sel := (selectorRun G (selectorTable B) (selectorCode B) v j x).1
  rw [linked.table] at res
  have hfirst : n₁ ≤ (7 * (u * B.selectorBits) + 6) * (2 * Fintype.card E) + 3 +
      ((6 * B.selectorBits + 1 + (2 * (selectorTable B).length + 1) + 5) * u + 1) := by
    unfold AnchorDecode.Program.visitCap at h₁
    rw [linked.table] at h₁
    exact h₁.trans (Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.mul_le_mul_left _ (ports_length_le G j P.edgeOrder)) _) _)
  have address (l : Fin t) : ((X.hist + l.val : ℕ) : BurstRAM.Word w).val = X.hist + l.val :=
    Nat.mod_eq_of_lt (Nat.add_lt_add_left l.isLt X.hist |>.trans_le X.histogramFit)
  have outside (l : Fin t) (atWord : ℕ) (apart : atWord + u ≤ X.hist ∨ X.hist + t ≤ atWord) :
      ((X.hist + l.val : ℕ) : BurstRAM.Word w).val < atWord ∨
        atWord + u ≤ ((X.hist + l.val : ℕ) : BurstRAM.Word w).val := by
    rw [address l]
    have := l.isLt
    omega
  have hsHist (l : Fin t) : m.privateMem ((X.hist + l.val : ℕ) : BurstRAM.Word w) =
      c.privateMem ((X.hist + l.val : ℕ) : BurstRAM.Word w) :=
    frame.memory _ (outside l _ X.sourceHistApart)
  rw [MapFinish.entry_value]
  change P.RunsPost M c X.hist _ (P.Outside X) ((sel.bind _).map _) _
  cases hsel : sel with
  | none =>
    dsimp only [sel] at hsel
    rw [hsel] at res
    refine ⟨n₁, m, hfirst.trans (by unfold MapNativeClock.cap; omega), pre, frame.persistent,
      fun a ha ↦ frame.memory a ha.1, ⟨res.trans linked.selectorBad, hsHist⟩, ?_⟩
    intro θ hit
    rw [hsel] at hit
    cases hit
  | some θ =>
    dsimp only [sel] at hsel
    rw [hsel] at res
    obtain ⟨hm, hselWords⟩ := res
    let labels := fun i ↦ ordinal (MapStream.readRow src dst (baseDemand B z) demand G
      (basePayload B) (lookup B z) v j d x i (θ i)
      (fun e ↦ offset (fun l ↦ basePayload B (θ l) e) i))
    let names := fun i ↦ ((labels i).val : BurstRAM.Word w)
    let n₂ := P.driverTicks d x θ fd fs M.publicData
    obtain ⟨mid, h₂, rows, widthPC, totals, he, hready, labelWords, memory, hp⟩ :=
      P.runSelectedRows X M linked separate selector ordinal fb fd fs pub c ready θ m frame hm
        hselWords
    obtain ⟨n₃, out, h₃, last, per, done⟩ := MapFinish.native (basePayload B) θ v
      (List.ofFn P.edgeOrder)
      (fun e ↦ List.mem_ofFn.mpr ⟨P.edgeOrder.symm e, P.edgeOrder.apply_symm_apply e⟩)
      _ P.expected P.guardTemp M P.guardPC P.histPC P.histReg P.done P.bad linked.guard
      linked.histogram
      X.target X.hist labels mid (widthPC.trans linked.rowExit) totals he hready X.histogramFit
      X.targetHistApart X.labelFit labelWords
    have hmid (l : Fin t) : mid.privateMem ((X.hist + l.val : ℕ) : BurstRAM.Word w) =
        c.privateMem ((X.hist + l.val : ℕ) : BurstRAM.Word w) :=
      (memory _ (outside l _ X.targetHistApart)).trans (hsHist l)
    refine ⟨n₁ + n₂ + n₃, out, ?_, ?_, per.trans (hp.trans frame.persistent), ?_, ?_, ?_⟩
    · simp only [List.length_ofFn] at h₃
      unfold MapNativeClock.cap
      change n₂ ≤ (5 + 2 * (selectorTable B).length + MapRowLoop.rowCap B z j) * u + 1 at h₂
      omega
    · rw [List.replicate_add, List.replicate_add]
      exact (pre.append rows).append last
    · intro a ha
      have keep := (memory a ha.2.1).trans (frame.memory a ha.1)
      by_cases valid : ∀ e, v e = totalWidth (basePayload B) θ e
      · rw [ite_eq_left valid] at done
        rw [done.2, PrivateLabels.accumulate_outside _ _ _ a ha.2.2]
        exact keep
      · rw [ite_eq_right valid] at done
        exact (congrFun done.2 a).trans keep
    · dsimp only [Option.bind_some]
      by_cases valid : ∀ e, v e = totalWidth (basePayload B) θ e
      · rw [ite_eq_left valid] at done ⊢
        refine ⟨done.1, fun l ↦ ?_⟩
        rw [done.2, PrivateLabels.accumulate_at _ _ _ X.histogramFit, hmid]
        simp only [List.map_ofFn, labels, Function.comp_def]
      · rw [ite_eq_right valid] at done ⊢
        exact ⟨done.1, fun l ↦ (congrFun done.2 _).trans (hmid l)⟩
    · intro θ' hit valid
      have eq := Option.some.inj (hit.symm.trans hsel)
      subst θ'
      rw [ite_eq_left valid] at done
      have sels : m.privateMem = PrivateScratch.write (X.source : BurstRAM.Word w)
          (fun i ↦ selector (θ i)) c.privateMem := by
        apply PrivateScratch.eq_write
        · intro i
          rw [← Nat.cast_add]
          exact (hselWords i).trans ((pub.name _).trans (pub.rows (.inl (θ i))))
        · intro a ne
          exact frame.memory a (PrivateScratch.outside_of_ne _ a ne)
      have labs : mid.privateMem = PrivateScratch.write (X.target : BurstRAM.Word w) names
          m.privateMem := by
        apply PrivateScratch.eq_write
        · intro i
          simpa only [Nat.cast_add] using labelWords i
        · intro a ne
          exact memory a (PrivateScratch.outside_of_ne _ a ne)
      rw [done.2, labs, sels]
      rfl

/-- Project the exterior-cell guarantee from the exact native post-state. -/
theorem native_framed (M : Machine w p r k) (linked : P.Linked M) (separate : P.Separate)
    (selector : Selector B ↪ BurstRAM.Word w) (ordinal : (parameterData B).Entry → Fin t)
    (fb : B.selectorBits ≤ w) (fd : ∀ e, baseDemand B z e ≤ w) (fs : ∀ s e, basePayload B s e ≤ w)
    (pub : P.Public M selector (fun s ↦ ((ordinal s).val : BurstRAM.Word w)) fb fd fs)
    (c : Config w p r) (ready : P.Ready X c) :
    P.RunsFramed M c X.hist (MapNativeClock.cap B z j u) (P.Outside X)
      ((MotifEntry.run src dst (baseDemand B z) demand G (basePayload B) (lookup B z)
        (selectorTable B) (selectorCode B) v j d x).1.map (List.map ordinal)) :=
  (P.native_post X M linked separate selector ordinal fb fd fs pub c ready).framed P

/-- Project the exact map result and histogram from its framed native path. -/
theorem native (M : Machine w p r k) (linked : P.Linked M) (separate : P.Separate)
    (selector : Selector B ↪ BurstRAM.Word w) (ordinal : (parameterData B).Entry → Fin t)
    (fb : B.selectorBits ≤ w) (fd : ∀ e, baseDemand B z e ≤ w) (fs : ∀ s e, basePayload B s e ≤ w)
    (pub : P.Public M selector (fun s ↦ ((ordinal s).val : BurstRAM.Word w)) fb fd fs)
    (c : Config w p r) (ready : P.Ready X c) :
    P.Runs M c X.hist (MapNativeClock.cap B z j u)
      ((MotifEntry.run src dst (baseDemand B z) demand G (basePayload B) (lookup B z)
        (selectorTable B) (selectorCode B) v j d x).1.map (List.map ordinal)) :=
  (P.native_framed X M linked separate selector ordinal fb fd fs pub c ready).forget P

end PairSimulation.MapEntry.Program

end VPVNP
end Computability
end OAI
