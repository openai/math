import OAI.Computability.VPVNP.CompressorBlockHeaderPlan
import OAI.Computability.VPVNP.CompressorSourceWalk

/-!
# Chronological publication of selected compressor level headers

The input header of each substep begins in terminal format. The first visit
relabels it in place using the selected pass. The second visit computes the
output state's terminal scalars. The third visits the new header and writes
its incidence and table pointers using the initial level's capacities.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.BlockHeaderRun

open BurstRAM BurstRAM.PrivateRAM Compression PhaseRecipe DescriptorSpace LevelFields
open scoped Fin.CommRing

variable {w a b : ℕ} {k : Type*} [_root_.Field k] {S : BlockSchedule k} {B : S.Templates}
  {R : Type*} [CommRing R] {f : B.Entry → R} {hf : B.IsSolution f}

/-- The machine-word address of the start of level `i`. -/
def header (w : ℕ) (L : Layout) (i : ℕ) : Word w := (levelStart L i : Word w)
/-- Public operand bank for a scalar publisher, with the destination header in operand zero. -/
def scalarPorts (dest : Word w) : Fin 5 → Word w := ![dest,0,0,0,0]
/-- Public operand bank for the pointer publisher, carrying the destination header and the
first level header. -/
def headPorts (dest first : Word w) : Fin 5 → Word w := ![dest,first,0,0,0]

private theorem span (L : Layout) (i : ℕ) :
    levelStart L i + L.shape.scalarFields ≤ levelStart L (i+1) := by
  change levelsBase L + i*levelWords L + L.shape.scalarFields ≤ levelsBase L + (i+1)*levelWords L
  have h : L.shape.scalarFields ≤ levelWords L := by unfold levelWords levelHeaderWords; omega
  rw [Nat.succ_mul]; omega

private theorem fit_fields (L : Layout) (i : Fin L.levels) (fit : endAddress L < 2^w) :
    levelStart L i + L.shape.scalarFields < 2^w := (span L i).trans_lt (level_room L fit i)

private theorem address_val (L : Layout) (i n : ℕ) (h : levelStart L i+n < 2^w) :
    (header w L i+(n : Word w)).val = levelStart L i+n := by
  change (((levelStart L i : ℕ) : Word w)+(n : Word w)).val = _
  rw [← Nat.cast_add, Fin.val_natCast,Nat.mod_eq_of_lt h]

private theorem header_val (L : Layout) (i : Fin L.levels) (fit : endAddress L < 2^w) :
    (header w L i).val = levelStart L i := Nat.mod_eq_of_lt (by have := fit_fields L i fit; omega)

private theorem as_word {z : Word w} {n : ℕ} (h : z.val = n) : z = (n : Word w) := by
  subst n
  exact Fin.ext (Nat.mod_eq_of_lt z.isLt).symm

theorem present_counts {p : Scalars.Pass a b} {V l : ℕ} {base : Word w} {m : Memory w}
    (h : Scalars.Present p V l base m) : DescriptorHeads.CountsAt base m V (2^a) (2^l) := by
  have hw (i : Fin 6) := as_word (h i)
  constructor
  · simpa [headerCell,Scalars.values] using hw 0
  · simpa [headerCell,Scalars.values] using hw 1
  · simpa [headerCell,Scalars.values] using hw 2

private theorem keep_counts {base : Word w} {m out : Memory w} {V D lanes : ℕ}
    (h : DescriptorHeads.CountsAt base m V D lanes)
    (keep : ∀ i : Fin 3, out (base+(i.val : Word w)).val = m (base+(i.val : Word w)).val) :
    DescriptorHeads.CountsAt base out V D lanes := by
  have h₀ : out base.val = m base.val := by simpa using keep 0
  have h₁ : out (base+1).val = m (base+1).val := by simpa using keep 1
  have h₂ : out (base+2).val = m (base+2).val := by simpa using keep 2
  exact ⟨h₀.trans h.vertices,h₁.trans h.degree,h₂.trans h.replicas⟩

/-- The pass origin identifies the lane count remaining in the actual output
state. This converts six natural scalar loads to the consumer's typed header. -/
theorem published_of_present (L : Layout) (i : Fin L.levels) (six : 6 ≤ L.shape.scalarFields)
    (fit : endAddress L < 2^w) (v : SelectedLevel B f hf) (m : Memory w)
    (h : Scalars.Present (Scalars.ofOrigin v.origin) (Fintype.card v.input.Base) v.inputLanes (header w L i) m) :
    Published L i v (Scalars.ofOrigin v.origin).expanderDegree m := by
  let p := Scalars.ofOrigin v.origin
  have room := fit_fields L i fit
  have read (j : Fin 6) :
      m (levelStart L i+j.val) = (Scalars.values p (Fintype.card v.input.Base) v.inputLanes j : Word w) := by
    have eqn := as_word (h j)
    change m (header w L i+(j.val : Word w)).val = _ at eqn
    rwa [address_val L i j.val (by have := j.isLt; omega)] at eqn
  have lane := (Scalars.origin_counts v.origin v.term).1
  have rem : v.inputLanes-p.spent = v.outputLanes := by change v.inputLanes = p.spent+v.outputLanes at lane; omega
  refine ⟨by omega,read 0,read 1,read 2,?_,read 4,read 5⟩
  simpa [Scalars.values,rem] using read 3

/-- Report of the native six-scalar publisher. Its result is the next cursor
relative to the supplied source, even when source and destination coincide. -/
def scalarReport (row : FormulaRow 3) (src dest : Word w) (m : Memory w) :=
  row.recipe.report (scalarPorts dest) src m

/-- The pointer publisher's report for level `i`, evaluated at cursor zero in the supplied
memory. -/
def headReport (L : Layout) (i : ℕ) (m : Memory w) :=
  (DescriptorHeads.publisher L.shape).recipe.report (headPorts (header w L i) (header w L 0)) 0 m

/-- Physical effects of the incidence/table pointer visit. -/
structure HeadsRun (L : Layout) (i : Fin L.levels) (rows : ℕ) (m : Memory w) : Prop where
  execute : let row := DescriptorHeads.publisher L.shape
    let M := (row.recipe.table.instantiate w (headPorts (header w L i) (header w L 0))).program
    BurstRAM.execute M (row.recipe.code.length+1) (M.start 0) m [] = some (headReport L i m)
  result : (headReport L i m).result = some 1
  incidence : ∀ j : Fin 6, after m (headReport L i m).events (incidenceHead L i j) =
    (incidenceBase L i rows j : Word w)
  tables : ∀ j : Fin L.shape.tables, after m (headReport L i m).events (tableHead L i j) =
    (tableBase L i j : Word w)
  outside : ∀ x, x < levelStart L i + L.shape.scalarFields ∨ incidenceStart L i ≤ x →
    after m (headReport L i m).events x = m x
  cost : let row := DescriptorHeads.publisher L.shape
    (headReport L i m).events.length = row.recipe.code.length ∧
      (headReport L i m).probes = row.recipe.reads+(L.shape.tables+3+3) ∧ choiceBits (headReport L i m).events = []

theorem heads_run (L : Layout) (i : Fin L.levels) (m : Memory w) (fit : endAddress L < 2^w)
    {V D lanes V₀ D₀ lanes₀ : ℕ} (h : DescriptorHeads.CountsAt (header w L i) m V D lanes)
    (h₀ : DescriptorHeads.CountsAt (header w L 0) m V₀ D₀ lanes₀) (hP : V₀*lanes₀ = L.positions) :
    HeadsRun L i (V*lanes*D) m := by
  obtain ⟨he,hr,hi,ht,hf,hc⟩ := DescriptorHeads.publish L i (headPorts (header w L i) (header w L 0)) m 0 fit
    rfl rfl h h₀ hP
  exact ⟨he,by simpa only [headReport,zero_add] using hr,hi,ht,hf,hc⟩

private theorem keep_present {p : Scalars.Pass a b} {V l : ℕ} {base : Word w} {m out : Memory w}
    (input : Scalars.Present p V l base m)
    (keep : ∀ j : Fin 6, out (base+(j.val : Word w)).val = m (base+(j.val : Word w)).val) :
    Scalars.Present p V l base out := by
  intro j
  change (out (base+(j.val : Word w)).val).val = _
  rw [keep]
  exact input j

private theorem counts_agree {base : Word w} {m out : Memory w} {V D lanes : ℕ}
    (h : DescriptorHeads.CountsAt base m V D lanes) (h' : DescriptorHeads.CountsAt base out V D lanes)
    (i : Fin 3) : out (base+(i.val : Word w)).val = m (base+(i.val : Word w)).val := by
  fin_cases i
  · simpa using h'.vertices.trans h.vertices.symm
  · exact h'.degree.trans h.degree.symm
  · exact h'.replicas.trans h.replicas.symm

variable (v : SelectedLevel B f hf)

/-- Scalar formula converting the input's terminal header to the selected pass's header format. -/
def inputRow := Scalars.advanceRow (.terminal v.inputExponent) (Scalars.ofOrigin v.origin)
/-- Scalar formula advancing from the selected pass's header format to the successor's terminal
format. -/
def outputRow := Scalars.advanceRow (Scalars.ofOrigin v.origin) (.terminal v.outputExponent)

/-- Memory after relabeling the input level's scalar header in place. -/
def inputMemory (L : Layout) (i : ℕ) (m : Memory w) :=
  after m (scalarReport (inputRow v) (header w L i) (header w L i) m).events

/-- Memory after the input relabel and the publication of the successor's terminal scalars. -/
def outputMemory (L : Layout) (i j : ℕ) (m : Memory w) :=
  let m₁ := inputMemory v L i m
  after m₁ (scalarReport (outputRow v) (header w L i) (header w L j) m₁).events

/-- Memory after both scalar visits and the successor's incidence and table pointer
publication. -/
def finalMemory (L : Layout) (i j : ℕ) (m : Memory w) :=
  let m₂ := outputMemory v L i j m
  after m₂ (headReport L j m₂).events

/-- All three reports execute with the actual post-memory of their predecessor.
The published input fields express the selected pass, and the output's terminal
fields can serve as the input of the next substep. -/
structure Substep (L : Layout) (i j : Fin L.levels) (six : 6 ≤ L.shape.scalarFields)
    (m : Memory w) : Prop where
  relabel : Scalars.Publishes L i six (inputRow v) (Scalars.ofOrigin v.origin)
    (Fintype.card v.input.Base) v.inputLanes (scalarPorts (header w L i)) (header w L i) m
  advance : Scalars.Publishes L j six (outputRow v) (.terminal v.outputExponent)
    (Fintype.card (v.pass.next v.term).Base) v.outputLanes
    (scalarPorts (header w L j)) (header w L i) (inputMemory v L i m)
  heads : HeadsRun L j v.outputSlots (outputMemory v L i j m)
  input : Published L i v (Scalars.ofOrigin v.origin).expanderDegree (finalMemory v L i j m)
  output : Scalars.Present (.terminal v.outputExponent) (Fintype.card (v.pass.next v.term).Base) v.outputLanes
    (header w L j) (finalMemory v L i j m)
  firstCounts : ∀ t : Fin 3, finalMemory v L i j m (header w L 0+(t.val : Word w)).val =
    m (header w L 0+(t.val : Word w)).val
  outside : ∀ x, (x < levelStart L i ∨ levelStart L i+6 ≤ x) →
    (x < levelStart L j ∨ levelStart L j+6 ≤ x) →
    (x < levelStart L j+L.shape.scalarFields ∨ incidenceStart L j ≤ x) →
    finalMemory v L i j m x = m x

theorem substep_run (L : Layout) (i j : Fin L.levels) (next : i.val+1 = j.val)
    (six : 6 ≤ L.shape.scalarFields) (fit : endAddress L < 2^w) (m : Memory w)
    (input : Scalars.Present (.terminal v.inputExponent) (Fintype.card v.input.Base) v.inputLanes (header w L i) m)
    {V₀ D₀ lanes₀ : ℕ} (h₀ : DescriptorHeads.CountsAt (header w L 0) m V₀ D₀ lanes₀)
    (hP : V₀*lanes₀ = L.positions) (sites : v.input.positions < 2^w) (slots : slotDegree S < 2^w) :
    Substep v L i j six m := by
  let p := Scalars.ofOrigin v.origin
  let m₁ := inputMemory v L i m
  let m₂ := outputMemory v L i j m
  let m₃ := finalMemory v L i j m
  have spent := (Scalars.origin_counts v.origin v.term).1
  change v.inputLanes = p.spent+v.outputLanes at spent
  have fs := Scalars.fits_selected v sites slots
  have h1 : Scalars.Publishes L i six (inputRow v) p (Fintype.card v.input.Base) v.inputLanes
      (scalarPorts (header w L i)) (header w L i) m := by
    simpa only [inputRow,p,Scalars.Pass.baseFactor, Nat.mul_one, Scalars.Pass.spent, Nat.sub_zero] using
      Scalars.advance L i six fit (.terminal v.inputExponent) p (scalarPorts (header w L i)) (header w L i) m
        (header_val L i fit) input (by change p.spent ≤ v.inputLanes-0; omega)
        (by simpa only [Scalars.Pass.baseFactor,Nat.mul_one,Scalars.Pass.spent,Nat.sub_zero] using fs)
  have live : Scalars.Present p (Fintype.card v.input.Base) v.inputLanes (header w L i) m₁ :=
    h1.2.2.2.1
  have targetFit : Scalars.Fits (.terminal v.outputExponent) (Fintype.card (v.pass.next v.term).Base)
      v.outputLanes w := Scalars.fits_state _ _ (v.outputSites_le.trans_lt sites)
        (v.outputDegree_le.trans_lt slots) (v.outputDegree_le.trans_lt slots) (Nat.two_pow_pos _)
  have h2 := Scalars.advance_selected v.origin v.term (.terminal v.outputExponent) L j six fit
    (scalarPorts (header w L j)) (header w L i) m₁ (header_val L j fit) live (Nat.zero_le _) targetFit
  have successor : Scalars.Present (.terminal v.outputExponent) (Fintype.card (v.pass.next v.term).Base)
      v.outputLanes (header w L j) m₂ := h2.2.2.2.1
  have before := span L i
  rw [next] at before
  have zeroLe := levelStart_mono L (Nat.zero_le i.val)
  let z : Fin L.levels := ⟨0, by have := i.isLt; omega⟩
  have zeroRoom : levelStart L 0+L.shape.scalarFields < 2^w := fit_fields L z fit
  have oldRoom := fit_fields L i fit
  have newRoom := fit_fields L j fit
  have c₁ : DescriptorHeads.CountsAt (header w L 0) m₁ V₀ D₀ lanes₀ := by
    apply keep_counts h₀
    intro t
    by_cases eqn : i.val = 0
    · have hsame := counts_agree (present_counts input) (present_counts live) t
      simpa only [eqn] using hsame
    · have le := levelStart_mono L (show 1 ≤ i.val by omega)
      have sep : levelStart L 0+L.shape.scalarFields ≤ levelStart L 1 := span L 0
      rw [address_val L 0 t.val (by have := t.isLt; omega)]
      exact h1.2.2.2.2.1 _ (.inl (by have := t.isLt; omega))
  have c₂ : DescriptorHeads.CountsAt (header w L 0) m₂ V₀ D₀ lanes₀ := by
    apply keep_counts c₁
    intro t
    rw [address_val L 0 t.val (by have := t.isLt; omega)]
    exact h2.2.2.2.2.1 _ (.inl (by have := t.isLt; omega))
  have head := heads_run L j m₂ fit (present_counts successor) c₂ hP
  have outSlots : Fintype.card (v.pass.next v.term).Base * 2^v.outputLanes * 2^v.outputExponent = v.outputSlots := by
    rw [SelectedLevel.outputSlots,SelectedLevel.outputSites,State.positions,Fintype.card_prod,
      Fintype.card_congr (bitWordFinEquiv _),Fintype.card_fin]
  refine ⟨h1,h2,outSlots ▸ head,?_,?_,?_,?_⟩
  · apply published_of_present L i six fit v m₃
    apply keep_present live
    intro t
    rw [address_val L i t.val (by have := t.isLt; omega)]
    exact (head.outside _ (.inl (by have := t.isLt; omega))).trans
      (h2.2.2.2.2.1 _ (.inl (by have := t.isLt; omega)))
  · apply keep_present successor
    intro t
    rw [address_val L j t.val (by have := t.isLt; omega)]
    exact head.outside _ (.inl (by have := t.isLt; omega))
  · intro t
    rw [← counts_agree h₀ c₂ t]
    exact head.outside _ (.inl (by
      rw [address_val L 0 t.val (by have := t.isLt; omega)]
      have := t.isLt; omega))
  · intro x hx hy hz
    exact (head.outside _ hz).trans ((h2.2.2.2.2.1 _ hy).trans (h1.2.2.2.2.1 _ hx))

/-- All completed earlier levels and the schedule directory keep their exact
word values throughout this three-visit substep. -/
theorem Substep.before {L : Layout} {i j : Fin L.levels} {six : 6 ≤ L.shape.scalarFields}
    {m : Memory w} (run : Substep v L i j six m) (next : i.val+1 = j.val) (x : ℕ)
    (hx : x < levelStart L i) : finalMemory v L i j m x = m x := by
  have le := levelStart_mono L (show i.val ≤ j.val by omega)
  exact run.outside x (.inl hx) (.inl (by omega)) (.inl (by omega))

/-- Immutable scalar cells beyond the six mutable fields survive all three
visits. These include the saved parameter bank and the arena-base word. -/
theorem Substep.firstScalarTail {L : Layout} {i j : Fin L.levels} {six : 6 ≤ L.shape.scalarFields}
    {m : Memory w} (run : Substep v L i j six m) (next : i.val+1 = j.val) (x : ℕ)
    (lo : 6 ≤ x) (hi : x < L.shape.scalarFields) :
    finalMemory v L i j m (levelStart L 0+x) = m (levelStart L 0+x) := by
  have sep : levelStart L 0+L.shape.scalarFields ≤ levelStart L 1 := span L 0
  have nj := levelStart_mono L (show 1 ≤ j.val by omega)
  apply run.outside
  · by_cases eqn : i.val = 0
    · exact .inr (by rw [eqn]; omega)
    · have oi := levelStart_mono L (show 1 ≤ i.val by omega)
      exact .inl (by omega)
  · exact .inl (by omega)
  · exact .inl (by omega)

theorem Substep.olderPublished {L : Layout} {i j : Fin L.levels} {six : 6 ≤ L.shape.scalarFields}
    {m : Memory w} (run : Substep v L i j six m) (next : i.val+1 = j.val) {n dH : ℕ}
    {previous : SelectedLevel B f hf} (old : n < i.val) (prev : Published L n previous dH m) :
    Published L n previous dH (finalMemory v L i j m) := by
  have le := levelStart_mono L (show n+1 ≤ i.val by omega)
  have span' := span L n
  have keep (x : ℕ) (hx : x < 6) := run.before v next (levelStart L n+x) (by omega)
  exact ⟨prev.room,(keep 0 (by decide)).trans prev.vertices,(keep 1 (by decide)).trans prev.degree,
    (keep 2 (by decide)).trans prev.lanes,(keep 3 (by decide)).trans prev.residual,
    (keep 4 (by decide)).trans prev.nextDegree,(keep 5 (by decide)).trans prev.expander⟩

/-- The original eight cursor parameters stay available at the first header
even when the current substep relabels level zero itself. -/
theorem Substep.cursorFrame {L : Layout} {i j : Fin L.levels} {six : 6 ≤ L.shape.scalarFields}
    {m : Memory w} (run : Substep v L i j six m) (next : i.val+1 = j.val)
    (fourteen : 14 ≤ L.shape.scalarFields) (fit : endAddress L < 2^w) :
    (Frame.data (header w L 0+6) (finalMemory v L i j m) : Fin 8 → Word w) =
      Frame.data (header w L 0+6) m := by
  funext t
  let z : Fin L.levels := ⟨0,by have := i.isLt; omega⟩
  have hroom : levelStart L 0+L.shape.scalarFields < 2^w := fit_fields L z fit
  have addr : (header w L 0+6+(t.val : Word w)).val = levelStart L 0+(6+t.val) := by
    rw [show header w L 0+6+(t.val : Word w) = header w L 0+((6+t.val : ℕ) : Word w) by
      simp [add_assoc]]
    exact address_val L 0 _ (by have := t.isLt; omega)
  change finalMemory v L i j m (header w L 0+6+(t.val : Word w)).val = _
  change _ = m (header w L 0+6+(t.val : Word w)).val
  rw [addr]
  exact run.firstScalarTail v next (6+t.val) (by omega) (by have := t.isLt; omega)

/-- The three chronological reports for a selected substep, each computed from the preceding
visit's output memory. -/
def reports (L : Layout) (i j : ℕ) (m : Memory w) : List (Report w) :=
  [scalarReport (inputRow v) (header w L i) (header w L i) m,
   scalarReport (outputRow v) (header w L i) (header w L j) (inputMemory v L i m),
   headReport L j (outputMemory v L i j m)]

theorem reports_after (L : Layout) (i j : ℕ) (m : Memory w) :
    after m (eventLog (reports v L i j m)) = finalMemory v L i j m := by
  simp [reports,eventLog,after,List.foldl_append,finalMemory,outputMemory,inputMemory]

/-- Memory after the level-zero scalar publisher reads the cursor frame and initializes the
first header. -/
def initialMemory (a : ℕ) (L : Layout) (m : Memory w) :=
  let start := header w L 0
  after m (scalarReport (Scalars.initialRow (.terminal a)) (start+6) start m).events

/-- Memory after the initial scalars and level-zero incidence and table pointers have been
published. -/
def initialFinal (a : ℕ) (L : Layout) (m : Memory w) :=
  let mid := initialMemory a L m
  after mid (headReport L 0 mid).events

/-- The first two raw workers in the initial calendar sequence. They install
level zero's terminal scalars and heads and retain its eight cursor parameters. -/
structure Initial (a low l : ℕ) (L : Layout) (nonempty : 0 < L.levels)
    (six : 6 ≤ L.shape.scalarFields) (m : Memory w) : Prop where
  scalarRun : Scalars.Publishes L ⟨0,nonempty⟩ six (Scalars.initialRow (.terminal a)) (.terminal a)
    ((low+l)*2^low) l (scalarPorts (header w L 0)) (header w L 0+6) m
  heads : HeadsRun L ⟨0,nonempty⟩ (((low+l)*2^low)*2^l*2^a) (initialMemory a L m)
  terminal : Scalars.Present (.terminal a) ((low+l)*2^low) l (header w L 0) (initialFinal a L m)
  cursorFrame : (Frame.data (header w L 0+6) (initialFinal a L m) : Fin 8 → Word w) =
    Frame.data (header w L 0+6) m
  outside : ∀ x, (x < levelStart L 0 ∨ levelStart L 0+6 ≤ x) →
    (x < levelStart L 0+L.shape.scalarFields ∨ incidenceStart L 0 ≤ x) → initialFinal a L m x = m x

theorem initial_run (L : Layout) (nonempty : 0 < L.levels) (fourteen : 14 ≤ L.shape.scalarFields)
    (fit : endAddress L < 2^w) (m : Memory w) (a low l : ℕ) {row tag : Word w} {width start : ℕ}
    (frame : Frame.data (header w L 0+6) m = CursorRAM.ScheduleInit.inputs row tag low l a width start)
    (positions : ((low+l)*2^low)*2^l = L.positions)
    (scalars : Scalars.Fits (.terminal a) ((low+l)*2^low) l w) :
    Initial a low l L nonempty (by omega) m := by
  let z : Fin L.levels := ⟨0,nonempty⟩
  let src := header w L 0
  let mid := initialMemory a L m
  have six : 6 ≤ L.shape.scalarFields := by omega
  have hs := Scalars.initialize_level L nonempty six fit (.terminal a) (scalarPorts src) (src+6) m
    (header_val L z fit) frame (Nat.zero_le l) scalars
  have live : Scalars.Present (.terminal a) ((low+l)*2^low) l src mid := hs.2.2.2.1
  have cnt := present_counts live
  have head := heads_run L z mid fit cnt cnt positions
  have room : levelStart L 0+L.shape.scalarFields < 2^w := fit_fields L z fit
  refine ⟨hs,head,?_,?_,?_⟩
  · apply keep_present live
    intro j
    rw [show (src+(j.val : Word w)).val = levelStart L 0+j.val from address_val L 0 _ (by have := j.isLt; omega)]
    exact head.outside (levelStart L 0+j.val) (.inl (by change _ < levelStart L 0+L.shape.scalarFields; have := j.isLt; omega))
  · funext t
    have haddr : (src+6+(t.val : Word w)).val = levelStart L 0+(6+t.val) := by
      rw [show src+6+(t.val : Word w) = header w L 0+((6+t.val : ℕ) : Word w) by simp [src,add_assoc]]
      exact address_val L 0 _ (by have := t.isLt; omega)
    change initialFinal a L m (src+6+(t.val : Word w)).val = m (src+6+(t.val : Word w)).val
    rw [haddr]
    exact (head.outside (levelStart L 0+(6+t.val)) (.inl (by
      change _ < levelStart L 0+L.shape.scalarFields; have := t.isLt; omega))).trans
      (hs.2.2.2.2.1 (levelStart L 0+(6+t.val)) (.inr (by change levelStart L 0+6 ≤ _; omega)))
  · intro x hx hy
    exact (head.outside _ hy).trans (hs.2.2.2.2.1 _ hx)

theorem Initial.scalarTail {a low l : ℕ} {L : Layout} {nonempty : 0 < L.levels} {six : 6 ≤ L.shape.scalarFields}
    {m : Memory w} (run : Initial a low l L nonempty six m) (x : ℕ) (lo : 6 ≤ x)
    (hi : x < L.shape.scalarFields) : initialFinal a L m (levelStart L 0+x) = m (levelStart L 0+x) :=
  run.outside _ (.inr (by omega)) (.inl (by omega))

/-- Evaluate the actual visit's operand bank and starting cursor, then enter
its native worker. All operand expressions use this visit's entry memory. -/
def rawCall (visit : BlockPlanner.Visit) (pub : Fin 5 → Word w) (state : Word w)
    (m : Memory w) (fuel : ℕ) :=
  let data := fun j ↦ (visit.params j).eval pub state m
  let M := (visit.worker.table.instantiate w data).program
  execute M fuel (M.start (visit.initial.eval pub state m)) m []

private theorem raw_formula (row : FormulaRow 3) (src dest : Expr) (pub : Fin 5 → Word w)
    (state : Word w) (m : Memory w) (fuel : ℕ) :
    let M := (row.recipe.table.instantiate w (scalarPorts (dest.eval pub state m))).program
    rawCall (BlockHeaderPlan.formula row src dest) pub state m fuel =
      execute M fuel (M.start (src.eval pub state m)) m [] := by
  have bank : (fun j : Fin 5 ↦ ((BlockHeaderPlan.formula row src dest).params j).eval pub state m) =
      scalarPorts (dest.eval pub state m) := by
    funext j; fin_cases j <;> rfl
  exact congrArg (fun data : Fin 5 → Word w ↦
    let M := (row.recipe.table.instantiate w data).program
    execute M fuel (M.start (src.eval pub state m)) m []) bank

private theorem raw_heads (F : Shape) (dst : Expr) (pub : Fin 5 → Word w)
    (state : Word w) (m : Memory w) (fuel : ℕ) :
    let bank := headPorts (dst.eval pub state m) (BlockHeaderPlan.firstHeader.eval pub state m)
    let M := ((DescriptorHeads.publisher F).recipe.table.instantiate w bank).program
    rawCall (BlockHeaderPlan.heads F dst) pub state m fuel = execute M fuel (M.start 0) m [] := by
  have bank : (fun j : Fin 5 ↦ ((BlockHeaderPlan.heads F dst).params j).eval pub state m) =
      headPorts (dst.eval pub state m) (BlockHeaderPlan.firstHeader.eval pub state m) := by
    funext j; fin_cases j <;> rfl
  exact congrArg (fun data : Fin 5 → Word w ↦
    let M := ((DescriptorHeads.publisher F).recipe.table.instantiate w data).program
    execute M fuel (M.start 0) m []) bank

private theorem firstHeader_keep (pub : Fin 5 → Word w) (state : Word w) (m out : Memory w)
    (h : out (pub 3).val = m (pub 3).val) :
    BlockHeaderPlan.firstHeader.eval pub state out = BlockHeaderPlan.firstHeader.eval pub state m := by
  simp only [BlockHeaderPlan.firstHeader,Expr.add,Expr.sub,Expr.mul,Expr.eval,h]

/-- The three native executions use exactly the public operands and cursors of
the compiled block plan. The two directory control cells lie before the level
headers and survive the preceding raw visits. -/
theorem Substep.visits {L : Layout} {i j : Fin L.levels} {six : 6 ≤ L.shape.scalarFields} {m : Memory w}
    (run : Substep v L i j six m) (first step : ℕ) (old : first+step = i.val) (new : first+(step+1) = j.val)
    (pub : Fin 5 → Word w) (state : Word w) (entry : Entry L first pub state m)
    (hFirst : BlockHeaderPlan.firstHeader.eval pub state m = header w L 0)
    (pitch : (pub 1-1).val < levelStart L i) (count : (pub 3).val < levelStart L i) :
    let ls := BlockHeaderPlan.substep L.shape step (Scalars.ofOrigin v.origin)
    let src := header w L i
    let dst := header w L j
    let m₁ := inputMemory v L i m
    let m₂ := outputMemory v L i j m
    rawCall (ls[0]'(by simp [ls])) pub state m ((inputRow v).recipe.code.length+1) =
        some (scalarReport (inputRow v) src src m) ∧
      rawCall (ls[1]'(by simp [ls])) pub state m₁ ((outputRow v).recipe.code.length+1) =
        some (scalarReport (outputRow v) src dst m₁) ∧
      rawCall (ls[2]'(by simp [ls])) pub state m₂ ((DescriptorHeads.publisher L.shape).recipe.code.length+1) =
        some (headReport L j m₂) := by
  let m₁ := inputMemory v L i m
  let m₂ := outputMemory v L i j m
  have before := levelStart_mono L (show i.val ≤ j.val by omega)
  have eq₁ (x : ℕ) (hx : x < levelStart L i) : m₁ x = m x := run.relabel.2.2.2.2.1 x (.inl hx)
  have eq₂ (x : ℕ) (hx : x < levelStart L i) : m₂ x = m x :=
    (run.advance.2.2.2.2.1 x (.inl (by omega))).trans (eq₁ _ hx)
  have e₁ : Entry L first pub state m₁ := ⟨entry.pointer,(eq₁ _ pitch).trans entry.pitch⟩
  have e₂ : Entry L first pub state m₂ := ⟨entry.pointer,(eq₂ _ pitch).trans entry.pitch⟩
  have oldAt {mem : Memory w} (e : Entry L first pub state mem) :
      (atLevel step).eval pub state mem = header w L i := old ▸ eval_atLevel e step
  have newAt {mem : Memory w} (e : Entry L first pub state mem) :
      (atLevel (step+1)).eval pub state mem = header w L j := new ▸ eval_atLevel e (step+1)
  refine ⟨?_,?_,?_⟩
  · change rawCall (BlockHeaderPlan.formula (inputRow v) (atLevel step) (atLevel step)) _ _ _ _ = _
    rw [raw_formula,oldAt entry]; exact run.relabel.1
  · change rawCall (BlockHeaderPlan.formula (outputRow v) (atLevel step) (atLevel (step+1))) pub state m₁ _ = _
    rw [raw_formula,newAt e₁,oldAt e₁]; exact run.advance.1
  · change rawCall (BlockHeaderPlan.heads L.shape (atLevel (step+1))) pub state m₂ _ = _
    rw [raw_heads,newAt e₂,firstHeader_keep pub state m m₂ (eq₂ _ count),hFirst]
    exact run.heads.execute

theorem Initial.visits {a low l : ℕ} {L : Layout} {nonempty : 0 < L.levels} {six : 6 ≤ L.shape.scalarFields}
    {m : Memory w} (run : Initial a low l L nonempty six m) (pub : Fin 5 → Word w) (state : Word w)
    (hFirst : BlockHeaderPlan.firstHeader.eval pub state m = header w L 0)
    (count : (pub 3).val < levelStart L 0) :
    let ls := BlockHeaderPlan.initial L.shape a
    let src := header w L 0
    let row := Scalars.initialRow (.terminal a)
    rawCall (ls[0]'(by simp [ls,BlockHeaderPlan.initial])) pub state m (row.recipe.code.length+1) =
        some (scalarReport row (src+6) src m) ∧
      rawCall (ls[1]'(by simp [ls,BlockHeaderPlan.initial])) pub state (initialMemory a L m)
        ((DescriptorHeads.publisher L.shape).recipe.code.length+1) = some (headReport L 0 (initialMemory a L m)) := by
  let mid := initialMemory a L m
  have hMid := firstHeader_keep pub state m mid (run.scalarRun.2.2.2.2.1 _ (.inl count))
  constructor
  · change rawCall (BlockHeaderPlan.formula _ BlockHeaderPlan.persistentFrame BlockHeaderPlan.firstHeader) _ _ _ _ = _
    have hs : BlockHeaderPlan.persistentFrame.eval pub state m = header w L 0+6 := by
      change BlockHeaderPlan.firstHeader.eval pub state m + ((6 : ℕ) : Word w) = _
      rw [hFirst]; rfl
    rw [raw_formula,hFirst,hs]
    exact run.scalarRun.1
  · change rawCall (BlockHeaderPlan.heads L.shape BlockHeaderPlan.firstHeader) pub state mid _ = _
    rw [raw_heads,hMid,hFirst]; exact run.heads.execute

/-- After the two initialization reports, the third visit reads the eight
immutable parameter words from the first header. Its bound and its eleven
public operands are exactly those of the native cursor-incidence scan. -/
theorem Initial.cursor {a low l : ℕ} {L : Layout} {nonempty : 0 < L.levels} {six : 6 ≤ L.shape.scalarFields}
    {m : Memory w} (run : Initial a low l L nonempty six m) (pub : Fin 5 → Word w) (state : Word w)
    (hFirst : BlockHeaderPlan.firstHeader.eval pub state m = header w L 0)
    (count : (pub 3).val < levelStart L 0) {row tag : Word w} {width start : ℕ}
    (frame : Frame.data (header w L 0+6) m = CursorRAM.ScheduleInit.inputs row tag low l a width start) :
    let visit := (BlockHeaderPlan.initial L.shape a)[2]'(by simp [BlockHeaderPlan.initial])
    let out := initialFinal a L m
    visit.stop.eval pub state out = ((CursorRAM.rowCount low l a : ℕ) : Word w) ∧
      (fun j ↦ (visit.params j).eval pub state out) = CursorRAM.publicWords w low l a width start := by
  let out := initialFinal a L m
  have hkeep := run.outside _ (.inl count) (.inl (by omega))
  have h := (firstHeader_keep pub state m out hkeep).trans hFirst
  have hf : BlockHeaderPlan.persistentFrame.eval pub state out = header w L 0+6 := by
    change BlockHeaderPlan.firstHeader.eval pub state out+((6 : ℕ) : Word w) = _
    rw [h]; rfl
  apply BlockPlanner.cursor_parameters _ pub state out _ hf
  intro j
  let i : Fin 8 := ⟨j.val+2,by have := j.isLt; omega⟩
  have hi := congrFun (run.cursorFrame.trans frame) i
  change out (header w L 0+6+((j.val+2 : ℕ) : Word w)).val =
    CursorRAM.ScheduleInit.inputs row tag low l a width start i at hi
  rw [hi]
  fin_cases j <;> simp [CursorRAM.ScheduleInit.inputs,CursorRAM.encode,i]

/-- A one-call deterministic source scan in the compiled visit's own operand
bank. The report and the memory for its successor are retained by SourceWalk. -/
def OneCall (pub : Fin 5 → Word w) (state : Word w) (visit : BlockPlanner.Visit)
    (m : Memory w) (rs : List (Report w)) : Prop :=
  let data := fun j ↦ (visit.params j).eval pub state m
  let M := (visit.worker.table.instantiate w data).program
  ∃ fuel, runSegment M fuel (some (visit.initial.eval pub state m)) m [[]] = some rs

private theorem walk_cons (pub : Fin 5 → Word w) (state : Word w) {visit : BlockPlanner.Visit}
    {rest : List BlockPlanner.Visit} {m : Memory w} {rep : Report w} {rs : List (Report w)} {fuel : ℕ}
    (h : rawCall visit pub state m fuel = some rep)
    (tail : SourceWalk (OneCall pub state) rest (after m rep.events) rs) :
    SourceWalk (OneCall pub state) (visit::rest) m (rep::rs) := by
  apply SourceWalk.next (rs := [rep])
  · refine ⟨fuel,?_⟩
    rw [runSegment]
    change (match rawCall visit pub state m fuel with
      | none => none
      | some r => (some ([] : List (Report w))).map (r :: ·)) = _
    rw [h]
    rfl
  · simpa [eventLog] using tail

theorem Substep.walk {L : Layout} {i j : Fin L.levels} {six : 6 ≤ L.shape.scalarFields} {m : Memory w}
    (run : Substep v L i j six m) (first step : ℕ) (old : first+step = i.val) (new : first+(step+1) = j.val)
    (pub : Fin 5 → Word w) (state : Word w) (entry : Entry L first pub state m)
    (hFirst : BlockHeaderPlan.firstHeader.eval pub state m = header w L 0)
    (pitch : (pub 1-1).val < levelStart L i) (count : (pub 3).val < levelStart L i) :
    SourceWalk (OneCall pub state) (BlockHeaderPlan.substep L.shape step (Scalars.ofOrigin v.origin)) m
      (reports v L i j m) := by
  obtain ⟨h₁,h₂,h₃⟩ := run.visits v first step old new pub state entry hFirst pitch count
  exact walk_cons pub state h₁ (walk_cons pub state h₂ (walk_cons pub state h₃ (SourceWalk.done _)))

theorem Initial.walk {a low l : ℕ} {L : Layout} {nonempty : 0 < L.levels} {six : 6 ≤ L.shape.scalarFields}
    {m : Memory w} (run : Initial a low l L nonempty six m) (pub : Fin 5 → Word w) (state : Word w)
    (hFirst : BlockHeaderPlan.firstHeader.eval pub state m = header w L 0)
    (count : (pub 3).val < levelStart L 0) :
    SourceWalk (OneCall pub state)
      [BlockHeaderPlan.initialScalars a,BlockHeaderPlan.heads L.shape BlockHeaderPlan.firstHeader] m
      [scalarReport (Scalars.initialRow (.terminal a)) (header w L 0+6) (header w L 0) m,
       headReport L 0 (initialMemory a L m)] := by
  obtain ⟨h₁,h₂⟩ := run.visits pub state hFirst count
  exact walk_cons pub state h₁ (walk_cons pub state h₂ (SourceWalk.done _))

end CompressorRecords.BlockHeaderRun

end VPVNP
end Computability
end OAI
