import OAI.Computability.VPVNP.PairTraversalArena
import OAI.Computability.VPVNP.PairTraversalControllerFormula

/-!
# Memory and call accounting for the two traversal-directory passes

The controller processes all role layers, then all descriptor layers. Its
administrative reads and its writes to terminal header cells at or above
`H` preserve the worker writes below `H`. This region contains the raw
placement directories, the descriptor rows, the final bits, and the tags.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TraversalRoles.ControllerMemory

open BurstRAM TraversalRows LocalHistory Compression CompressorRecords
open scoped Fin.CommRing

variable {w : ℕ}

/-- Equality on the protected prefix of external memory. -/
abbrev AgreeBelow (H : ℕ) (m n : Memory w) := ∀ x < H, m x = n x

theorem write_above {H : ℕ} (m : Memory w) (a v : Word w) (ha : H ≤ a.val) :
    AgreeBelow H (writeMemory m a v) m := fun _ hx => ite_eq_right (hx.trans_le ha).ne

/-- A terminal header word, including the outer dispatcher's ordinal cell
at displacement 31, preserves the entire lower memory interval. -/
theorem write_header (H d : ℕ) (m : Memory w) (v : Word w) (fit : H + d < 2 ^ w) :
    AgreeBelow H (writeMemory m ((H + d : ℕ) : Word w) v) m :=
  write_above m _ _ ((Nat.le_add_right H d).trans_eq (Nat.mod_eq_of_lt fit).symm)

private def isProtectedWrite (H : ℕ) : Event w → Bool
  | .write a _ => decide (a.val < H)
  | _ => false

/-- The ordered external writes visible below the control header. -/
def writesBelow (H : ℕ) (es : List (Event w)) : List (Event w) := es.filter (isProtectedWrite H)

@[simp] theorem writesBelow_append (H : ℕ) (es fs : List (Event w)) :
    writesBelow H (es ++ fs) = writesBelow H es ++ writesBelow H fs := List.filter_append _ _

theorem writesBelow_header (H d : ℕ) (v : Word w) (fit : H + d < 2 ^ w) :
    writesBelow H [.write ((H+d : ℕ) : Word w) v] = [] := by
  have ha : ¬ ((H + d : ℕ) : Word w).val < H := by
    rw [Fin.val_natCast, Nat.mod_eq_of_lt fit]
    omega
  simp only [writesBelow, List.filter_cons, isProtectedWrite, decide_eq_false ha,
    Bool.false_eq_true, ↓reduceIte, List.filter_nil]

@[simp] theorem writesBelow_header_add (H d : ℕ) (v : Word w) (fit : H + d < 2 ^ w) :
    writesBelow H [.write ((H : Word w) + (d : Word w)) v] = [] := by
  simpa only [Nat.cast_add] using writesBelow_header H d v fit

@[simp] theorem writesBelow_tick (H : ℕ) (es : List (Event w)) :
    writesBelow H (.tick :: es) = writesBelow H es := rfl

@[simp] theorem writesBelow_read (H : ℕ) (a v : Word w) (es : List (Event w)) :
    writesBelow H (.read a v :: es) = writesBelow H es := rfl

@[simp] theorem writesBelow_choice (H : ℕ) (b : Bool) (es : List (Event w)) :
    writesBelow H (.choice b :: es) = writesBelow H es := rfl

@[simp] theorem writesBelow_high (H : ℕ) (a v : Word w) (es : List (Event w)) (hi : H ≤ a.val) :
    writesBelow H (.write a v :: es) = writesBelow H es := by
  simp only [writesBelow, List.filter_cons, isProtectedWrite, decide_eq_false hi.not_gt,
    Bool.false_eq_true, ↓reduceIte]

private theorem update_at {m n : Memory w} {x : ℕ} (hx : m x = n x) (e : Event w) :
    update m e x = update n e x := by
  cases e <;> simp only [update, writeMemory, hx]

theorem after_at {m n : Memory w} {x : ℕ} (hx : m x = n x) (es : List (Event w)) :
    after m es x = after n es x := by
  induction es generalizing m n with
  | nil => exact hx
  | cons e es ih => exact ih (update_at hx e)

private theorem replay_filtered (H : ℕ) (m : Memory w) (es : List (Event w)) :
    AgreeBelow H (after m es) (after m (writesBelow H es)) := by
  induction es generalizing m with
  | nil => exact fun _ _ => rfl
  | cons e es ih =>
    intro x hx
    apply (ih (update m e) x hx).trans
    cases e with
    | write a v =>
      by_cases ha : a.val < H
      · simp [writesBelow, isProtectedWrite, ha, after, update]
      · simp only [writesBelow, List.filter_cons, isProtectedWrite, decide_eq_false ha,
          Bool.false_eq_true, ↓reduceIte]
        exact after_at (write_above m a v (Nat.le_of_not_gt ha) x hx) _
    | tick | choice | read => rfl

/-- Two executions with the same visible writes agree below the controller's
header even when they insert different read, control, or high-address events. -/
theorem replay_below {H : ℕ} {m n : Memory w} (h : AgreeBelow H m n)
    {es fs : List (Event w)} (hw : writesBelow H es = writesBelow H fs) :
    AgreeBelow H (after m es) (after n fs) := by
  intro x hx
  refine (replay_filtered H m es x hx).trans ?_
  rw [hw]
  exact (after_at (h x hx) _).trans (replay_filtered H n fs x hx).symm

/-- The model of a single role write only consults the previous value of
the same cell. This holds for padding and for arbitrary prior memory. -/
theorem tag_at {m n : Memory w} {x : ℕ} (hx : m x = n x) (offset cap base count : ℕ)
    (tag : Word w) : Native.image offset cap base count tag m x =
      Native.image offset cap base count tag n x := by
  simp only [Native.image, hx]

/-- Descriptor writes have the same pointwise property. Child addresses
come from the selected placement, and padding comes from this cell of memory. -/
theorem row_at {m n : Memory w} {x : ℕ} (hx : m x = n x) (cap previous base : ℕ) (L : Layer) :
    writeLayer cap previous base L m x = writeLayer cap previous base L n x := by
  simp only [writeLayer, hx]

theorem tags_at {m n : Memory w} {x : ℕ} (hx : m x = n x) (offset cap base : ℕ)
    (ls : List TaggedLayer) :
    writeTags offset cap base ls m x = writeTags offset cap base ls n x := by
  induction ls generalizing m n base with
  | nil => exact hx
  | cons L ls ih => exact ih (tag_at hx _ _ _ _ _) _

theorem rows_at {m n : Memory w} {x : ℕ} (hx : m x = n x) (cap previous base : ℕ)
    (ls : List Layer) : build cap previous base ls m x = build cap previous base ls n x := by
  induction ls generalizing m n previous base with
  | nil => exact hx
  | cons L ls ih => exact ih (row_at hx _ _ _ _) _ _

/-- A high header write commutes, as a full memory equality, with the two
passes below it. The row and tag regions may have unused cells. -/
theorem header_commute (offset cap base : ℕ) (ls : List TaggedLayer) (m : Memory w)
    (a v : Word w) (ha : offset + base + tagWords cap ls ≤ a.val) :
    build cap base base (ls.map TaggedLayer.layer)
      (writeTags offset cap base ls (writeMemory m a v)) =
    writeMemory (build cap base base (ls.map TaggedLayer.layer) (writeTags offset cap base ls m))
      a v := by
  funext x
  by_cases he : x = a.val
  · subst x
    rw [build_outside _ _ _ _ _ _ (Or.inr (show base + tagWords cap ls ≤ a.val by omega)),
      write_tags_outside _ _ _ _ _ _ (Or.inr ha)]
    simp [writeMemory]
  · rw [writeMemory, ite_eq_right he]
    apply rows_at
    apply tags_at
    exact ite_eq_right he

open private row_end_le from OAI.Computability.VPVNP.PairTraversalRows

theorem allRows_below {m n : Memory w} {H cap previous base : ℕ} (ls : List Layer)
    (ag : AgreeBelow H m n) (room : base + words cap ls ≤ H)
    (hc : ∀ L ∈ ls, ∀ i, (L.ids i).length ≤ cap)
    (rows : AllRows w n cap previous base ls) : AllRows w m cap previous base ls := by
  induction ls generalizing previous base with
  | nil => trivial
  | cons L ls ih =>
    have he : endPos cap base L + words cap ls ≤ H := by
      simpa [words, endPos, address, Nat.mul_add, Nat.add_assoc] using room
    refine ⟨fun i => ?_, ih he (fun l hl => hc l (List.mem_cons_of_mem _ hl)) rows.2⟩
    let node := address cap base i.val
    have hend : node + (cap+2) ≤ endPos cap base L := row_end_le _ _ _ _
    have hlen : (childWords w cap previous L i).length ≤ cap := by
      simpa only [childWords, List.length_map] using hc L List.mem_cons_self i
    obtain ⟨hn, hn1, hs, h0, h1, hj⟩ := rows.1 i
    refine ⟨hn, hn1, hs, (ag node (by omega)).trans h0, (ag (node+1) (by omega)).trans h1,
      fun j => (ag (node+2+j.val) ?_).trans (hj j)⟩
    have := j.isLt
    omega

theorem reads_below {m n : Memory w} {H offset cap base : ℕ} (ls : List TaggedLayer)
    (ag : AgreeBelow H m n) (room : offset + base + tagWords cap ls ≤ H)
    (reads : Reads w n offset cap base ls) : Reads w m offset cap base ls := by
  induction ls generalizing base with
  | nil => trivial
  | cons L ls ih =>
    have he : offset + endPos cap base L.layer + tagWords cap ls ≤ H := by
      simpa [tagWords, words, endPos, address, Nat.mul_add, Nat.add_assoc] using room
    refine ⟨fun i => ?_, ih he reads.2⟩
    have h : address cap base i.val < endPos cap base L.layer :=
      Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_left i.isLt (by omega)) _
    exact (ag _ ((Nat.add_lt_add_left h offset).trans_le ((Nat.le_add_right _ _).trans he))).trans
      (reads.1 i)

/-- Reports of one pass in layer order. Each layer has one additional call
that returns the first site of the next layer. -/
def passReports (ls : List TaggedLayer)
    (sites : (i : Fin ls.length) → Fin ls[i].layer.count → Report w)
    (reset : Fin ls.length → Report w) : List (Report w) :=
  (List.ofFn fun i => List.ofFn (sites i) ++ [reset i]).flatten

private theorem sum_layer_counts (ls : List TaggedLayer) :
    (∑ i : Fin ls.length, ls[i].layer.count) = (ls.map (fun l => l.layer.count)).sum := by
  rw [← List.sum_ofFn]
  congr 1
  exact List.ext_getElem (by simp) (fun _ _ _ => by simp)

theorem pass_calls (ls : List TaggedLayer)
    (sites : (i : Fin ls.length) → Fin ls[i].layer.count → Report w)
    (reset : Fin ls.length → Report w) :
    (passReports ls sites reset).length = (ls.map (fun l => l.layer.count)).sum + ls.length := by
  simp only [passReports, List.length_flatten, List.map_ofFn, Function.comp_apply,
    List.length_append, List.length_ofFn, List.length_singleton, List.sum_ofFn,
    Finset.sum_add_distrib]
  rw [sum_layer_counts]
  simp

private theorem cost_ofFn {m : ℕ} (r : Fin m → Report w) :
    RAMBuckets.cost Report.probes (List.ofFn r) = ∑ i, (1 + (r i).probes) := by
  induction m with
  | zero => simp [RAMBuckets.cost]
  | succ n ih => rw [List.ofFn_succ, RAMBuckets.cost, ih, Fin.sum_univ_succ]

private theorem cost_layers {m : ℕ} (stages : Fin m → List (Report w)) :
    RAMBuckets.cost Report.probes (List.ofFn stages).flatten =
      ∑ i, RAMBuckets.cost Report.probes (stages i) := by
  induction m with
  | zero => simp [RAMBuckets.cost]
  | succ n ih =>
    rw [List.ofFn_succ, List.flatten_cons, RAMBuckets.cost_append, ih, Fin.sum_univ_succ]

/-- Exact native cost, including every reset and all reported operand reads. -/
theorem pass_cost (ls : List TaggedLayer)
    (sites : (i : Fin ls.length) → Fin ls[i].layer.count → Report w)
    (reset : Fin ls.length → Report w) :
    RAMBuckets.cost Report.probes (passReports ls sites reset) =
      ∑ i, ((∑ j, (1 + (sites i j).probes)) + (1 + (reset i).probes)) := by
  simp only [passReports, cost_layers, RAMBuckets.cost_append, cost_ofFn, RAMBuckets.cost,
    Nat.add_zero]

/-- Bound a pass by the measured probe allowance for active calls and its
separate reset allowance. The terminal acceptance is accounted for separately. -/
theorem pass_cost_le (ls : List TaggedLayer)
    (sites : (i : Fin ls.length) → Fin ls[i].layer.count → Report w)
    (reset : Fin ls.length → Report w) {active resetReads : ℕ}
    (hs : ∀ i j, (sites i j).probes ≤ active) (hr : ∀ i, (reset i).probes ≤ resetReads) :
    RAMBuckets.cost Report.probes (passReports ls sites reset) ≤
      (1 + active) * (ls.map (fun l => l.layer.count)).sum + (1 + resetReads) * ls.length := by
  rw [pass_cost]
  calc
    _ ≤ ∑ i : Fin ls.length, ((∑ _j : Fin ls[i].layer.count, (1 + active)) + (1 + resetReads)) :=
      Finset.sum_le_sum fun i _ => Nat.add_le_add
        (Finset.sum_le_sum fun j _ => Nat.add_le_add_left (hs i j) 1) (Nat.add_le_add_left (hr i) 1)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Finset.sum_add_distrib, ← Finset.sum_mul]
      simp only [Nat.cast_id, sum_layer_counts]
      ring

/-- All tags, all rows, and the accepting controller call. The exact count
charges two resets for every layer and a final acceptance even at zero blocks. -/
theorem controller_calls (ls : List TaggedLayer)
    (tags rows : (i : Fin ls.length) → Fin ls[i].layer.count → Report w)
    (tagReset rowReset : Fin ls.length → Report w) (done : Report w) :
    (passReports ls tags tagReset ++ passReports ls rows rowReset ++ [done]).length =
      2 * (ls.map (fun l => l.layer.count)).sum + 2 * ls.length + 1 := by
  rw [List.length_append, List.length_append, List.length_singleton, pass_calls, pass_calls]
  omega

/-- With a fixed operand setup cost on every burst, a role costs one
additional probe. A leaf costs two and a fiber costs two per child plus
three header probes. The resets and the accepting call use setup alone. -/
theorem controller_cost_le (ls : List TaggedLayer) (setup cap : ℕ)
    (tags rows : (i : Fin ls.length) → Fin ls[i].layer.count → Report w)
    (tagReset rowReset : Fin ls.length → Report w) (done : Report w)
    (tag : ∀ i j, (tags i j).probes ≤ setup + 1)
    (row : ∀ i j, (rows i j).probes ≤ setup +
      if i.val = 0 then 2 else 2 * (ls[i].layer.ids j).length + 3)
    (capacity : ∀ (i : Fin ls.length) (j : Fin ls[i].layer.count), (ls[i].layer.ids j).length ≤ cap)
    (tr : ∀ i, (tagReset i).probes ≤ setup) (rr : ∀ i, (rowReset i).probes ≤ setup)
    (terminal : done.probes ≤ setup) :
    RAMBuckets.cost Report.probes (passReports ls tags tagReset ++ passReports ls rows rowReset ++
      [done]) ≤ (2 * setup + 2 * cap + 6) * (ls.map (fun l => l.layer.count)).sum +
        2 * (setup + 1) * ls.length + (setup + 1) := by
  have row' i j : (rows i j).probes ≤ setup + 2 * cap + 3 := by
    have h := row i j
    have bound := capacity i j
    split at h <;> omega
  have ht := pass_cost_le ls tags tagReset tag tr
  have hr := pass_cost_le ls rows rowReset row' rr
  simp only [RAMBuckets.cost_append, RAMBuckets.cost, Nat.add_zero]
  exact (Nat.add_le_add (Nat.add_le_add ht hr) (Nat.add_le_add_left terminal 1)).trans_eq (by ring)

/-- Insert a reset after each stage. No protected write is added if the
active wrapper agrees with its worker on those writes and the reset only
reads or writes above the header. -/
theorem pass_writes (H : ℕ) (ls : List TaggedLayer)
    (sites workers : (i : Fin ls.length) → Fin ls[i].layer.count → Report w)
    (reset : Fin ls.length → Report w)
    (hs : ∀ i j, writesBelow H (sites i j).events = writesBelow H (workers i j).events)
    (hr : ∀ i, writesBelow H (reset i).events = []) :
    writesBelow H (eventLog (passReports ls sites reset)) =
      writesBelow H (eventLog (List.ofFn fun i => List.ofFn (workers i)).flatten) := by
  have flatten {n : ℕ} (f g : Fin n → List (Report w))
      (equal : ∀ i, writesBelow H (eventLog (f i)) = writesBelow H (eventLog (g i))) :
      writesBelow H (eventLog (List.ofFn f).flatten) =
        writesBelow H (eventLog (List.ofFn g).flatten) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [List.ofFn_succ, List.flatten_cons, eventLog, List.flatMap_append,
        writesBelow_append]
      exact congrArg₂ List.append (equal 0)
        (ih (fun i => f i.succ) (fun i => g i.succ) (fun i => equal i.succ))
  apply flatten
  intro i
  have site_eq {n : ℕ} (f g : Fin n → Report w)
      (equal : ∀ j, writesBelow H (f j).events = writesBelow H (g j).events) :
      writesBelow H (eventLog (List.ofFn f)) = writesBelow H (eventLog (List.ofFn g)) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [List.ofFn_succ, eventLog, List.flatMap_cons, writesBelow_append]
      exact congrArg₂ List.append (equal 0)
        (ih (fun j => f j.succ) (fun j => g j.succ) (fun j => equal j.succ))
  simpa only [eventLog, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, writesBelow_append, hr] using site_eq (sites i) (workers i) (hs i)

variable {k A : Type*} [Field k] [CommRing A] {S : BlockSchedule k}
variable (B : S.Templates) (f : B.Entry → A) (hf : B.IsSolution f) {n : ℕ} (T : ℕ)
variable (hT : T * S.laneBits ≤ n) (X : State (S.degreeExponent 0) n)
variable (z : (B.execute f hf T hT X).Choices)

/-- Evaluating the actual register setup counts repeated header loads in each
of its eighteen output expressions. -/
theorem controller_setup_loads : (∑ i, (TraversalController.formulas i).loads) = 257 := by decide

/-- With those setup reads included on every burst, the cost of the complete
two-pass controller is linear in the initial site count times the stage count.
The constant includes the resets and final acceptance. -/
theorem selected_controller_cost :
    let ls := selected B f hf T hT X z
    let cap := B.recordLimit
    let setup := ∑ i, (TraversalController.formulas i).loads
    ∀ (tags rows : (i : Fin ls.length) → Fin ls[i].layer.count → Report w)
      (tagReset rowReset : Fin ls.length → Report w) (done : Report w),
      (∀ i j, (tags i j).probes ≤ setup + 1) →
      (∀ i j, (rows i j).probes ≤ setup +
        if i.val = 0 then 2 else 2 * (ls[i].layer.ids j).length + 3) →
      (∀ i, (tagReset i).probes ≤ setup) → (∀ i, (rowReset i).probes ≤ setup) →
      done.probes ≤ setup →
      RAMBuckets.cost Report.probes (passReports ls tags tagReset ++ passReports ls rows rowReset ++
        [done]) ≤ (2 * cap + 1294) * (((S.steps + 1) * T + 1) * X.positions) := by
  intro ls cap setup tags rows tagReset rowReset done ht hr tr rr terminal
  have layers := selected_layers B f hf T hT X z
  change ls.map TaggedLayer.layer = _ at layers
  have hc (i : Fin ls.length) (j : Fin ls[i].layer.count) : (ls[i].layer.ids j).length ≤ cap := by
    apply selected_capacity B f hf T hT X z
    rw [← layers]
    exact List.mem_map_of_mem (List.getElem_mem i.isLt)
  have hs : (ls.map (fun l => l.layer.count)).sum ≤ ((S.steps + 1) * T + 1) * X.positions := by
    have h := selected_count_sum_le B f hf T hT X z
    rw [← layers, List.map_map] at h
    exact h
  let visits := ((S.steps + 1) * T + 1) * X.positions
  have hp : 0 < X.positions := X.positions_pos
  have hbound : (S.steps + 1) * T + 1 ≤ visits := Nat.le_mul_of_pos_right _ hp
  have hl : ls.length ≤ visits := by
    have h := executeLevels_length B f hf T hT X z
    simp only [ls, selected, List.length_cons, List.length_map]
    exact (Nat.succ_le_succ h).trans hbound
  have hv : 1 ≤ visits := (Nat.succ_pos _).trans_le hbound
  have hz : setup = 257 := controller_setup_loads
  calc
    _ ≤ _ := controller_cost_le ls setup cap tags rows tagReset rowReset done
      ht hr hc tr rr terminal
    _ ≤ (2 * setup + 2 * cap + 6) * visits + 2 * (setup + 1) * visits + (setup + 1) * visits :=
      Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ hs) (Nat.mul_le_mul_left _ hl))
        (Nat.le_mul_of_pos_right _ hv)
    _ = _ := by rw [hz]; change _ = (2 * cap + 1294) * visits; ring

/-- All protected data needed by the DFS survives the control-cell updates:
the selected role words and ordered placement rows, the final-bit gap, and
every raw input below the descriptor base. -/
theorem selected_readback (base F H : ℕ) (raw final : Memory w)
    (boundary : base + 2 * words B.recordLimit (selectedLayers B f hf T hT X z) + F ≤ H)
    (ag : let ls := selectedLayers B f hf T hT X z
      let size := words B.recordLimit ls
      AgreeBelow H final (build B.recordLimit base base ls
        (writeTags (size + F) B.recordLimit base (selected B f hf T hT X z) raw)))
    (rowFit : base + words B.recordLimit (selectedLayers B f hf T hT X z) < 2 ^ w) :
    let ls := selectedLayers B f hf T hT X z
    let roles := selected B f hf T hT X z
    let cap := B.recordLimit
    let size := words cap ls
    Reads w final (size + F) cap base roles ∧ AllRows w final cap base base ls ∧
      (∀ x < base, final x = raw x) ∧
      ∀ i < F, final (base + size + i) = raw (base + size + i) := by
  intro ls roles cap size
  have hroles : tagWords cap roles = size := by
    rw [tagWords, show roles.map TaggedLayer.layer = ls from selected_layers B f hf T hT X z]
  let tagged := writeTags (size + F) cap base roles raw
  let reference := build cap base base ls tagged
  have equal : AgreeBelow H final reference := ag
  change base + 2 * size + F ≤ H at boundary
  obtain ⟨rolesOK, bitsOK, rowsOK⟩ := selected_tags_and_rows B f hf T hT X z base F raw rowFit
  refine ⟨reads_below roles equal (by rw [hroles]; omega) rolesOK,
    allRows_below ls equal (by change base + size ≤ H; omega)
      (selected_capacity B f hf T hT X z) rowsOK, ?_, ?_⟩
  · intro x hx
    exact (equal x (by omega)).trans ((build_outside ls cap base base tagged x (Or.inl hx)).trans
      (write_tags_outside _ _ _ roles raw x (Or.inl (hx.trans_le (Nat.le_add_left _ _)))))
  · intro i hi
    exact (equal _ (by omega)).trans (bitsOK i hi)

/-- Select native workers on the actual branch. Any controller log with the
same visible writes reproduces their complete memory below the header. -/
theorem selected_native_replay (base F H : ℕ) (raw : Memory w)
    (ds : let vs := executeLevels B f hf T hT X z
      (i : Fin vs.length) → LevelDirectory vs[i] raw base)
    (room : base + 2 * words B.recordLimit (selectedLayers B f hf T hT X z) + F ≤ H)
    (fit : H < 2 ^ w) :
    let E := B.execute f hf T hT X
    let data := B.records f hf T hT X
    let c := E.termChain data z
    let ords := branchOrders E data z
    let old := siteOrder X
    let cap := B.recordLimit
    let ls := selectedLayers B f hf T hT X z
    let offset := words cap ls + F
    let roles := selected B f hf T hT X z
    let dirs := selectedDirectories B f hf T hT X z raw base ds
    let rowJobs := DirectoryRun.Worker.leaf cap base old.length ::
      DirectoryRun.workers c ords old dirs cap base (address cap base old.length)
    ∃ ts rs, RolePasses offset cap base roles raw ts ∧
      DirectoryRun.Segments rowJobs (after raw (eventLog ts)) rs ∧
      ∀ (m : Memory w) (controller : List (Report w)), AgreeBelow H m raw →
        writesBelow H (eventLog controller) = writesBelow H (eventLog (ts ++ rs)) →
        AgreeBelow H (after m (eventLog controller))
          (build cap base base ls (writeTags offset cap base roles raw)) := by
  intro E data c ords old cap ls offset roles dirs jobs
  obtain ⟨ts, rs, tags, rows, image, _⟩ :=
    native_arena B f hf T hT X z base F raw ds (room.trans_lt fit)
  refine ⟨ts, rs, tags, rows, fun m controller ag hw x hx => ?_⟩
  exact (replay_below ag hw x hx).trans (congrFun image x)

end PairSimulation.TraversalRoles.ControllerMemory

end VPVNP
end Computability
end OAI
