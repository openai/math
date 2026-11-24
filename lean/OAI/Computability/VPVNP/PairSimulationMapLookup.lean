import OAI.Computability.VPVNP.MotifConversion
import OAI.Computability.VPVNP.PrimedInputRAMFlowLinks
import OAI.Computability.VPVNP.PrimedCounterGuessWord

/-!
# Native fixed-table lookups for motif maps

The code compares the supplied fields with fixed public words. On the first
matching row it loads the corresponding selector or label ordinal. Reaching
the end of the table transfers control to the rejecting instruction.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapLookup

open BurstRAM BurstRAM.PrivateRAM PrimedCounter.GuessWord PrimedInputRAM PrimedStackRAM

variable {ι X : Type*} {w p r k : ℕ}

/-- A finite decision tree with public constants at the comparison nodes. -/
inductive Tree (ι X : Type*) (k : ℕ) where
  | miss
  | hit (x : X)
  | test (i : ι) (constant : Fin k) (yes no : Tree ι X k)

namespace Tree

/-- One native dispatch loads an output or goes to the bad exit. Each
comparison takes one public-word load and one conditional jump. -/
def eval (pub : Fin k → Word w) (input : ι → Word w) : Tree ι X k → Option X × ℕ
  | .miss => (none, 1)
  | .hit x => (some x, 1)
  | .test i j yes no =>
    let a := if input i = pub j then eval pub input yes else eval pub input no
    (a.1, 2 + a.2)

/-- Lower the decision tree to the same structured finite table compiler
used by the coefficient machine. -/
def flow (query : ι → Fin r) (tmp out : Fin r) (name : X → Fin k) : Tree ι X k → Flow r k
  | .miss => .line (.guardLt tmp tmp)
  | .hit x => .line (.publicWord out (name x))
  | .test i j yes no =>
    (Flow.line (.publicWord tmp j)).seq
      (.ifEq (query i) tmp (flow query tmp out name yes) (flow query tmp out name no))

/-- Success leaves the ordinal in the output register at the normal exit.
A miss reaches the rejecting exit. Each path consumes exactly its computed
number of ticks, without a probe or binary choice. -/
theorem native (t : Tree ι X k) (query : ι → Fin r) (tmp out : Fin r) (name : X → Fin k)
    (ht : ∀ i, query i ≠ tmp) (M : Machine w p r k)
    (label : (t.flow query tmp out name).Label → Fin p)
    (stop bad : Fin p) (hl : Flow.Linked M (t.flow query tmp out name) label stop bad)
    (c : Config w p r) (hc : c.pc = label (t.flow query tmp out name).entry) :
    let a := t.eval M.publicData (fun i ↦ c.reg (query i))
    ∃ final, Prefix M c (List.replicate a.2 .tick) final ∧
      (match a.1 with
       | none => final.pc = bad
       | some x => final.pc = stop ∧ final.reg out = M.publicData (name x)) ∧
      (∀ j, j ≠ tmp → j ≠ out → final.reg j = c.reg j) ∧
      final.privateMem = c.privateMem ∧ final.persistent = c.persistent := by
  dsimp only
  induction t generalizing c with
  | miss =>
    have hs : M.program.step c = .localStep {c with pc := bad} := by
      rw [show M.program.step c = (M.code c.pc).run M.publicData c from rfl, hc,
        hl.atLabel _]
      change CallAction.localStep {c with pc := if c.reg tmp < c.reg tmp then stop else bad} = _
      simp
    exact ⟨_, .tick hs (.nil _), rfl, fun _ _ _ ↦ rfl, rfl, rfl⟩
  | hit x =>
    let final := c.put stop out (M.publicData (name x))
    have hs : M.program.step c = .localStep final := by
      rw [show M.program.step c = (M.code c.pc).run M.publicData c from rfl, hc,
        hl.atLabel _]
      rfl
    exact ⟨_, .tick hs (.nil _), ⟨rfl, by simp [final]⟩,
      fun j _ hj ↦ by simp [final, Config.put, Function.update_of_ne hj], rfl, rfl⟩
  | test i j yes no hy hn =>
    let cond := Flow.ifEq (query i) tmp (yes.flow query tmp out name) (no.flow query tmp out name)
    let place := fun a : cond.Label ↦ label (.inr a)
    let mid := c.put (place cond.entry) tmp (M.publicData j)
    have hs : M.program.step c = .localStep mid := by
      rw [show M.program.step c = (M.code c.pc).run M.publicData c from rfl, hc, hl.atLabel _]
      rfl
    have heq (u : ι) : mid.reg (query u) = c.reg (query u) := by
      simp [mid, Config.put, Function.update_of_ne (ht u)]
    have hcond : Flow.Linked M cond place stop bad := hl.seqRight
    have jump : M.program.step mid = .localStep {mid with pc :=
        (if c.reg (query i) = M.publicData j then
          place (.inr (.inl (yes.flow query tmp out name).entry))
        else place (.inr (.inr (no.flow query tmp out name).entry)))} := by
      rw [show M.program.step mid = (M.code mid.pc).run M.publicData mid from rfl,
        show mid.pc = place cond.entry from rfl, hcond.atLabel _]
      change CallAction.localStep
        {mid with pc := if mid.reg (query i) = mid.reg tmp then _ else _} = _
      rw [heq, show mid.reg tmp = M.publicData j from Config.put_same ..]
      rfl
    have hinputs : (fun u ↦ mid.reg (query u)) = fun u ↦ c.reg (query u) := funext heq
    have hrest (a : Fin r) (ha : a ≠ tmp) : mid.reg a = c.reg a := by
      simp [mid, Config.put, Function.update_of_ne ha]
    by_cases h : c.reg (query i) = M.publicData j
    · rw [ite_eq_left h] at jump
      obtain ⟨d, pre, hd, ho, hm, hp⟩ := hy _ hcond.ifEqYes
        {mid with pc := place (.inr (.inl (yes.flow query tmp out name).entry))} rfl
      change Prefix M _ (List.replicate (yes.eval _ (fun u ↦ mid.reg (query u))).2 .tick) d at pre
      rw [hinputs] at pre
      change (match (yes.eval _ (fun u ↦ mid.reg (query u))).1 with
        | none => _ | some _ => _) at hd
      rw [hinputs] at hd
      simp only [eval, h, ↓reduceIte, List.replicate_add]
      exact ⟨d, .tick hs (.tick jump pre), hd, fun a ht' ho' ↦
        (ho a ht' ho').trans (hrest a ht'), hm, hp⟩
    · rw [ite_eq_right h] at jump
      obtain ⟨d, pre, hd, ho, hm, hp⟩ := hn _ hcond.ifEqNo
        {mid with pc := place (.inr (.inr (no.flow query tmp out name).entry))} rfl
      change Prefix M _ (List.replicate (no.eval _ (fun u ↦ mid.reg (query u))).2 .tick) d at pre
      rw [hinputs] at pre
      change (match (no.eval _ (fun u ↦ mid.reg (query u))).1 with
        | none => _ | some _ => _) at hd
      rw [hinputs] at hd
      simp only [eval, h, ↓reduceIte, List.replicate_add]
      exact ⟨d, .tick hs (.tick jump pre), hd, fun a ht' ho' ↦
        (ho a ht' ho').trans (hrest a ht'), hm, hp⟩

end Tree

/-- Comparing a row stops at the first differing field. -/
def row (key : ι → Fin k) (yes no : Tree ι X k) : List ι → Tree ι X k
  | [] => yes
  | i :: is => .test i (key i) (row key yes no is) no

/-- Compile a finite table in its given order, permitting partial tables. -/
def table (fields : List ι) (key : X → ι → Fin k) : List X → Tree ι X k
  | [] => .miss
  | x :: xs => row (key x) (.hit x) (table fields key xs) fields

private theorem row_eval (pub : Fin k → Word w) (input : ι → Word w) (key : ι → Fin k)
    (yes no : Tree ι X k) (fields : List ι) :
    let branch := if fields.all (fun i ↦ decide (input i = pub (key i))) then yes else no
    ((row key yes no fields).eval pub input).1 = (branch.eval pub input).1 ∧
      ((row key yes no fields).eval pub input).2 ≤
        2 * fields.length + (branch.eval pub input).2 := by
  induction fields with
  | nil => simp [row]
  | cons i is ih =>
    by_cases h : input i = pub (key i)
    · simp only [row, Tree.eval, h, ↓reduceIte, List.all_cons, decide_true, Bool.true_and,
        List.length_cons, Nat.mul_succ]
      exact ⟨ih.1, by have := ih.2; omega⟩
    · simp [row, Tree.eval, h]

/-- The path returns the first matching row and performs at most two tests
per row field plus the final dispatch. -/
theorem table_eval (pub : Fin k → Word w) (input : ι → Word w) (fields : List ι)
    (key : X → ι → Fin k) (xs : List X) :
    ((table fields key xs).eval pub input).1 =
        xs.find? (fun x ↦ fields.all fun i ↦ decide (input i = pub (key x i))) ∧
      ((table fields key xs).eval pub input).2 ≤ 2 * fields.length * xs.length + 1 := by
  induction xs with
  | nil => simp [table, Tree.eval]
  | cons x xs ih =>
    have hr := row_eval pub input (key x) (.hit x) (table fields key xs) fields
    by_cases h : fields.all (fun i ↦ decide (input i = pub (key x i))) = true
    · simp only [h, ↓reduceIte, Tree.eval] at hr
      simp only [table, List.find?_cons, h, List.length_cons, Nat.mul_succ]
      exact ⟨hr.1, by have := hr.2; omega⟩
    · simp only [Bool.eq_false_iff.mpr h, Bool.false_eq_true, ↓reduceIte] at hr
      simp only [table, List.find?_cons, h, List.length_cons, Nat.mul_succ]
      exact ⟨hr.1.trans ih.1, by have := hr.2; have := ih.2; omega⟩


/-- Public ports can be allocated from the fixed rows and fields alone. -/
def publicData (ports : (X × ι ⊕ X) ≃ Fin k) (key : X → ι → Word w)
    (name : X → Word w) (i : Fin k) : Word w :=
  (ports.symm i).elim (fun q ↦ key q.1 q.2) name

@[simp] theorem publicData_key (ports : (X × ι ⊕ X) ≃ Fin k) (key : X → ι → Word w)
    (name : X → Word w) (x : X) (i : ι) :
    publicData ports key name (ports (.inl (x, i))) = key x i := by simp [publicData]

@[simp] theorem publicData_name (ports : (X × ι ⊕ X) ≃ Fin k) (key : X → ι → Word w)
    (name : X → Word w) (x : X) :
    publicData ports key name (ports (.inr x)) = name x := by simp [publicData]

/-- A pathwise step cap, actual normal or bad exit, and the complete
private-memory frame available at that exit. -/
def Runs (M : Machine w p r k) (c : Config w p r) (stop bad : Fin p) (tmp out : Fin r)
    (name : X → Word w) (result : Option X) (cap : ℕ) : Prop :=
  ∃ steps final, steps ≤ cap ∧ Prefix M c (List.replicate steps .tick) final ∧
    (match result with
     | none => final.pc = bad
     | some x => final.pc = stop ∧ final.reg out = name x) ∧
    (∀ j, j ≠ tmp → j ≠ out → final.reg j = c.reg j) ∧
    final.privateMem = c.privateMem ∧ final.persistent = c.persistent

/-- A deterministic tick prefix ending in the rejecting instruction rejects
with every fuel budget, including one that expires inside the prefix. -/
theorem reject_after_ticks {M : Machine w p r k} {c final : Config w p r}
    {es : List (Event w)} (h : Prefix M c es final) (ticks : ∀ e ∈ es, e = .tick)
    (bad : M.code final.pc = .reject) (fuel : ℕ) (mem : Memory w) (bits : List Bool) :
    execute M.program fuel c mem bits = none := by
  induction h generalizing fuel with
  | nil =>
    cases fuel <;> simp [execute, Machine.program, bad, Instr.run]
  | tick step _ ih =>
    cases fuel with
    | zero => rfl
    | succ fuel =>
      simp [execute, step, ih (fun e he ↦ ticks e (List.mem_cons_of_mem _ he)) bad fuel]
  | @choice _ _ b _ _ _ _ _ => exact (by simpa using ticks (.choice b) (by simp) : False).elim

/-- A missing key rejects on every continuation budget and branch tape. -/
theorem Runs.rejects {M : Machine w p r k} {c : Config w p r} {stop bad : Fin p}
    {tmp out : Fin r} {name : X → Word w} {cap : ℕ}
    (h : Runs M c stop bad tmp out name none cap) (hb : M.code bad = .reject)
    (fuel : ℕ) (mem : Memory w) (bits : List Bool) : execute M.program fuel c mem bits = none := by
  obtain ⟨n, d, _, pref, hd, _⟩ := h
  exact reject_after_ticks pref (fun e he ↦ (List.eq_of_mem_replicate he))
    (hd ▸ hb) fuel mem bits

/-- The actual instructions read the given public key words. In particular
a short path on an early match satisfies the same cap as the longest path. -/
theorem native_table (xs : List X) (fields : List ι) (key : X → ι → Fin k)
    (name : X → Fin k) (query : ι → Fin r) (tmp out : Fin r) (ht : ∀ i, query i ≠ tmp)
    (M : Machine w p r k) (label : ((table fields key xs).flow query tmp out name).Label → Fin p)
    (stop bad : Fin p) (hl : Flow.Linked M ((table fields key xs).flow query tmp out name)
      label stop bad) (c : Config w p r)
    (hc : c.pc = label ((table fields key xs).flow query tmp out name).entry) :
    Runs M c stop bad tmp out (M.publicData ∘ name)
      (xs.find? (fun x ↦ fields.all fun i ↦ decide (c.reg (query i) = M.publicData (key x i))))
      (2 * fields.length * xs.length + 1) := by
  obtain ⟨d, pre, hd, ho, hm, hp⟩ := (table fields key xs).native query tmp out name ht M label
    stop bad hl c hc
  obtain ⟨hr, hn⟩ := table_eval M.publicData (fun i ↦ c.reg (query i)) fields key xs
  rw [hr] at hd
  exact ⟨_, d, hn, pre, hd, ho, hm, hp⟩

/-- Allocate the public ports once and compile an ordinary finite program.
Its opcode table and register numbering are independent of the word width. -/
def tableFlow (ports : (X × ι ⊕ X) ≃ Fin k) (xs : List X) (fields : List ι)
    (query : ι → Fin r) (tmp out : Fin r) : Flow r k :=
  (table fields (fun x i ↦ ports (.inl (x, i))) xs).flow query tmp out (fun x ↦ ports (.inr x))

/-- The compiler provides a concrete instruction table with all constants
installed. A caller can enter with arbitrary private memory and input
registers. The common exit returns the ordinal and the bad exit rejects. -/
theorem compiled_table (ports : (X × ι ⊕ X) ≃ Fin k) (xs : List X) (fields : List ι)
    (query : ι → Fin r) (tmp out : Fin r) (ht : ∀ i, query i ≠ tmp)
    (key : X → ι → Word w) (name : X → Word w) (rs : Fin r → Word w)
    (state : Word w) (priv : Word w → Word w) :
    let block := tableFlow ports xs fields query tmp out
    let M := (block.template (some out)).instantiate w (publicData ports key name)
    let c : Config w (block.length + 2) r := ⟨block.pc block.entry, state, rs, priv⟩
    Runs M c block.exitPC block.rejectPC tmp out name
      (xs.find? (fun x ↦ fields.all fun i ↦ decide (rs (query i) = key x i)))
      (2 * fields.length * xs.length + 1) ∧ M.code block.rejectPC = .reject := by
  dsimp only
  let block := tableFlow ports xs fields query tmp out
  let pub := publicData ports key name
  let M := (block.template (some out)).instantiate w pub
  let c : Config w (block.length + 2) r := ⟨block.pc block.entry, state, rs, priv⟩
  have h := native_table xs fields (fun x i ↦ ports (.inl (x, i))) (fun x ↦ ports (.inr x))
    query tmp out ht M block.pc block.exitPC block.rejectPC
    (Flow.template_linked block (some out) pub) c rfl
  refine ⟨?_, ?_⟩
  · simpa only [M, c, Template.instantiate, pub, Function.comp_def, publicData_key,
      publicData_name] using h
  · change ((block.template (some out)).code block.rejectPC).resize w = _
    rw [Flow.template_reject]
    rfl

/-- Widen a fixed base-motif field to one machine register without truncation. -/
def widen {b : ℕ} (h : b ≤ w) : Word b ↪ Word w :=
  Fin.castLEEmb (Nat.pow_le_pow_right (by decide) h)

/-- Compare the anchor word against the fixed selector codes. The first
matching selector returns its recorded ordinal. An unused code reaches
the rejecting exit in at most twice the table length plus one tick. -/
theorem native_selector {b : ℕ} (fits : b ≤ w) (xs : List X) (code : X ↪ Word b)
    (key name : X → Fin k) (src tmp out : Fin r) (ht : src ≠ tmp) (tag : Word b)
    (M : Machine w p r k) (hkey : ∀ x, M.publicData (key x) = widen fits (code x))
    (label : ((table [()] (fun x _ ↦ key x) xs).flow (fun _ ↦ src) tmp out name).Label → Fin p)
    (stop bad : Fin p) (hl : Flow.Linked M
      ((table [()] (fun x _ ↦ key x) xs).flow (fun _ ↦ src) tmp out name) label stop bad)
    (c : Config w p r) (hc : c.pc = label
      ((table [()] (fun x _ ↦ key x) xs).flow (fun _ ↦ src) tmp out name).entry)
    (hs : c.reg src = widen fits tag) :
    Runs M c stop bad tmp out (M.publicData ∘ name) (MotifEntry.decode xs code tag)
      (2 * xs.length + 1) := by
  have h := native_table xs [()] (fun x _ ↦ key x) name (fun _ ↦ src) tmp out
    (fun _ ↦ ht) M label stop bad hl c hc
  simpa [MotifEntry.decode, hs, hkey, eq_comm] using h


section Label

open MotifGrid MotifBlocks MotifSelector MotifDemandPadding MotifConversion

variable {J D S : Type} [Fintype J] [Fintype D] [Fintype S]
variable {src dst : D → J} {P : Supply J S}

open Classical in
/-- Absent endpoints contribute zero to the fixed tuple of compared words.
The two ends of a loop have distinct positions. -/
noncomputable def halfKey {E : Type} (a b : E → J) (width : E → ℕ) (fit : ∀ e, width e ≤ w)
    (j : J) (x : HalfBits a b width j) : Bool × E → BurstRAM.Word w
  | (false, e) => if h : j = a e then widen (fit e) (x.1 e h) else 0
  | (true, e) => if h : j = b e then widen (fit e) (x.2 e h) else 0

omit [Fintype J] in
private theorem halfKey_injective {E : Type} (a b : E → J) (width : E → ℕ)
    (fit : ∀ e, width e ≤ w) (j : J) : Function.Injective (halfKey a b width fit j) := by
  intro x y he
  apply Prod.ext
  · funext e h
    have eq := congrFun he (false, e)
    simpa [halfKey, h] using eq
  · funext e h
    have eq := congrFun he (true, e)
    simpa [halfKey, h] using eq

variable {K : Type} [Field K] {p₀ : D → ℚ} {q₀ : S → ℚ} {H H' : ℝ}
  (B : FixedBlock K src dst P (realWidths p₀) (realWidths q₀) H H')
  (z : B.grid.demands) (s : Selector B) (j : J)

/-- Exactly the two input tuples in the fixed label lookup of the motif evaluator. -/
abbrev LabelRow := HalfBits src dst (baseDemand B z) j ×
  Half P (fun e ↦ MotifSelector.Word (basePayload B s e)) j

open Classical in
/-- The fixed matrix has one row for each pair of local coordinates. -/
noncomputable def labelRows : List (LabelRow B z s j) := Finset.univ.toList

theorem mem_labelRows (x : LabelRow B z s j) : x ∈ labelRows B z s j := by simp [labelRows]

/-- An endpoint field used in matrix-row lookup. The sum distinguishes demand from supply
edges, and the Boolean selects the source or target endpoint. -/
abbrev LabelField (D S : Type) := (Bool × D) ⊕ (Bool × S)

open Classical in
/-- All endpoints can be numbered once for a fixed base motif. -/
noncomputable def labelFields (D S : Type) [Fintype D] [Fintype S] : List (LabelField D S) :=
  Finset.univ.toList

theorem mem_labelFields (i : LabelField D S) : i ∈ labelFields D S := by simp [labelFields]

/-- The same bound holds at all grid points, selectors and parties of the
fixed motif, before choosing the widths or the number of outer copies. -/
theorem label_step_cap :
    2 * (labelFields D S).length * (labelRows B z s j).length + 1 ≤
      2 * (labelFields D S).length * Nat.card (parameterData B).Entry + 1 := by
  classical
  let incl : LabelRow B z s j → (parameterData B).Entry := fun x ↦ lookup B z s j x.1 x.2
  have hinj : Function.Injective incl := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h₁ := eq_of_heq (Sigma.mk.inj h).2
    have h₂ := eq_of_heq (Sigma.mk.inj h₁).2
    exact eq_of_heq (Sigma.mk.inj h₂).2
  have hcard := Nat.card_le_card_of_injective incl hinj
  simp only [labelRows, Finset.length_toList, Finset.card_univ]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (by simpa using hcard)) 1

variable (fd : ∀ e, baseDemand B z e ≤ w) (fs : ∀ e, basePayload B s e ≤ w)

/-- Every demand and supply coordinate is represented by its widened natural digit. -/
noncomputable def labelKey (x : LabelRow B z s j) : LabelField D S → BurstRAM.Word w :=
  Sum.elim (halfKey src dst (baseDemand B z) fd j x.1)
    (halfKey P.src P.dst (basePayload B s) fs j x.2)

theorem labelKey_injective : Function.Injective (labelKey B z s j fd fs) := by
  intro x y h
  exact Prod.ext (halfKey_injective _ _ _ fd j (funext (fun i ↦ congrFun h (.inl i))))
    (halfKey_injective _ _ _ fs j (funext (fun i ↦ congrFun h (.inr i))))

/-- Scan the complete fixed local matrix. The query registers hold the
decoded fields of one copy, in their own endpoint positions. A successful
scan emits precisely the ordinal of the parameter in equation (6.2). -/
theorem native_label_exact (rows : List (LabelRow B z s j)) (complete : ∀ x, x ∈ rows)
    (fields : List (LabelField D S)) (covers : ∀ i, i ∈ fields)
    (key : LabelRow B z s j → LabelField D S → Fin k) (name : LabelRow B z s j → Fin k)
    (query : LabelField D S → Fin r) (tmp out : Fin r) (ht : ∀ i, query i ≠ tmp)
    (ordinal : (parameterData B).Entry → BurstRAM.Word w) (M : Machine w p r k)
    (hkey : ∀ y i, M.publicData (key y i) = labelKey B z s j fd fs y i)
    (hname : ∀ y, M.publicData (name y) = ordinal (lookup B z s j y.1 y.2))
    (label : ((table fields key rows).flow query tmp out name).Label → Fin p)
    (stop bad : Fin p) (hl : Flow.Linked M ((table fields key rows).flow query tmp out name)
      label stop bad) (c : Config w p r)
    (hc : c.pc = label ((table fields key rows).flow query tmp out name).entry)
    (x : LabelRow B z s j) (hquery : ∀ i, c.reg (query i) = labelKey B z s j fd fs x i) :
    let a := (table fields key rows).eval M.publicData (labelKey B z s j fd fs x)
    ∃ final, Prefix M c (List.replicate a.2 .tick) final ∧
      final.pc = stop ∧ final.reg out = ordinal (lookup B z s j x.1 x.2) ∧
      (∀ i, i ≠ tmp → i ≠ out → final.reg i = c.reg i) ∧
      final.privateMem = c.privateMem ∧ final.persistent = c.persistent := by
  intro a
  let isMatch := fun y ↦ fields.all fun i ↦ decide (c.reg (query i) = M.publicData (key y i))
  have hm (y) : isMatch y = true ↔ x = y := by
    simp only [isMatch, List.all_eq_true, decide_eq_true_eq, hquery, hkey]
    exact ⟨fun h ↦ labelKey_injective B z s j fd fs (funext (fun i ↦ h i (covers i))),
      fun e _ _ ↦ e ▸ rfl⟩
  have hf : rows.find? isMatch = some x := by
    cases he : rows.find? isMatch with
    | none =>
      exact ((List.find?_eq_none.mp he x (complete x)) ((hm x).2 rfl)).elim
    | some y =>
      have eq := (hm y).1 (List.find?_some he)
      rw [eq]
  obtain ⟨final, pre, exit, frame, mem, state⟩ :=
    (table fields key rows).native query tmp out name ht M label stop bad hl c hc
  have result := (table_eval M.publicData (fun i ↦ c.reg (query i)) fields key rows).1.trans hf
  rw [result] at exit
  rw [funext hquery] at pre
  exact ⟨final, pre, exit.1, exit.2.trans (hname x), frame, mem, state⟩

/-- The complete local matrix lookup also satisfies its uniform table cap. -/
theorem native_label (rows : List (LabelRow B z s j)) (complete : ∀ x, x ∈ rows)
    (fields : List (LabelField D S)) (covers : ∀ i, i ∈ fields)
    (key : LabelRow B z s j → LabelField D S → Fin k) (name : LabelRow B z s j → Fin k)
    (query : LabelField D S → Fin r) (tmp out : Fin r) (ht : ∀ i, query i ≠ tmp)
    (ordinal : (parameterData B).Entry → BurstRAM.Word w) (M : Machine w p r k)
    (hkey : ∀ y i, M.publicData (key y i) = labelKey B z s j fd fs y i)
    (hname : ∀ y, M.publicData (name y) = ordinal (lookup B z s j y.1 y.2))
    (label : ((table fields key rows).flow query tmp out name).Label → Fin p)
    (stop bad : Fin p) (hl : Flow.Linked M ((table fields key rows).flow query tmp out name)
      label stop bad) (c : Config w p r)
    (hc : c.pc = label ((table fields key rows).flow query tmp out name).entry)
    (x : LabelRow B z s j) (hquery : ∀ i, c.reg (query i) = labelKey B z s j fd fs x i) :
    Runs M c stop bad tmp out (fun y ↦ ordinal (lookup B z s j y.1 y.2)) (some x)
      (2 * fields.length * rows.length + 1) := by
  let a := (table fields key rows).eval M.publicData (labelKey B z s j fd fs x)
  obtain ⟨final, pre, pc, value, frame, mem, state⟩ :=
    native_label_exact B z s j fd fs rows complete fields covers key name query tmp out ht
      ordinal M hkey hname label stop bad hl c hc x hquery
  exact ⟨a.2, final, (table_eval ..).2, pre, ⟨pc, value⟩, frame, mem, state⟩

end Label

end PairSimulation.MapLookup

end VPVNP
end Computability
end OAI
