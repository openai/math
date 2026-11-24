import OAI.Computability.VPVNP.PairSimulationAnchorDecode
import OAI.Computability.VPVNP.PairSimulationMapStream

/-!
# Native dispatch and repetition of the selected map rows

Each pass reads the next private selector ordinal and compares it with the
fixed selector ports. A match jumps directly to the corresponding row's
first instruction. All row subroutines return to the same label store.
After the last copy the driver transfers control to the full-width test.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapDriver

open BurstRAM BurstRAM.PrivateRAM PrimedCounter.GuessWord
open scoped Fin.CommRing

variable {S : Type*} {w p r k u : ℕ}

private abbrev word (w n : ℕ) : Word w := (n : Word w)

private theorem val_word {n : ℕ} (h : n < 2 ^ w) : (word w n).val = n := Nat.mod_eq_of_lt h

/-- Registers hold the selector cursor and end, label cursor, one, loaded
ordinal, comparison temporary, and the label returned by the selected row. -/
structure Program (S : Type*) (p r k : ℕ) where
  /-- Selectors in the order the driver tests when dispatching a decoded ordinal. -/
  selectors : List S
  /-- Public-word position holding the dispatch ordinal for each selector. -/
  port : S → Fin k
  /-- Place the selector cursor and end, label cursor, increment, loaded ordinal, comparison
  temporary, and returned label in seven distinct registers. -/
  reg : Fin 7 ↪ Fin r
  /-- Program counters for the five outer-loop instructions that test for completion, load a
  selector, store a label, and advance both cursors. -/
  pc : Fin 5 → Fin p
  /-- Instruction addresses for one selector's dispatch pair. The false branch loads its public
  ordinal and the true branch compares that ordinal with the private one. -/
  comparePC : S → Bool → Fin p
  /-- Entry address of the row evaluator chosen by a successful selector comparison. -/
  rowPC : S → Fin p
  /-- Continuation that checks final widths after the driver consumes the selector array. -/
  checkWidths : Fin p
  /-- Rejecting continuation taken when the comparison chain exhausts all selectors. -/
  bad : Fin p

namespace Program

variable (P : Program S p r k)

/-- An exhausted comparison chain jumps to the rejecting exit. -/
def first : List S → Fin p
  | [] => P.bad
  | x :: _ => P.comparePC x false

/-- The five outer-loop instructions for checking the selector cursor, loading the next
ordinal, storing the row's returned label, and incrementing the two cursors. -/
def instruction : Fin 5 → Instr w p r k :=
  ![.jumpEq (P.reg 0) (P.reg 1) P.checkWidths (P.pc 1),
    .loadPrivate (P.reg 4) (P.reg 0) (P.first P.selectors),
    .storePrivate (P.reg 2) (P.reg 6) (P.pc 3),
    .binary .add (P.reg 0) (P.reg 0) (P.reg 3) (P.pc 4),
    .binary .add (P.reg 2) (P.reg 2) (P.reg 3) (P.pc 0)]

theorem resize_instruction (i : Fin 5) :
    (P.instruction (w := 1) i).resize w = P.instruction i := by fin_cases i <;> rfl

/-- Two actual opcodes per fixed selector, with an independent hit target. -/
def dispatch (M : Machine w p r k) : List S → Prop
  | [] => True
  | s :: ss =>
    M.code (P.comparePC s false) = .publicWord (P.reg 5) (P.port s) (P.comparePC s true) ∧
    M.code (P.comparePC s true) =
      .jumpEq (P.reg 4) (P.reg 5) (P.rowPC s) (P.first ss) ∧ dispatch M ss

/-- The machine implements both the five outer driver instructions and the ordered
load-and-compare dispatch for every selector in the table. -/
structure Linked (M : Machine w p r k) : Prop where
  outer : ∀ i, M.code (P.pc i) = P.instruction i
  table : P.dispatch M P.selectors

variable {P} {M : Machine w p r k}

open Classical in
/-- Two instructions per candidate through the first match, in table order. -/
noncomputable def dispatchSteps : List S → S → ℕ
  | [], _ => 0
  | a :: as, s => if s = a then 2 else 2 + dispatchSteps as s

/-- Successful dispatch consumes at most two instructions per selector.
The selected row receives the loaded ordinal and the same private memory. -/
theorem dispatch_hit_exact (ss : List S) (hl : P.dispatch M ss)
    (inj : Function.Injective (M.publicData ∘ P.port)) (s : S) (member : s ∈ ss)
    (c : Config w p r) (hc : c.pc = P.first ss) (hs : c.reg (P.reg 4) = M.publicData (P.port s)) :
    ∃ n d, n ≤ 2 * ss.length ∧ n = dispatchSteps ss s ∧
      Prefix M c (List.replicate n .tick) d ∧ d.pc = P.rowPC s ∧
      (∀ j, j ≠ P.reg 5 → d.reg j = c.reg j) ∧
      d.privateMem = c.privateMem ∧ d.persistent = c.persistent := by
  induction ss generalizing c with
  | nil => simp at member
  | cons x xs ih =>
    let mid := c.put (P.comparePC x true) (P.reg 5) (M.publicData (P.port x))
    have load : M.program.step c = .localStep mid := by
      rw [show M.program.step c = (M.code c.pc).run M.publicData c from rfl, hc, first, hl.1]
      rfl
    have test : M.program.step mid = .localStep {mid with pc :=
        (if M.publicData (P.port s) = M.publicData (P.port x) then P.rowPC x else P.first xs)} := by
      rw [show M.program.step mid = (M.code mid.pc).run M.publicData mid from rfl,
        show mid.pc = P.comparePC x true from rfl, hl.2.1]
      change CallAction.localStep {mid with pc :=
        (if mid.reg (P.reg 4) = mid.reg (P.reg 5) then P.rowPC x else P.first xs)} = _
      simp [mid, Config.put, hs]
    have keep (j : Fin r) (hj : j ≠ P.reg 5) : mid.reg j = c.reg j := by
      simp [mid, Config.put, Function.update_of_ne hj]
    by_cases h : s = x
    · subst x
      rw [ite_eq_left rfl] at test
      exact ⟨2, _, by simp, by simp [dispatchSteps], .tick load (.tick test (.nil _)),
        rfl, keep, rfl, rfl⟩
    · have ne : M.publicData (P.port s) ≠ M.publicData (P.port x) := inj.ne h
      rw [ite_eq_right ne] at test
      obtain ⟨n, d, bound, ticks, pre, pc, other, mem, per⟩ := ih hl.2.2
        ((List.mem_cons.mp member).resolve_left h) {mid with pc := P.first xs} rfl
        ((keep _ (by simp)).trans hs)
      refine ⟨2 + n, d, by simp; omega, by simp [dispatchSteps, h, ticks], ?_, pc,
        fun j hj ↦ (other j hj).trans (keep j hj), mem, per⟩
      rw [List.replicate_add]
      exact .tick load (.tick test pre)

/-- Successful dispatch consumes at most two instructions per selector.
The selected row receives the loaded ordinal and the same private memory. -/
theorem dispatch_hit (ss : List S) (hl : P.dispatch M ss)
    (inj : Function.Injective (M.publicData ∘ P.port)) (s : S) (member : s ∈ ss)
    (c : Config w p r) (hc : c.pc = P.first ss) (hs : c.reg (P.reg 4) = M.publicData (P.port s)) :
    ∃ n d, n ≤ 2 * ss.length ∧ Prefix M c (List.replicate n .tick) d ∧ d.pc = P.rowPC s ∧
      (∀ j, j ≠ P.reg 5 → d.reg j = c.reg j) ∧
      d.privateMem = c.privateMem ∧ d.persistent = c.persistent := by
  obtain ⟨n, d, bound, _, rest⟩ := dispatch_hit_exact ss hl inj s member c hc hs
  exact ⟨n, d, bound, rest⟩

/-- Controller instructions change four registers and may store in the
label array. A row invariant stable under these changes can include all
resident input bits, base addresses, and current demand and supply offsets. -/
def Stable (P : Program S p r k) (inv : ℕ → Config w p r → Prop) (dest u : ℕ) : Prop :=
  ∀ n c d, inv n c →
    (∀ j, j ≠ P.reg 0 → j ≠ P.reg 2 → j ≠ P.reg 4 → j ≠ P.reg 5 → d.reg j = c.reg j) →
    (∀ a : Word w, a.val < dest ∨ dest + u ≤ a.val → d.privateMem a = c.privateMem a) →
    d.persistent = c.persistent → inv n d

/-- One row contract is discharged by the selected row's own native prefix.
It advances the local offsets and leaves the driver cursor words intact. -/
def RowRuns (P : Program S p r k) (M : Machine w p r k) (θ : Fin u → S)
    (labelWord : Fin u → Word w) (inv : ℕ → Config w p r → Prop) (cap : ℕ) : Prop :=
  ∀ (i : Fin u) c, c.pc = P.rowPC (θ i) → inv i.val c →
    ∃ n d, n ≤ cap ∧ Prefix M c (List.replicate n .tick) d ∧ d.pc = P.pc 2 ∧
      d.reg (P.reg 6) = labelWord i ∧ inv (i.val + 1) d ∧
      (∀ j : Fin 4, d.reg (P.reg (Fin.castLE (by decide) j)) =
        c.reg (P.reg (Fin.castLE (by decide) j))) ∧
      d.privateMem = c.privateMem ∧ d.persistent = c.persistent

/-- A row prefix carrying a further predicate on its actual instruction count. -/
def RowRunsWith (P : Program S p r k) (M : Machine w p r k) (θ : Fin u → S)
    (labelWord : Fin u → Word w) (inv : ℕ → Config w p r → Prop) (cap : ℕ)
    (clock : Fin u → ℕ → Prop) : Prop :=
  ∀ (i : Fin u) c, c.pc = P.rowPC (θ i) → inv i.val c →
    ∃ n d, n ≤ cap ∧ clock i n ∧ Prefix M c (List.replicate n .tick) d ∧ d.pc = P.pc 2 ∧
      d.reg (P.reg 6) = labelWord i ∧ inv (i.val + 1) d ∧
      (∀ j : Fin 4, d.reg (P.reg (Fin.castLE (by decide) j)) =
        c.reg (P.reg (Fin.castLE (by decide) j))) ∧
      d.privateMem = c.privateMem ∧ d.persistent = c.persistent

/-- A ready loop boundary includes all completed labels and all resident
selectors. Unused cells of the output array may hold arbitrary values. -/
structure Ready (P : Program S p r k) (M : Machine w p r k) (θ : Fin u → S)
    (labelWord : Fin u → Word w) (src dest n : ℕ) (c : Config w p r) : Prop where
  pc : c.pc = P.pc 0
  source : c.reg (P.reg 0) = word w (src + n)
  stop : c.reg (P.reg 1) = word w (src + u)
  target : c.reg (P.reg 2) = word w (dest + n)
  one : c.reg (P.reg 3) = 1
  selectors : ∀ i : Fin u, c.privateMem (word w (src + i.val)) = M.publicData (P.port (θ i))
  labels : ∀ i : Fin u, i.val < n → c.privateMem (word w (dest + i.val)) = labelWord i

private theorem step_at (link : P.Linked M) (i : Fin 5) {c : Config w p r} (hc : c.pc = P.pc i) :
    M.program.step c = (P.instruction i).run M.publicData c := by
  simp [Machine.program, hc, link.outer i]

/-- Budget for one loop test, ordinal load, fixed dispatch, selected row,
label store and two cursor increments. -/
def visitCap (P : Program S p r k) (rowCap : ℕ) := 5 + 2 * P.selectors.length + rowCap

/-- The same path returns the label and charges exactly the row's own ticks plus
the comparison-chain ticks and five loop instructions. -/
theorem visitWith (link : P.Linked M) (inj : Function.Injective (M.publicData ∘ P.port))
    (θ : Fin u → S) (member : ∀ i, θ i ∈ P.selectors) (labelWord : Fin u → Word w)
    (inv : ℕ → Config w p r → Prop) (src dest cap : ℕ) (stable : P.Stable inv dest u)
    (clock : Fin u → ℕ → Prop) (row : P.RowRunsWith M θ labelWord inv cap clock)
    (hs : src + u < 2 ^ w) (hd : dest + u < 2 ^ w)
    (sep : src + u ≤ dest ∨ dest + u ≤ src) (i : Fin u) (c : Config w p r)
    (ready : P.Ready M θ labelWord src dest i.val c) (hi : inv i.val c) :
    ∃ n d, n ≤ P.visitCap cap ∧
      (∃ t, clock i t ∧ n = 5 + dispatchSteps P.selectors (θ i) + t) ∧
      Prefix M c (List.replicate n .tick) d ∧
      P.Ready M θ labelWord src dest (i.val + 1) d ∧ inv (i.val + 1) d ∧
      (∀ a : Word w, a ≠ word w (dest + i.val) → d.privateMem a = c.privateMem a) ∧
      d.persistent = c.persistent := by
  have hit := i.isLt
  have ne : c.reg (P.reg 0) ≠ c.reg (P.reg 1) := by
    rw [ready.source, ready.stop]
    intro he
    have hv := congrArg Fin.val he
    rw [val_word (by omega : src + i.val < 2 ^ w), val_word hs] at hv
    omega
  let c₁ := {c with pc := P.pc 1}
  let c₂ := c₁.put (P.first P.selectors) (P.reg 4) (M.publicData (P.port (θ i)))
  have s₀ : M.program.step c = .localStep c₁ := by
    rw [step_at link 0 ready.pc]
    simp [instruction, Instr.run, ne, c₁]
  have s₁ : M.program.step c₁ = .localStep c₂ := by
    rw [step_at link 1 rfl]
    change CallAction.localStep (c₁.put _ _ (c.privateMem (c.reg (P.reg 0)))) = _
    rw [ready.source, ready.selectors i]
  obtain ⟨a, selected, ha, dispatchTicks, dispatchRun, selectedPC, other, sm, sp⟩ :=
    dispatch_hit_exact P.selectors link.table inj (θ i) (member i) c₂ rfl (by simp [c₂])
  have keep (j : Fin r) (h4 : j ≠ P.reg 4) (h5 : j ≠ P.reg 5) : selected.reg j = c.reg j :=
    (other j h5).trans (by simp [c₂, c₁, Config.put, Function.update_of_ne h4])
  have si : inv i.val selected :=
    stable _ c selected hi (fun j _ _ h4 h5 ↦ keep j h4 h5) (fun j _ ↦ congrFun sm j) sp
  obtain ⟨t, returned, bound, rowTicks, run, hr, value, next, controls, rm, rp⟩ :=
    row i selected selectedPC si
  have ctrl (j : Fin 4) : returned.reg (P.reg (Fin.castLE (by decide) j)) =
      c.reg (P.reg (Fin.castLE (by decide) j)) := by
    apply (controls j).trans
    apply keep <;> apply P.reg.injective.ne <;> intro h <;>
      have he := congrArg Fin.val h <;> change j.val = _ at he <;> have := j.isLt <;> omega
  have srcReg : returned.reg (P.reg 0) = word w (src + i.val) := (ctrl 0).trans ready.source
  have dstReg : returned.reg (P.reg 2) = word w (dest + i.val) := (ctrl 2).trans ready.target
  have one : returned.reg (P.reg 3) = 1 := (ctrl 3).trans ready.one
  let stored := returned.store (P.pc 3) (word w (dest + i.val)) (labelWord i)
  let advanced := stored.put (P.pc 4) (P.reg 0) (word w (src + (i.val + 1)))
  let d := advanced.put (P.pc 0) (P.reg 2) (word w (dest + (i.val + 1)))
  have s₂ : M.program.step returned = .localStep stored := by
    rw [step_at link 2 hr]
    change CallAction.localStep (returned.store _ (returned.reg (P.reg 2))
      (returned.reg (P.reg 6))) = _
    rw [dstReg, value]
  have s₃ : M.program.step stored = .localStep advanced := by
    rw [step_at link 3 rfl]
    change CallAction.localStep
      (stored.put _ _ (returned.reg (P.reg 0) + returned.reg (P.reg 3))) = _
    simp [advanced, srcReg, one, word, add_assoc]
  have s₄ : M.program.step advanced = .localStep d := by
    rw [step_at link 4 rfl]
    change CallAction.localStep (advanced.put _ _
      (advanced.reg (P.reg 2) + advanced.reg (P.reg 3))) = _
    simp [d, advanced, stored, Config.put, Config.store, dstReg, one, word, add_assoc]
  have tail : Prefix M returned (List.replicate 3 .tick) d :=
    .tick s₂ (.tick s₃ (.tick s₄ (.nil _)))
  have keep' (j : Fin r) (h0 : j ≠ P.reg 0) (h2 : j ≠ P.reg 2) : d.reg j = returned.reg j := by
    simp [d, advanced, stored, Config.put, Config.store, Function.update_of_ne h0,
      Function.update_of_ne h2]
  have unchanged (j : Word w) (h : j ≠ word w (dest + i.val)) :
      d.privateMem j = returned.privateMem j :=
    Config.store_other returned (P.pc 3) (word w (dest + i.val)) j (labelWord i) h
  have away (j : Word w) (h : j ≠ word w (dest + i.val)) : d.privateMem j = c.privateMem j :=
    (unchanged j h).trans ((congrFun rm j).trans (congrFun sm j))
  have exactDest := val_word (by omega : dest + i.val < 2 ^ w)
  refine ⟨2 + a + t + 3, d, by unfold visitCap; omega, ⟨t, rowTicks, by omega⟩,
    ?_, ?_, ?_, away, rp.trans sp⟩
  · simp only [List.replicate_add]
    exact ((Prefix.tick s₀ (.tick s₁ dispatchRun)).append run).append tail
  · refine ⟨rfl, by simp [d, advanced, Config.put],
      (keep' _ (by simp) (by simp)).trans ((ctrl 1).trans ready.stop),
      by simp [d], (keep' _ (by simp) (by simp)).trans one, ?_, ?_⟩
    · intro j
      have hv := j.isLt
      apply (away _ ?_).trans (ready.selectors j)
      intro h
      have hh := congrArg Fin.val h
      rw [val_word (by omega : src + j.val < 2 ^ w), exactDest] at hh
      omega
    · intro j hj
      by_cases he : j = i
      · subst j; exact Config.store_same returned (P.pc 3) _ _
      · apply (away _ ?_).trans (ready.labels j (by have h := Fin.val_ne_of_ne he; omega))
        intro h
        have hh := congrArg Fin.val h
        rw [val_word (by have := j.isLt; omega : dest + j.val < 2 ^ w), exactDest] at hh
        exact he (Fin.ext (Nat.add_left_cancel hh))
  · refine stable _ returned d next (fun j h0 h2 _ _ ↦ keep' j h0 h2) (fun j hj ↦ ?_) rfl
    apply unchanged
    intro he
    have hh := congrArg Fin.val he
    rw [exactDest] at hh
    omega

private theorem visit (link : P.Linked M) (inj : Function.Injective (M.publicData ∘ P.port))
    (θ : Fin u → S) (member : ∀ i, θ i ∈ P.selectors) (labelWord : Fin u → Word w)
    (inv : ℕ → Config w p r → Prop) (src dest cap : ℕ) (stable : P.Stable inv dest u)
    (row : P.RowRuns M θ labelWord inv cap) (hs : src + u < 2 ^ w) (hd : dest + u < 2 ^ w)
    (sep : src + u ≤ dest ∨ dest + u ≤ src) (i : Fin u) (c : Config w p r)
    (ready : P.Ready M θ labelWord src dest i.val c) (hi : inv i.val c) :
    ∃ n d, n ≤ P.visitCap cap ∧ Prefix M c (List.replicate n .tick) d ∧
      P.Ready M θ labelWord src dest (i.val + 1) d ∧ inv (i.val + 1) d ∧
      (∀ a : Word w, a ≠ word w (dest + i.val) → d.privateMem a = c.privateMem a) ∧
      d.persistent = c.persistent := by
  have r : P.RowRunsWith M θ labelWord inv cap (fun _ _ ↦ True) := by
    intro j q hq hv
    obtain ⟨n, d, bound, post⟩ := row j q hq hv
    exact ⟨n, d, bound, trivial, post⟩
  obtain ⟨n, d, bound, _, post⟩ := visitWith link inj θ member labelWord inv src dest cap stable
    (fun _ _ ↦ True) r hs hd sep i c ready hi
  exact ⟨n, d, bound, post⟩

/-- Repeat actual selected row calls in input order. Every written label is
already available at the next copy boundary, and the next row receives the
updated offset invariant. -/
theorem visits (link : P.Linked M) (inj : Function.Injective (M.publicData ∘ P.port))
    (θ : Fin u → S) (member : ∀ i, θ i ∈ P.selectors) (labelWord : Fin u → Word w)
    (inv : ℕ → Config w p r → Prop) (src dest cap : ℕ) (stable : P.Stable inv dest u)
    (row : P.RowRuns M θ labelWord inv cap) (hs : src + u < 2 ^ w) (hd : dest + u < 2 ^ w)
    (sep : src + u ≤ dest ∨ dest + u ≤ src) (c : Config w p r)
    (ready : P.Ready M θ labelWord src dest 0 c) (h0 : inv 0 c) (n : ℕ) (hn : n ≤ u) :
    ∃ ticks d, ticks ≤ P.visitCap cap * n ∧ Prefix M c (List.replicate ticks .tick) d ∧
      P.Ready M θ labelWord src dest n d ∧ inv n d ∧
      (∀ a : Word w, a.val < dest ∨ dest + n ≤ a.val → d.privateMem a = c.privateMem a) ∧
      d.persistent = c.persistent := by
  induction n with
  | zero => exact ⟨0, c, by simp, .nil _, ready, h0, fun _ _ ↦ rfl, rfl⟩
  | succ n ih =>
    obtain ⟨t, mid, bound, pre, hr, hi, mem, per⟩ := ih (by omega)
    let i : Fin u := ⟨n, hn⟩
    obtain ⟨s, d, budget, tail, hr', hi', hm, hp⟩ :=
      visit link inj θ member labelWord inv src dest cap stable row hs hd sep i mid hr hi
    refine ⟨t + s, d, ?_, ?_, hr', hi', ?_, hp.trans per⟩
    · rw [Nat.mul_succ]
      omega
    · rw [List.replicate_add]
      exact pre.append tail
    · intro a ha
      apply (hm a ?_).trans (mem a (by omega))
      intro he
      have hh := congrArg Fin.val he
      rw [val_word (by change dest + n < 2 ^ w; omega)] at hh
      change a.val = dest + n at hh
      omega

/-- At the final-width checker the label slice is in copy order and the
row invariant has reached its final offsets. This includes the zero-copy
case, which executes exactly the loop's final test. -/
theorem native (link : P.Linked M) (inj : Function.Injective (M.publicData ∘ P.port))
    (θ : Fin u → S) (member : ∀ i, θ i ∈ P.selectors) (labelWord : Fin u → Word w)
    (inv : ℕ → Config w p r → Prop) (src dest cap : ℕ) (stable : P.Stable inv dest u)
    (row : P.RowRuns M θ labelWord inv cap) (hs : src + u < 2 ^ w) (hd : dest + u < 2 ^ w)
    (sep : src + u ≤ dest ∨ dest + u ≤ src) (c : Config w p r)
    (ready : P.Ready M θ labelWord src dest 0 c) (h0 : inv 0 c) :
    ∃ ticks d, ticks ≤ P.visitCap cap * u + 1 ∧ Prefix M c (List.replicate ticks .tick) d ∧
      d.pc = P.checkWidths ∧ inv u d ∧
      (∀ i : Fin u, d.privateMem (word w (dest + i.val)) = labelWord i) ∧
      (∀ a : Word w, a.val < dest ∨ dest + u ≤ a.val → d.privateMem a = c.privateMem a) ∧
      d.persistent = c.persistent := by
  obtain ⟨t, m, bound, pre, hr, hi, hm, hp⟩ :=
    visits link inj θ member labelWord inv src dest cap stable row hs hd sep c ready h0 u le_rfl
  let d := {m with pc := P.checkWidths}
  have eq : m.reg (P.reg 0) = m.reg (P.reg 1) := hr.source.trans hr.stop.symm
  have stop : M.program.step m = .localStep d := by
    rw [step_at link 0 hr.pc]
    simp [instruction, Instr.run, eq, d]
  refine ⟨t + 1, d, Nat.add_le_add_right bound _, ?_, rfl, ?_, fun i ↦ hr.labels i i.isLt, hm, hp⟩
  · rw [List.replicate_add]
    exact pre.append (.tick stop (.nil _))
  · exact stable _ m d hi (fun _ _ _ _ _ ↦ rfl) (fun _ _ ↦ rfl) rfl

end Program
end PairSimulation.MapDriver

end VPVNP
end Computability
end OAI
