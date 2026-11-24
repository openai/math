import OAI.Computability.VPVNP.NetworkKernel
import OAI.Computability.VPVNP.PrimedInputRAMChoices
import OAI.Computability.VPVNP.PrimedInputRAMHeaders
import OAI.Computability.VPVNP.RAMChain
import OAI.Computability.VPVNP.RAMRecords
import OAI.Computability.VPVNP.RAMUniform
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.Defs

/-!
# Native scan of the final arc bits

After the compression descriptors have supplied the total width, the burst
starts at the exclusive upper address of the final bit array. Each data call
decrements this cursor, makes one binary choice, writes its value at the new
cursor and returns that cursor. The lower address is fixed public data, so
the same instruction table works for every selection of compression terms.
The reads at the two incident positions use the same prefix-sum address.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.FinalBits

open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM
open scoped Fin.CommRing

/-- The two registers hold the cursor and a temporary word. The data calls
return to the dispatcher. At the lower address the fragment jumps to its
continuation without making a choice or accessing external memory. -/
def instruction {p r k : ℕ} (w : ℕ) (pc : Fin 10 → Fin p)
    (reg : Fin 2 ↪ Fin r) (base : Fin k) (done : Fin p) : Fin 10 → Instr w p r k :=
  ![.stateWord (reg 0) (pc 1), .publicWord (reg 1) base (pc 2),
    .jumpEq (reg 0) (reg 1) done (pc 3), .constant (reg 1) 1 (pc 4),
    .binary .sub (reg 0) (reg 0) (reg 1) (pc 5), .choose (pc 6) (pc 7),
    .constant (reg 1) 1 (pc 8), .constant (reg 1) 0 (pc 8),
    .writeExternal (reg 0) (reg 1) (pc 9), .returnState (reg 0)]

/-- The ten scan instructions occupy their designated labels in the host machine. -/
def Linked {w p r k : ℕ} (M : Machine w p r k) (pc : Fin 10 → Fin p)
    (reg : Fin 2 ↪ Fin r) (base : Fin k) (done : Fin p) : Prop :=
  ∀ i, M.code (pc i) = instruction w pc reg base done i

variable {w p r k : ℕ} {M : Machine w p r k} {pc : Fin 10 → Fin p}
  {reg : Fin 2 ↪ Fin r} {base : Fin k} {done : Fin p}

/-- Report of one bit call. -/
def bitReport (a : Word w) (b : Bool) : Report w :=
  ⟨[.tick, .tick, .tick, .tick, .tick, .choice b, .tick, .write a (encodeBit w b)], some a⟩

@[simp] theorem bitReport_probes (a : Word w) (b : Bool) : (bitReport a b).probes = 1 := rfl

@[simp] theorem bitReport_result (a : Word w) (b : Bool) : (bitReport a b).result = some a := rfl

@[simp] theorem bitReport_memory (a : Word w) (b : Bool) (m : Memory w) :
    after m (bitReport a b).events = writeMemory m a (encodeBit w b) := rfl

private theorem step_at (hl : Linked M pc reg base done) (i : Fin 10) (c : Config w p r)
    (hc : c.pc = pc i) : M.program.step c = (instruction w pc reg base done i).run M.publicData
      c := by
  simp [Machine.program, hc, hl i]

private def tested (c : Config w p r) (pc : Fin 10 → Fin p)
    (reg : Fin 2 ↪ Fin r) (low : Word w) (target : Fin p) : Config w p r :=
  (c.put (pc 1) (reg 0) c.persistent).put target (reg 1) low

private theorem execute_test (hl : Linked M pc reg base done) (c : Config w p r)
    (hc : c.pc = pc 0) (m : Memory w) (bs : List Bool) (fuel : ℕ) :
    let target := if c.persistent = M.publicData base then done else pc 3
    execute M.program (fuel + 3) c m bs =
      (execute M.program fuel (tested c pc reg (M.publicData base) target) m bs).map
        (fun rep ↦ ⟨[.tick,.tick,.tick] ++ rep.events, rep.result⟩) := by
  let a := c.put (pc 1) (reg 0) c.persistent
  let d := a.put (pc 2) (reg 1) (M.publicData base)
  have s0 : M.program.step c = .localStep a := step_at hl 0 c hc
  have s1 : M.program.step a = .localStep d := step_at hl 1 _ rfl
  have s2 : M.program.step d = .localStep
      (tested c pc reg (M.publicData base) (if c.persistent = M.publicData base then done else pc
        3)) := by
    rw [step_at hl 2 d rfl]
    change CallAction.localStep {d with
      pc := if d.reg (reg 0) = d.reg (reg 1) then done else pc 3} = _
    simp [d, a, Config.put, tested]
  dsimp only
  simp only [execute, s0, s1, s2]
  simp [Option.map_map, Function.comp_def, Report.prepend]

/-- Exact native execution of a data call on *any* supplied branch stream.
Missing or unused bits reject even when the machine has excess fuel. -/
theorem execute_bit (hl : Linked M pc reg base done) (c : Config w p r) (hc : c.pc = pc 0)
    (hs : c.persistent ≠ M.publicData base) (m : Memory w) (bs : List Bool) (extra : ℕ) :
    execute M.program (extra + 9) c m bs =
      match bs with
      | [b] => some (bitReport (c.persistent - 1) b)
      | _ => none := by
  rw [show extra + 9 = (extra + 6) + 3 by omega, execute_test hl c hc]
  simp only [hs, ↓reduceIte]
  let ct := tested c pc reg (M.publicData base) (pc 3)
  let cd := ct.put (pc 4) (reg 1) 1
  let cb := cd.put (pc 5) (reg 0) (c.persistent - 1)
  let choose (b : Bool) := {cb with pc := if b then pc 6 else pc 7}
  let cw (b : Bool) := cb.put (pc 8) (reg 1) (encodeBit w b)
  let cr (b : Bool) := {cw b with pc := pc 9}
  have s3 : M.program.step ct = .localStep cd := step_at hl 3 _ rfl
  have s4 : M.program.step cd = .localStep cb := by
    rw [step_at hl 4 cd rfl]
    change CallAction.localStep (cd.put (pc 5) (reg 0) (cd.reg (reg 0) - cd.reg (reg 1))) = _
    simp [cb, cd, ct, tested, Config.put]
  have s5 : M.program.step cb = .branch choose := step_at hl 5 _ rfl
  have s67 (b : Bool) : M.program.step (choose b) = .localStep (cw b) := by
    cases b with
    | false => exact step_at hl 7 _ rfl
    | true => exact step_at hl 6 _ rfl
  have s8 (b : Bool) : M.program.step (cw b) = .write (c.persistent-1) (encodeBit w b) (cr b) := by
    rw [step_at hl 8 (cw b) rfl]
    change CallAction.write ((cw b).reg (reg 0)) ((cw b).reg (reg 1)) (cr b) = _
    simp [cw, cb, Config.put]
  have s9 (b : Bool) : M.program.step (cr b) = .finish (some (c.persistent - 1)) := by
    rw [step_at hl 9 (cr b) rfl]
    change CallAction.finish (some ((cr b).reg (reg 0))) = _
    simp [cr, cw, cb, Config.put]
  change (execute M.program (extra + 6) ct m bs).map _ = _
  cases bs with
  | nil => simp only [execute, s3, s4, s5, Option.map_none]
  | cons b tail =>
    cases tail <;> simp only [execute, s3, s4, s5, s67, s8, s9] <;> rfl

/-- The lower-bound test composes with arbitrary native continuation code. -/
theorem execute_done (hl : Linked M pc reg base done) (c : Config w p r) (hc : c.pc = pc 0)
    (hs : c.persistent = M.publicData base) (m : Memory w) (bs : List Bool) (fuel : ℕ) :
    let out := (c.put (pc 1) (reg 0) c.persistent).put done (reg 1) (M.publicData base)
    execute M.program (fuel + 3) c m bs = (execute M.program fuel out m bs).map
      (fun rep ↦ ⟨[.tick,.tick,.tick] ++ rep.events, rep.result⟩) := by
  simp [execute_test hl c hc, hs, tested]

/-- Standalone table with an accepting continuation. The ten labels of the
scan are embedded unchanged in this eleven-instruction template. -/
def template : Template 11 2 1 where
  literalWidth := 1
  entry := 0
  code j := if h : j.val < 10 then
    instruction 1 Fin.castSucc (Function.Embedding.refl _) 0 10 ⟨j.val,h⟩
  else .accept

theorem template_linked (pub : Fin 1 → Word w) :
    Linked (template.instantiate w pub) Fin.castSucc (Function.Embedding.refl _) 0 10 := by
  intro i
  fin_cases i <;> rfl

/-- Ascending physical address; the scan visits the addresses in reverse. -/
def cursor (w low n : ℕ) : Word w := ((low + n : ℕ) : Word w)

@[simp] private theorem cursor_pred (low n : ℕ) :
    cursor w low (n+1) - 1 = cursor w low n := by
  simp [cursor, ← Nat.add_assoc]

private theorem cursor_ne {low n : ℕ} (fit : low + (n + 1) < 2 ^ w) :
    cursor w low (n+1) ≠ cursor w low 0 := by
  intro he
  have hv := congrArg Fin.val he
  simp only [cursor, Fin.val_natCast, Nat.add_zero, Nat.mod_eq_of_lt fit,
    Nat.mod_eq_of_lt (show low < 2^w by omega)] at hv
  omega

/-- A successful branch stream for the whole scan, before the continuation. -/
def calls {n : ℕ} (f : Fin n → Bool) : List (List Bool) :=
  (List.ofFn fun i ↦ [f i]).reverse

/-- Exact chronological reports for the choices written in the scan. -/
def reports {n : ℕ} (w low : ℕ) (f : Fin n → Bool) : List (Report w) :=
  (List.ofFn fun i ↦ bitReport (cursor w low i) (f i)).reverse

@[simp] theorem calls_length {n : ℕ} (f : Fin n → Bool) : (calls f).length = n := by simp [calls]

theorem calls_succ {n : ℕ} (f : Fin (n + 1) → Bool) :
    calls f = [f (Fin.last n)] :: calls (Fin.init f) := by
  rw [calls, List.ofFn_succ', List.concat_eq_append, List.reverse_concat']
  rfl

theorem reports_succ {n : ℕ} (low : ℕ) (f : Fin (n + 1) → Bool) :
    reports w low f = bitReport (cursor w low n) (f (Fin.last n)) :: reports w low
      (Fin.init f) := by
  rw [reports, List.ofFn_succ', List.concat_eq_append, List.reverse_concat']
  rfl

private theorem execute_succ (hl : Linked M pc reg base done) (he : M.entry = pc 0)
    (low n : ℕ) (fit : low + (n + 1) < 2 ^ w) (hpub : M.publicData base = cursor w low 0)
    (m : Memory w) (bs : List Bool) (extra : ℕ) :
    execute M.program (extra + 9) (M.program.start (cursor w low (n+1))) m bs =
      match bs with
      | [b] => some (bitReport (cursor w low n) b)
      | _ => none := by
  have hs : cursor w low (n+1) ≠ M.publicData base := hpub ▸ cursor_ne fit
  rw [execute_bit hl _ he hs]
  change (match bs with
    | [b] => some (bitReport (cursor w low (n+1) - 1) b)
    | _ => none) = _
  rw [cursor_pred]

/-- The native scan can be followed by arbitrary further calls. The memory
passed to those calls is the memory obtained by replaying the actual writes. -/
theorem run_scan (hl : Linked M pc reg base done) (he : M.entry = pc 0) (low n : ℕ)
    (fit : low + n < 2 ^ w) (hpub : M.publicData base = cursor w low 0)
    (f : Fin n → Bool) (m : Memory w) (tail : List (List Bool)) (extra : ℕ) :
    runSegment M.program (extra+9) (some (cursor w low n)) m (calls f ++ tail) =
      (runSegment M.program (extra+9) (some (cursor w low 0))
        (after m (eventLog (reports w low f))) tail).map (reports w low f ++ ·) := by
  induction n generalizing m with
  | zero =>
    simp [calls, reports, eventLog, after]
  | succ n ih =>
    rw [calls_succ, reports_succ, List.cons_append, runSegment,
      execute_succ hl he low n fit hpub]
    simp only [bitReport_result, bitReport_memory]
    rw [ih (by omega) (Fin.init f)]
    simp [eventLog, after, Option.map_map, Function.comp_def]
    rfl

/-- For any scan of the prescribed length, success forces one singleton
choice per physical address. This excludes all extra and missing choices. -/
theorem scan_complete (hl : Linked M pc reg base done) (he : M.entry = pc 0) (low n : ℕ)
    (fit : low + n < 2 ^ w) (hpub : M.publicData base = cursor w low 0) (m : Memory w)
    (bs : List (List Bool)) (rs : List (Report w)) (extra : ℕ)
    (hlen : bs.length = n)
    (hr : runSegment M.program (extra + 9) (some (cursor w low n)) m bs = some rs) :
    ∃ f : Fin n → Bool, bs = calls f ∧ rs = reports w low f := by
  induction n generalizing m bs rs with
  | zero =>
    have hb : bs = [] := List.length_eq_zero_iff.mp hlen
    subst bs
    obtain rfl : rs = [] := (Option.some.inj hr).symm
    exact ⟨Fin.elim0, rfl, rfl⟩
  | succ n ih =>
    cases bs with
    | nil => simp at hlen
    | cons head rest =>
      have hlen' : rest.length = n := by simpa using hlen
      rw [runSegment, execute_succ hl he low n fit hpub] at hr
      cases head with
      | nil => contradiction
      | cons b more =>
        cases more with
        | cons => contradiction
        | nil =>
          obtain ⟨ts, ht, rfl⟩ := Option.map_eq_some_iff.mp hr
          obtain ⟨g, rfl, rfl⟩ := ih (by omega) _ _ ts hlen' ht
          refine ⟨Fin.snoc g b, ?_, ?_⟩
          · simp [calls_succ]
          · simp [reports_succ]

theorem calls_injective {n : ℕ} : Function.Injective (@calls n) := by
  intro f g he
  have h := congrArg List.reverse he
  simp only [calls, List.reverse_reverse, List.ofFn_inj] at h
  funext i
  exact (List.cons.inj (congrFun h i)).1

/-- Histories reaching the end of the data phase in exactly the scheduled
number of calls. The subsequent vertex visits supply the continuation. -/
abbrev ScanPaths {C : Type*} (P : Program w C) (fuel low n : ℕ) (m : Memory w) :=
  {bs : List (List Bool) // bs.length = n ∧
    (runSegment P fuel (some (cursor w low n)) m bs).isSome}

/-- Bijective enumeration by native branch paths, including the empty scan. -/
noncomputable def scanEquiv (hl : Linked M pc reg base done) (he : M.entry = pc 0) (low n : ℕ)
    (fit : low + n < 2 ^ w) (hpub : M.publicData base = cursor w low 0) (m : Memory w)
      (extra : ℕ) :
    (Fin n → Bool) ≃ ScanPaths M.program (extra+9) low n m := by
  let path (f : Fin n → Bool) : ScanPaths M.program (extra+9) low n m := ⟨calls f,
    calls_length f, by
    have h := run_scan hl he low n fit hpub f m [] extra
    simpa [runSegment] using congrArg Option.isSome h⟩
  apply Equiv.ofBijective path
  constructor
  · intro f g eq
    exact calls_injective (congrArg Subtype.val eq)
  · rintro ⟨bs,hlen,hs⟩
    obtain ⟨rs,hr⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨f,hf,_⟩ := scan_complete hl he low n fit hpub m bs rs extra hlen hr
    exact ⟨f, Subtype.ext hf.symm⟩

private def stopReport (w : ℕ) : Report w := ⟨[.tick,.tick,.tick], none⟩

private theorem execute_stop (hl : Linked M pc reg base done) (he : M.entry = pc 0)
    (ha : M.code done = .accept) (low : ℕ) (hpub : M.publicData base = cursor w low 0)
    (m : Memory w) (bs : List Bool) (extra : ℕ) :
    execute M.program (extra+9) (M.program.start (cursor w low 0)) m bs =
      if bs = [] then some (stopReport w) else none := by
  rw [show extra+9 = (extra+6)+3 by omega, execute_done hl _ he hpub.symm]
  have hs (c : Config w p r) (hc : c.pc = done) : M.program.step c = .finish none := by
    simp [Machine.program, hc, ha, Instr.run]
  have hfinish (c : Config w p r) (hc : c.pc = done) (fuel : ℕ) :
      execute M.program (fuel+1) c m bs = if bs = [] then some ⟨[],none⟩ else none := by
    simp only [execute, hs c hc]
  rw [hfinish _ rfl]
  cases bs <;> rfl

/-- With an accepting exit, every complete native history consists of the
data choices followed by the deterministic halt call. Here the stream is
unrestricted: reaching acceptance itself forces the number of data calls. -/
theorem accepted_iff (hl : Linked M pc reg base done) (he : M.entry = pc 0)
    (ha : M.code done = .accept) (low n : ℕ) (fit : low + n < 2 ^ w)
    (hpub : M.publicData base = cursor w low 0) (m : Memory w) (bs : List (List Bool)) (extra : ℕ) :
    (∃ rs, runSegment M.program (extra+9) (some (cursor w low n)) m bs = some rs ∧
      endState (some (cursor w low n)) rs = none) ↔ ∃ f : Fin n → Bool, bs = calls f ++ [[]] := by
  constructor
  · rintro ⟨rs, hr, hend⟩
    induction n generalizing m bs rs with
    | zero =>
      cases bs with
      | nil => obtain rfl : rs = [] := (Option.some.inj hr).symm; contradiction
      | cons b rest =>
        rw [runSegment, execute_stop hl he ha low hpub] at hr
        cases b with
        | cons => contradiction
        | nil =>
          cases rest with
          | nil => exact ⟨Fin.elim0, rfl⟩
          | cons => contradiction
    | succ n ih =>
      cases bs with
      | nil => obtain rfl : rs = [] := (Option.some.inj hr).symm; contradiction
      | cons b rest =>
        rw [runSegment, execute_succ hl he low n fit hpub] at hr
        cases b with
        | nil => contradiction
        | cons v vs =>
          cases vs with
          | cons => contradiction
          | nil =>
            obtain ⟨ts,ht,rfl⟩ := Option.map_eq_some_iff.mp hr
            obtain ⟨g,rfl⟩ := ih (by omega) _ _ ts ht hend
            exact ⟨Fin.snoc g v, by simp [calls_succ]⟩
  · rintro ⟨f,rfl⟩
    refine ⟨reports w low f ++ [stopReport w], ?_, ?_⟩
    · rw [run_scan hl he low n fit hpub, runSegment, execute_stop hl he ha low hpub]
      rfl
    · rw [endState_append]
      rfl

/-- Exactly one call and one external write per physical bit. -/
theorem scan_cost (low n : ℕ) (f : Fin n → Bool) :
    (reports w low f).length = n ∧ RAMBuckets.cost Report.probes (reports w low f) = 2*n := by
  constructor
  · simp [reports]
  · induction n with
    | zero => rfl
    | succ n ih =>
      rw [reports_succ, RAMBuckets.cost, bitReport_probes, ih]
      omega

private theorem replay_store {n : ℕ} (low : ℕ) (fit : low + n < 2 ^ w)
    (f : Fin n → Bool) (m : Memory w) (cells : List (Fin n)) :
    after m (eventLog (cells.map fun (i : Fin n) ↦ bitReport (cursor w low i) (f i))) =
      store (scratchAddress low fit.le) (encodeBit w ∘ f) cells m := by
  induction cells generalizing m with
  | nil => rfl
  | cons i cells ih =>
    have he : cursor w low i = scratchAddress low fit.le i := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt ((Nat.add_lt_add_left i.isLt low).trans fit)
    simp only [List.map_cons, eventLog, List.flatMap_cons, store]
    rw [show ∀ es tail, after m (es ++ tail) = after (after m es) tail by simp [after]]
    rw [bitReport_memory]
    exact (ih _).trans (by rw [he]; rfl)

private theorem after_reports {n : ℕ} (low : ℕ) (fit : low + n < 2 ^ w)
    (f : Fin n → Bool) (m : Memory w) :
    after m (eventLog (reports w low f)) =
      store (scratchAddress low fit.le) (encodeBit w ∘ f) (List.finRange n).reverse m := by
  rw [reports, List.ofFn_eq_map, ← List.map_reverse]
  exact replay_store low fit f m _

/-- The physical cell at every address receives the unique bit chosen there. -/
theorem readback {n : ℕ} (low : ℕ) (fit : low + n < 2 ^ w)
    (f : Fin n → Bool) (m : Memory w) (i : Fin n) :
    after m (eventLog (reports w low f)) (low+i) = encodeBit w (f i) := by
  rw [after_reports low fit]
  exact store_at _ _ _ _ (by simp : i ∈ (List.finRange n).reverse)

/-- All cells outside the scanned interval retain their previous contents. -/
theorem outside {n : ℕ} (low : ℕ) (fit : low + n < 2 ^ w) (f : Fin n → Bool)
    (m : Memory w) (a : ℕ) (ha : a < low ∨ low + n ≤ a) :
    after m (eventLog (reports w low f)) a = m a := by
  rw [after_reports low fit]
  apply store_outside
  intro i _
  have := i.isLt
  change a ≠ low+i.val
  omega

variable {E : ℕ} (width : Fin E → ℕ)

/-- Edge number and offset address a single contiguous bit array. -/
def index (e : Fin E) (j : Fin (width e)) : Fin (∑ e, width e) :=
  finSigmaFinEquiv ⟨e,j⟩

theorem index_val (e : Fin E) (j : Fin (width e)) :
    (index width e j).val = (∑ i : Fin e, width (Fin.castLE e.isLt.le i)) + j :=
  finSigmaFinEquiv_apply _

/-- Splitting the scan into its arc words, including the unique empty word
for every zero-width arc. -/
def arcWords : (Fin (∑ e, width e) → Bool) ≃ ((e : Fin E) → Fin (width e) → Bool) where
  toFun f e j := f (index width e j)
  invFun z i :=
    let p := (finSigmaFinEquiv (n := width)).symm i
    z p.1 p.2
  left_inv f := by funext i; simp [index]
  right_inv z := by
    funext e j
    exact congrArg (fun p : (e : Fin E) × Fin (width e) ↦ z p.1 p.2)
      ((finSigmaFinEquiv (n := width)).symm_apply_apply ⟨e,j⟩)

variable (N : NetworkKernel.Network) (number : N.Edge ≃ Fin E)
  (encode : ∀ e, N.Payload e ≃ (Fin (width (number e)) → Bool))

/-- A scan assignment is precisely a payload assignment to the edges of the
network in the contraction formula. Parallel arcs keep distinct numbers. -/
def payloads : (Fin (∑ e, width e) → Bool) ≃ ((e : N.Edge) → N.Payload e) :=
  (arcWords width).trans ((Equiv.piCongrLeft' (fun e ↦ Fin (width e) → Bool) number.symm).trans
    (Equiv.piCongrRight fun e ↦ (encode e).symm))

@[simp] theorem payloads_bit (f : Fin (∑ e, width e) → Bool) (e : N.Edge) (j : Fin (width
    (number e))) :
    encode e (payloads width N number encode f e) j = f (index width (number e) j) := by
  change encode e ((encode e).symm _) j = _
  rw [Equiv.apply_symm_apply]
  rfl

/-- Both incident payloads in equation (7.1) read the stored bit, even for
loops or multiple edges with identical endpoints. -/
theorem endpoint_bits (low : ℕ) (fit : low + ∑ e, width e < 2 ^ w)
    (f : Fin (∑ e, width e) → Bool) (m : Memory w) (e : N.Edge) (j : Fin (width (number e))) :
    let halves := WireTensor.edgeAssignment N.src N.dst (payloads width N number encode f)
    let cell := after m (eventLog (reports w low f)) (low + (index width (number e) j).val)
    cell = encodeBit w (encode e ((halves (N.src e)).1 e rfl) j) ∧
      cell = encodeBit w (encode e ((halves (N.dst e)).2 e rfl) j) := by
  simp [WireTensor.edgeAssignment, readback low fit]

/-- The two reads may belong to different vertex calls. From either read
label the interpreter passes precisely the incident value to its private
destination register, preserves external memory and consumes no choice. -/
theorem execute_endpoint_read (low : ℕ) (fit : low + ∑ e, width e < 2 ^ w)
    (f : Fin (∑ e, width e) → Bool) (m : Memory w) (e : N.Edge) (j : Fin (width (number e)))
    (c : Config w p r) (dst addr : Fin r) (next : Fin p)
    (hread : M.code c.pc = .readExternal dst addr next)
    (haddr : (c.reg addr).val = low + (index width (number e) j).val)
    (bits : List Bool) (fuel : ℕ) :
    let mem := after m (eventLog (reports w low f))
    let val := encodeBit w (encode e (payloads width N number encode f e) j)
    execute M.program (fuel+1) c mem bits =
      (execute M.program fuel (c.put next dst val) mem bits).map (Report.prepend (.read
        (c.reg addr) val)) := by
  dsimp only
  simp only [execute, M.step_read c hread, haddr, readback low fit, payloads_bit]

/-- For the actual fixed template, the independent summation indices of the
network biject onto the native scan histories. -/
noncomputable def networkScanEquiv (low : ℕ) (fit : low + ∑ e, width e < 2 ^ w)
    (m : Memory w) (extra : ℕ) :
    ((e : N.Edge) → N.Payload e) ≃
      ScanPaths (template.instantiate w (fun _ ↦ cursor w low 0)).program
        (extra+9) low (∑ e, width e) m :=
  (payloads width N number encode).symm.trans
    (scanEquiv (template_linked _) rfl low _ fit rfl m extra)

/-- Complete accepting paths of the standalone table enumerate each network
summand exactly once, with no restriction on the proposed history length. -/
noncomputable def acceptedNetworkEquiv (low : ℕ) (fit : low + ∑ e, width e < 2 ^ w)
    (m : Memory w) (extra : ℕ) :
    ((e : N.Edge) → N.Payload e) ≃
      ActualPaths (template.instantiate w (fun _ ↦ cursor w low 0)).program
        (extra+9) (cursor w low (∑ e, width e)) m (fun _ ↦ True) := by
  apply (payloads width N number encode).symm.trans
  let T := template.instantiate w (fun _ ↦ cursor w low 0)
  have accepted := accepted_iff (template_linked (fun _ ↦ cursor w low 0)) rfl rfl
    low _ fit rfl m
  let path (f : Fin (∑ e, width e) → Bool) :
      ActualPaths T.program (extra+9) (cursor w low (∑ e, width e)) m (fun _ ↦ True) :=
    ⟨calls f ++ [[]], by
      obtain ⟨rs,hr,he⟩ := (accepted _ extra).mpr ⟨f,rfl⟩
      exact ⟨rs,hr,he,trivial⟩⟩
  apply Equiv.ofBijective path
  constructor
  · intro f g h
    exact calls_injective (List.append_cancel_right (congrArg Subtype.val h))
  · rintro ⟨bs,rs,hr,he,_⟩
    obtain ⟨f,hf⟩ := (accepted bs extra).mp ⟨rs,hr,he⟩
    exact ⟨f, Subtype.ext hf.symm⟩

end PairSimulation.FinalBits

end VPVNP
end Computability
end OAI
