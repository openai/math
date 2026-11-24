import OAI.Computability.VPVNP.PairSimulationResidentMapLoop
import OAI.Computability.VPVNP.PairShrinkRoleStages

/-!
# Exact parsing of a resident map loop

Each map acts on the scratch left by its predecessors. A failed entry
rejects the burst at that occurrence. The native guard and advance rows
consume no choices and execute at their actual cursor addresses.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ResidentMapLoop.Exact

open BurstRAM BurstRAM.PrivateRAM DFS ShrinkRole NodeArguments.ChildScan
open scoped Fin.CommRing
open private Program.tick from OAI.Computability.VPVNP.PairSimulationResidentMapLoop

variable {w endAddr p r k : ℕ}

/-- Deterministic evaluation of one selected occurrence on the actual scratch. -/
abbrev Action (w endAddr : ℕ) :=
  Word w → Scratch w endAddr → Option (List (Event w) × Scratch w endAddr)

/-- Every successful evaluation of this occurrence, on any node and saved scratch, yields a
trace with an empty sequence of choice bits. -/
def NoChoices (j : Action w endAddr) : Prop :=
  ∀ node saved es updated, j node saved = some (es, updated) → choiceBits es = []

/-- Trace and scratch of the linked test, occurrence, advance and remaining entries. -/
def scan (node : Word w) : List (Action w endAddr) → Scratch w endAddr →
    Option (List (Event w) × Scratch w endAddr)
  | [], s => some ([.tick], s)
  | j :: js, s =>
    match j node s with
    | none => none
    | some (es, mid) =>
      match scan node js mid with
      | none => none
      | some (tail, out) => some ((([.tick] ++ es) ++ [.tick]) ++ tail, out)

/-- Run the resident occurrences on successive scratch states as a shrink-role reader. Success
returns their scan trace and final scratch with the entire choice tape as the remainder. -/
def mapReader (js : List (Action w endAddr)) : Reader w endAddr Unit := fun node saved bs =>
  (scan node js saved).map fun (es, out) => (⟨(), es, out⟩, bs)

private theorem scan_bits (js : List (Action w endAddr)) (node : Word w)
    (saved : Scratch w endAddr) {es : List (Event w)} {out : Scratch w endAddr}
    (quiet : ∀ j ∈ js, NoChoices j) (got : scan node js saved = some (es, out)) :
    choiceBits es = [] := by
  induction js generalizing saved es out with
  | nil =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj got)
    rfl
  | cons j js ih =>
    cases h : j node saved with
    | none => simp [scan, h] at got
    | some pair =>
      obtain ⟨first, mid⟩ := pair
      cases hr : scan node js mid with
      | none => simp [scan, h, hr] at got
      | some pair =>
        obtain ⟨tail, last⟩ := pair
        simp only [scan, h, hr, Option.some.injEq, Prod.mk.injEq] at got
        rw [← got.1]
        simp only [PrimedInputRAM.Flow.choiceBits_append, choiceBits,
          quiet j List.mem_cons_self node saved first mid h,
          ih mid (fun v hv => quiet v (List.mem_cons_of_mem _ hv)) hr, List.nil_append]

theorem splitBits {js : List (Action w endAddr)} (quiet : ∀ j ∈ js, NoChoices j)
    {node : Word w} {saved : Scratch w endAddr} {bs rest : List Bool}
    {out : Outcome w endAddr Unit} (h : mapReader js node saved bs = some (out, rest)) :
    bs = choiceBits out.trace ++ rest := by
  obtain ⟨⟨es, last⟩, got, eqn⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj eqn
  rw [show choiceBits es = [] from scan_bits js node saved quiet got]
  rfl

variable (P : Program p r) (M : Machine w p r k) (m : Memory w) (dfs : Fin 9 ↪ Fin r)
  (inv : Word w → Config w p r → Prop)

/-- Exact deterministic semantics needed from the descriptor reader and the
selected matrix routine at this one occurrence. -/
structure Item (src : ℕ) (j : Action w endAddr) : Prop where
  noChoices : NoChoices j
  success : ∀ node c es updated, c.pc = P.item → c.reg P.cursor = (src : Word w) → inv node c →
    j node (scratch endAddr c.privateMem) = some (es, updated) →
    ∃ d, d.pc = P.advance ∧ inv node d ∧ d.reg P.cursor = c.reg P.cursor ∧
      d.reg P.stop = c.reg P.stop ∧ d.reg P.one = c.reg P.one ∧ ShrinkRole.Frame dfs endAddr c d ∧
      scratch endAddr d.privateMem = updated ∧ Prefix M m c d [] es
  reject : ∀ node c, c.pc = P.item → c.reg P.cursor = (src : Word w) → inv node c →
    j node (scratch endAddr c.privateMem) = none → ∀ bs, ¬ Returns M c m bs

/-- Exact machine realization of each occurrence in list order at successive cursor positions
starting at `src`, with both successful execution and rejection specified at each position. -/
def Items : ℕ → List (Action w endAddr) → Prop
  | _, [] => True
  | src, j :: js => Item P M m dfs inv src j ∧ Items (src + 1) js

variable {P M m dfs inv} in
theorem Items.quiet {js : List (Action w endAddr)} {src : ℕ}
    (items : Items P M m dfs inv src js) : ∀ j ∈ js, NoChoices j := by
  induction js generalizing src with
  | nil => simp
  | cons j js ih =>
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact items.1.noChoices
    · exact ih items.2 v hv

/-- Configuration at the scan guard with cursor `src`, exclusive end `src + count`, unit
increment and the node's operand invariant. This is the entry condition for realizing the
map reader. -/
structure Entry (src count : ℕ) (node : Word w) (c : Config w p r) : Prop where
  pc : c.pc = P.test
  cursor : c.reg P.cursor = (src : Word w)
  stop : c.reg P.stop = ((src + count : ℕ) : Word w)
  one : c.reg P.one = 1
  ready : inv node c

variable {M m dfs inv}

private theorem native (link : P.Linked M) (stable : ∀ node, P.Stable (inv node))
    (apart : ∀ i : Fin 9, i = 3 ∨ i = 5 ∨ i = 6 ∨ i = 7 → dfs i ≠ P.cursor)
    (js : List (Action w endAddr)) (src : ℕ) (items : Items P M m dfs inv src js)
    (fit : src + js.length < 2 ^ w) (node : Word w) (c : Config w p r)
    (h : Entry P inv src js.length node c) :
    match scan node js (scratch endAddr c.privateMem) with
    | none => ∀ bs, ¬ Returns M c m bs
    | some (es, updated) => ∃ d, d.pc = P.done ∧ inv node d ∧ ShrinkRole.Frame dfs endAddr c d ∧
        scratch endAddr d.privateMem = updated ∧ Prefix M m c d [] es := by
  induction js generalizing src c with
  | nil =>
    let d := {c with pc := P.done}
    have step : M.program.step c = .localStep d := by
      rw [show M.program.step c = (M.code c.pc).run M.publicData c from rfl, h.pc, link.test]
      simp [Program.control, Instr.run, h.cursor, h.stop, d]
    exact ⟨d, rfl, stable node c d h.ready (fun _ _ => rfl) rfl rfl,
      ⟨fun _ _ => rfl, fun _ _ => rfl, rfl⟩, rfl, Program.tick m step⟩
  | cons j js ih =>
    let a := {c with pc := P.item}
    have ne : c.reg P.cursor ≠ c.reg P.stop := by
      rw [h.cursor, h.stop]
      intro eqn
      have e := congrArg Fin.val eqn
      change src % (2 ^ w) = (src + (j :: js).length) % (2 ^ w) at e
      rw [Nat.mod_eq_of_lt ((Nat.le_add_right ..).trans_lt fit), Nat.mod_eq_of_lt fit] at e
      simp at e
    have step : M.program.step c = .localStep a := by
      rw [show M.program.step c = (M.code c.pc).run M.publicData c from rfl, h.pc, link.test]
      simp [Program.control, Instr.run, ne, a]
    have first := Program.tick m step
    have ready := stable node c a h.ready (fun _ _ => rfl) rfl rfl
    cases hj : j node (scratch endAddr c.privateMem) with
    | none =>
      simp only [scan, hj]
      exact fun bs => mt (first.returns bs).mp (items.1.reject node a rfl h.cursor ready hj bs)
    | some pair =>
      obtain ⟨es, updated⟩ := pair
      obtain ⟨mid, pc, ri, cs, st, one, frame, mem, path⟩ :=
        items.1.success node a es updated rfl h.cursor ready hj
      let b := mid.put P.test P.cursor ((src + 1 : ℕ) : Word w)
      have add : M.program.step mid = .localStep b := by
        rw [show M.program.step mid = (M.code mid.pc).run M.publicData mid from rfl,
          pc, link.advance]
        change CallAction.localStep (mid.put P.test P.cursor (mid.reg P.cursor + mid.reg P.one)) = _
        rw [cs, one, show a.reg P.cursor = _ from h.cursor, show a.reg P.one = _ from h.one]
        simp [b]
      have keep (q) (hq : q ≠ P.cursor) : b.reg q = mid.reg q := by
        simp [b, Config.put, Function.update_of_ne hq]
      have len : src + 1 + js.length = src + (j :: js).length := by simp; omega
      have next : Entry P inv (src + 1) js.length node b :=
        ⟨rfl, Config.put_same .., (keep P.stop P.stopApart).trans (st.trans (len ▸ h.stop)),
          (keep P.one P.oneApart).trans (one.trans h.one), stable node mid b ri keep rfl rfl⟩
      have pre := (first.trans path).trans (Program.tick m add)
      have result := ih (src + 1) items.2 (len ▸ fit) b next
      have memory : scratch endAddr b.privateMem = updated := mem
      rw [memory] at result
      cases hr : scan node js updated with
      | none =>
        rw [hr] at result
        simp only [scan, hj, hr]
        exact fun bs => mt (pre.returns bs).mp (result bs)
      | some pair =>
        obtain ⟨tail, last⟩ := pair
        rw [hr] at result
        obtain ⟨d, done, rd, fd, sd, run⟩ := result
        have advance : ShrinkRole.Frame dfs endAddr mid b :=
          ⟨fun i hi => keep _ (apart i hi), fun _ _ => rfl, rfl⟩
        have guard : ShrinkRole.Frame dfs endAddr c a :=
          ⟨fun _ _ => rfl, fun _ _ => rfl, rfl⟩
        simp only [scan, hj, hr]
        exact ⟨d, done, rd, ((guard.trans frame).trans advance).trans fd, sd, pre.trans run⟩

/-- The linked map loop preserves every remaining tape bit. A rejected occurrence
rules out returning from the original guard even when previous maps succeeded. -/
theorem maps_realizes (link : P.Linked M) (stable : ∀ node, P.Stable (inv node))
    (apart : ∀ i : Fin 9, i = 3 ∨ i = 5 ∨ i = 6 ∨ i = 7 → dfs i ≠ P.cursor)
    (js : List (Action w endAddr)) (src : ℕ) (items : Items P M m dfs inv src js)
    (fit : src + js.length < 2 ^ w) :
    Realizes (mapReader js) M m dfs (Entry P inv src js.length)
      (fun _ node d => d.pc = P.done ∧ inv node d) := by
  constructor
  · intro node c bs out rest hc got
    obtain ⟨⟨es, updated⟩, result, eqn⟩ := Option.map_eq_some_iff.mp got
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj eqn
    have h := native P link stable apart js src items fit node c hc
    rw [result] at h
    obtain ⟨d, pc, ready, frame, mem, path⟩ := h
    have quiet := scan_bits js node _ items.quiet result
    exact ⟨by simp [quiet], d, ⟨pc, ready⟩, frame, mem, quiet ▸ path⟩
  · intro node c bs hc bad
    have result := Option.map_eq_none_iff.mp bad
    have h := native P link stable apart js src items fit node c hc
    rw [result] at h
    exact h bs

end PairSimulation.ResidentMapLoop.Exact

end VPVNP
end Computability
end OAI
