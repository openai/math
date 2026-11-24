import OAI.Computability.VPVNP.PairNodeChildLoop
import OAI.Computability.VPVNP.PairSimulationResidentMapDispatch
import OAI.Computability.VPVNP.RAMProcessorReportPrefix

/-!
# Visiting a selected node's resident map entries

The loop tests the private row cursor against its exclusive end, enters the
resident entry routine, and advances the cursor only on success. Histograms
retain the increments of all earlier successful entries when a later map is
syntactically zero. Neither the directory order nor repeated names are deduplicated.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ResidentMapLoop

open BurstRAM BurstRAM.PrivateRAM NodeArguments.ChildScan
open scoped Fin.CommRing
open private ReadPrefix ReadPrefix.tick ReadPrefix.nil ReadPrefix.execute
  from OAI.Computability.VPVNP.PairSimulationPrivateSlices

variable {w p r k t : ℕ}

/-- The value of one occurrence may be zero. The two bounds include directory
reads, operand preparation, matrix dispatch, and the private parameter scan. -/
structure Job (t : ℕ) where
  /-- Parameter labels emitted by the map, or `none` if it rejects. -/
  names : Option (List (Fin t))
  /-- Bound on events in the descriptor read and map execution. -/
  work : ℕ
  /-- Bound on probes in the descriptor read and map execution. -/
  probes : ℕ

/-- Concatenate the labels of successive jobs up to the first failure, retaining multiplicities. -/
def labels : List (Job t) → List (Fin t)
  | [] => []
  | j :: js => j.names.elim [] (fun names ↦ names ++ labels js)

/-- Whether every job returned a list of labels. -/
def passed (js : List (Job t)) : Bool := js.all fun j ↦ j.names.isSome

/-- Event bound charging a test and an advance per job, plus the final test. -/
def work (js : List (Job t)) : ℕ := (js.map fun j ↦ 2 + j.work).sum + 1

/-- Sum of the probe bounds for the individual jobs. -/
def probes (js : List (Job t)) : ℕ := (js.map Job.probes).sum

/-- The item starts at its genuine descriptor-reader entry. The returning
map takes the increment row; unsuccessful map images enter their rejecting halt. -/
structure Program (p r : ℕ) where
  /-- Address of the test for the end of the directory slice. -/
  test : Fin p
  /-- Address of the cursor increment after a successful item. -/
  advance : Fin p
  /-- Entry address of the current item's descriptor reader. -/
  item : Fin p
  /-- Continuation reached when the cursor equals the exclusive end. -/
  done : Fin p
  /-- Register holding the current directory row. -/
  cursor : Fin r
  /-- Register holding the exclusive end of the directory slice. -/
  stop : Fin r
  /-- Register supplying one for cursor increments. -/
  one : Fin r
  stopApart : stop ≠ cursor
  oneApart : one ≠ cursor

namespace Program

variable (P : Program p r)

/-- Test the cursor against its exclusive end (`false`) or advance it and retest (`true`). -/
def control : Bool → Instr w p r k
  | false => .jumpEq P.cursor P.stop P.done P.item
  | true => .binary .add P.cursor P.cursor P.one P.test

/-- The machine contains the cursor test and advance instructions at the loop addresses. -/
structure Linked (M : Machine w p r k) : Prop where
  test : M.code P.test = P.control false
  advance : M.code P.advance = P.control true

/-- Scratch facts for the remaining operands survive the two loop rows. -/
def Stable (inv : Config w p r → Prop) : Prop :=
  ∀ c d, inv c → (∀ q, q ≠ P.cursor → d.reg q = c.reg q) →
    d.privateMem = c.privateMem → d.persistent = c.persistent → inv d

/-- An item reader and map body at its real directory position. The accepted
result and all future operand buffers can depend on the supplied half-wires. -/
def Item (M : Machine w p r k) (m : Memory w) (inv : Config w p r → Prop)
    (hist : Fin t → Word w) (src : ℕ) (j : Job t) : Prop :=
  ∀ c, c.pc = P.item → c.reg P.cursor = (src : Word w) → inv c →
    ∃ d es, Prefix M m c d [] es ∧ es.length ≤ j.work ∧ countProbes es ≤ j.probes ∧
      choiceBits es = [] ∧ (if j.names.isSome then d.pc = P.advance else M.code d.pc = .reject) ∧
      inv d ∧ d.reg P.cursor = c.reg P.cursor ∧ d.reg P.stop = c.reg P.stop ∧
      d.reg P.one = c.reg P.one ∧ d.persistent = c.persistent ∧
      ∀ l, d.privateMem (hist l) = c.privateMem (hist l) + ((j.names.getD []).count l : Word w)

/-- Every source position receives its own callback; a repeated local matrix
and a repeated output label retain their separate occurrences. -/
def Items (M : Machine w p r k) (m : Memory w) (inv : Config w p r → Prop)
    (hist : Fin t → Word w) : ℕ → List (Job t) → Prop
  | _, [] => True
  | src, j :: js => P.Item M m inv hist src j ∧ Items M m inv hist (src + 1) js

private theorem tick {M : Machine w p r k} (m : Memory w) {c d : Config w p r}
    (h : M.program.step c = .localStep d) : Prefix M m c d [] [.tick] :=
  fun fuel bs ↦ ReadPrefix.execute (ReadPrefix.tick h (ReadPrefix.nil _)) fuel bs

/-- Run the actual loop, retaining the exact prefix of successful parameter
labels on every rejecting branch. The bounds also hold when the first entry fails. -/
theorem native (M : Machine w p r k) (m : Memory w) (link : P.Linked M)
    (inv : Config w p r → Prop) (stable : P.Stable inv) (hist : Fin t → Word w)
    (js : List (Job t)) (src : ℕ) (items : P.Items M m inv hist src js)
    (fit : src + js.length < 2 ^ w)
    (c : Config w p r) (pc : c.pc = P.test) (cursor : c.reg P.cursor = (src : Word w))
    (stop : c.reg P.stop = ((src + js.length : ℕ) : Word w)) (one : c.reg P.one = 1) (hi : inv c) :
    ∃ d es, Prefix M m c d [] es ∧ es.length ≤ work js ∧ countProbes es ≤ probes js ∧
      choiceBits es = [] ∧ (if passed js then d.pc = P.done else M.code d.pc = .reject) ∧ inv d ∧
      d.persistent = c.persistent ∧ ∀ l, d.privateMem (hist l) = c.privateMem (hist l) +
        ((labels js).count l : Word w) := by
  induction js generalizing c src with
  | nil =>
    let d := {c with pc := P.done}
    have step : M.program.step c = .localStep d := by
      rw [show M.program.step c = (M.code c.pc).run M.publicData c from rfl, pc, link.test]
      simp [control, Instr.run, cursor, stop, d]
    exact ⟨d, [.tick], tick m step, by simp [work], by simp [probes, countProbes], rfl, rfl,
      stable c d hi (fun _ _ ↦ rfl) rfl rfl, rfl, fun _ ↦ by simp [labels, d]⟩
  | cons j js ih =>
    let a := {c with pc := P.item}
    have ne : c.reg P.cursor ≠ c.reg P.stop := by
      rw [cursor, stop]
      intro eq
      have e := congrArg Fin.val eq
      change src % (2 ^ w) = (src + (j :: js).length) % (2 ^ w) at e
      rw [Nat.mod_eq_of_lt (by simp at fit; omega), Nat.mod_eq_of_lt fit] at e
      simp at e
    have step : M.program.step c = .localStep a := by
      rw [show M.program.step c = (M.code c.pc).run M.publicData c from rfl, pc, link.test]
      simp [control, Instr.run, ne, a]
    have first := tick m step
    obtain ⟨mid, es, path, len, probe, choices, hmid, him, cs, st, one', per, hs⟩ :=
      items.1 a rfl cursor (stable c a hi (fun _ _ ↦ rfl) rfl rfl)
    cases names : j.names with
    | none =>
      have endPC : M.code mid.pc = .reject := by simpa [names] using hmid
      refine ⟨mid, [Event.tick] ++ es, first.trans path, ?_, ?_, ?_, ?_, him, per, ?_⟩
      · simp [work]; omega
      · simpa [probes, countProbes] using probe.trans (Nat.le_add_right _ _)
      · simpa [choiceBits] using choices
      · simpa [passed, names] using endPC
      · simpa [labels, names, a] using hs
    | some ls =>
      have hp : mid.pc = P.advance := by simpa [names] using hmid
      let b := mid.put P.test P.cursor ((src + 1 : ℕ) : Word w)
      have add : M.program.step mid = .localStep b := by
        rw [show M.program.step mid = (M.code mid.pc).run M.publicData mid from rfl, hp,
          link.advance]
        change CallAction.localStep (mid.put P.test P.cursor (mid.reg P.cursor + mid.reg P.one)) = _
        rw [cs, one', show a.reg P.cursor = (src : Word w) from cursor,
          show a.reg P.one = 1 from one]
        simp [b]
      have keep (q) (hq : q ≠ P.cursor) : b.reg q = mid.reg q := by
        simp [b, Config.put, Function.update_of_ne hq]
      have lenEq : src + 1 + js.length = src + (j :: js).length := by simp; omega
      obtain ⟨out, tail, run, hlen, hprobe, hchoices, hpc, hout, hper, hhist⟩ :=
        ih (src + 1) items.2 (lenEq ▸ fit) b rfl (Config.put_same ..)
          ((keep P.stop P.stopApart).trans (st.trans (lenEq ▸ stop)))
          ((keep P.one P.oneApart).trans (one'.trans one)) (stable mid b him keep rfl rfl)
      let events := (([.tick] ++ es) ++ [.tick]) ++ tail
      refine ⟨out, events, ((first.trans path).trans (tick m add)).trans run, ?_, ?_, ?_, ?_, hout,
        hper.trans per, ?_⟩
      · simp only [events, work, List.length_append, List.length_cons, List.length_nil,
          List.map_cons, List.sum_cons] at hlen ⊢
        omega
      · simp only [events, countProbes_append, countProbes, probes, List.map_cons, List.sum_cons,
          Nat.zero_add, Nat.add_zero] at hprobe ⊢
        exact Nat.add_le_add probe hprobe
      · simp [events, PrimedInputRAM.Flow.choiceBits_append, choiceBits, choices, hchoices]
      · simpa [passed, names] using hpc
      · intro l
        rw [hhist]
        change mid.privateMem (hist l) + _ = _
        rw [hs l]
        simp [labels, names, a, add_assoc]

end Program
end PairSimulation.ResidentMapLoop

end VPVNP
end Computability
end OAI
