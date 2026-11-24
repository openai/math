import OAI.Computability.VPVNP.PairSimulationInlineLiteral
import OAI.Computability.VPVNP.PairSimulationRouteRange
import OAI.Computability.VPVNP.PairNodeChildLoop
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Native dispatch on the producing shrink stage

The preceding level locator supplies the zero-based ordinal of the producing
stage. Each compressor block has `N` shrinking stages followed by a refresh.
This finite program constructs the period `N+1` from zero and one, takes the
native word remainder, and tests the `N` shrink ordinals in sequence.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexStageDispatch

open BurstRAM PrivateRAM PrimedCounter.GuessWord
open scoped Fin.CommRing

variable {N w p r : ℕ}

/-- Instruction labels of the scheduled-stage selector, including ordinal comparison, per-stage
tests, and rejection. -/
abbrev Address (N : ℕ) := Fin (N + 3) ⊕ Fin 3 ⊕ (Fin N × Bool) ⊕ Fin 1

/-- Total number of instructions reserved for selecting among the fixed number of scheduled
stage bodies. -/
def count (N : ℕ) := (N + 3) + (3 + (N * 2 + 1))

/-- The constant loader, three preparation rows, two rows per shrink stage,
and the rejection row occupy consecutive ranges. -/
def address (N : ℕ) : Address N ≃ Fin (count N) :=
  let tests := ((Equiv.refl (Fin N)).prodCongr finTwoEquiv.symm).trans finProdFinEquiv
  let tail := (tests.sumCongr (Equiv.refl (Fin 1))).trans finSumFinEquiv
  let body := ((Equiv.refl (Fin 3)).sumCongr tail).trans finSumFinEquiv
  ((Equiv.refl _).sumCongr body).trans finSumFinEquiv

/-- First instruction label of the stage-selection table. -/
def entry (N : ℕ) := address N (.inl 0)

private abbrev prep (j : Fin 3) : Address N := .inr (.inl j)
private abbrev test (j : Fin N) (b : Bool) : Address N := .inr (.inr (.inl (j,b)))
private abbrev reject : Address N := .inr (.inr (.inr 0))

private def scanAt (j : ℕ) : Address N :=
  if h : j < N then test ⟨j,h⟩ false else reject

private def litPC (pc : Address N → Fin p) : Fin ((N + 1) + 3) → Fin p :=
  Fin.lastCases (pc (prep 0)) (fun j ↦ pc (.inl j))

private def native (W : ℕ) (pc : Address N → Fin p) (scratch : Fin 4 ↪ Fin r)
    (src : Fin r) (jump : Fin N → Fin p) : Address N → Instr W p r 11
  | .inl j => InlinePublic.literalInstruction W (N + 1) (N + 1) (litPC pc)
      (scratch 0) (scratch 1) j
  | .inr (.inl j) => (![.binary .mod (scratch 2) src (scratch 1) (pc (prep 1)),
      .constant (scratch 3) 0 (pc (prep 2)),
      .constant (scratch 0) 1 (pc (scanAt 0))] : Fin 3 → Instr W p r 11) j
  | .inr (.inr (.inl (j,false))) => .jumpEq (scratch 2) (scratch 3) (jump j) (pc (test j true))
  | .inr (.inr (.inl (j,true))) =>
    .binary .add (scratch 3) (scratch 3) (scratch 0) (pc (scanAt (j.val + 1)))
  | .inr (.inr (.inr _)) => .reject

/-- Relocatable native selector rows with five literal bits, for all block lengths. -/
def row (N : ℕ) (loc : Fin (count N) → Fin p) (scratch : Fin 4 ↪ Fin r)
    (src : Fin r) (jump : Fin N → Fin p) (j : Fin (count N)) : Instr 5 p r 11 :=
  native 5 (loc ∘ address N) scratch src jump ((address N).symm j)

private theorem resize_native (pc : Address N → Fin p) (scratch : Fin 4 ↪ Fin r)
    (src : Fin r) (jump : Fin N → Fin p) (j : Address N) :
    (native 5 pc scratch src jump j).resize w = native w pc scratch src jump j := by
  rcases j with j | j | ⟨j,b⟩ | j
  · simp only [native, InlinePublic.literalInstruction]
    split_ifs <;> rfl
  · fin_cases j <;> rfl
  · cases b <;> rfl
  · rfl

variable (M : Machine w p r 11) (loc : Fin (count N) → Fin p) (scratch : Fin 4 ↪ Fin r)
    (src : Fin r) (jump : Fin N → Fin p)

/-- The host contains every width-resized stage-selector instruction under the supplied
placements and jumps. -/
def Linked := ∀ j, M.code (loc j) = (row N loc scratch src jump j).resize w

private theorem atCode (link : Linked M loc scratch src jump) (j : Address N) :
    M.code (loc (address N j)) = native w (loc ∘ address N) scratch src jump j := by
  simpa only [row, Equiv.symm_apply_apply, resize_native] using link (address N j)

variable {M loc scratch src jump}

private theorem atStep (link : Linked M loc scratch src jump) (j : Address N)
    (c : Config w p r) (hc : c.pc = loc (address N j)) :
    M.program.step c = (native w (loc ∘ address N) scratch src jump j).run M.publicData c := by
  simp only [Machine.program, hc, atCode _ _ _ _ _ link]

/-- The stage selector preserves the machine state outside its designated scratch registers. -/
abbrev Frame (scratch : Fin 4 ↪ Fin r) (c d : Config w p r) :=
  RouteRange.Frame (fun i ↦ i ∉ Set.range scratch) c d

private theorem prepare (link : Linked M loc scratch src jump) (fresh : src ∉ Set.range scratch)
    (c : Config w p r) (hc : c.pc = loc (entry N)) (hN : N + 1 < 2 ^ w) :
    ∃ d, Prefix M c (List.replicate (N + 6) .tick) d ∧ d.pc = loc (address N (scanAt 0)) ∧
      d.reg (scratch 2) = ((c.reg src).val % (N + 1) : ℕ) ∧ d.reg (scratch 3) = 0 ∧
      d.reg (scratch 0) = 1 ∧ Frame scratch c d := by
  let pc := loc ∘ address N
  have start : c.pc = litPC pc 0 := by
    rw [show (0 : Fin ((N + 1) + 3)) = (0 : Fin ((N + 1) + 2)).castSucc from rfl,
      litPC, Fin.lastCases_castSucc]
    exact hc
  have lit (i : Fin ((N + 1) + 2)) : M.code (litPC pc i.castSucc) =
      InlinePublic.literalInstruction w (N + 1) (N + 1) (litPC pc) (scratch 0) (scratch 1) i := by
    rw [litPC, Fin.lastCases_castSucc]
    exact atCode _ _ _ _ _ link (.inl i)
  obtain ⟨a, pre, ha, modulus, outside, mem, persist⟩ :=
    InlinePublic.literal_prefix (scratch.injective.ne (by decide)) le_rfl lit c start
  rw [litPC, Fin.lastCases_last] at ha
  have ne (i : Fin r) (h : i ∉ Set.range scratch) (j : Fin 4) : i ≠ scratch j :=
    fun e ↦ h ⟨j,e.symm⟩
  let z : Word w := ((c.reg src).val % (N + 1) : ℕ)
  let b := a.put (pc (prep 1)) (scratch 2) z
  let e := b.put (pc (prep 2)) (scratch 3) 0
  let d := e.put (pc (scanAt 0)) (scratch 0) 1
  have h₀ : M.program.step a = .localStep b := by
    rw [atStep link (prep 0) a ha]
    change CallAction.localStep (a.put _ _ (BinaryOp.mod.eval (a.reg src) (a.reg (scratch 1)))) = _
    rw [outside src (ne _ fresh _) (ne _ fresh _), modulus]
    simp only [BinaryOp.eval, Fin.val_natCast, Nat.mod_eq_of_lt hN]
    rfl
  have h₁ : M.program.step b = .localStep e := atStep link (prep 1) b rfl
  have h₂ : M.program.step e = .localStep d := atStep link (prep 2) e rfl
  have boot : Prefix M a (List.replicate 3 .tick) d := .tick h₀ (.tick h₁ (.tick h₂ (.nil _)))
  have f : Frame scratch c a := ⟨fun i hi ↦ outside _ (ne _ hi _) (ne _ hi _), mem, persist⟩
  refine ⟨d, ?_, rfl, ?_, ?_, ?_, ((f.put _ _ _ (fun i h ↦ ne i h _)).put _ _ _
    (fun i h ↦ ne i h _)).put _ _ _ (fun i h ↦ ne i h _)⟩
  · simpa only [← List.replicate_add] using pre.append boot
  all_goals simp [d, e, b, Config.put, z]

private theorem scanTo (link : Linked M loc scratch src jump) (hN : N + 1 < 2 ^ w)
    (c : Config w p r) (hc : c.pc = loc (address N (scanAt 0))) (target : ℕ)
    (ht : target ≤ N) (residue : c.reg (scratch 2) = (target : Word w))
    (start : c.reg (scratch 3) = 0) (one : c.reg (scratch 0) = 1) (j : ℕ) (hj : j ≤ target) :
    ∃ d, Prefix M c (List.replicate (2 * j) .tick) d ∧ d.pc = loc (address N (scanAt j)) ∧
      d.reg (scratch 2) = (target : Word w) ∧ d.reg (scratch 3) = (j : Word w) ∧
      d.reg (scratch 0) = 1 ∧ Frame scratch c d := by
  induction j with
  | zero => exact ⟨c, by simpa using Prefix.nil (M := M) c, hc, residue, by simpa using start,
      one, RouteRange.Frame.refl c⟩
  | succ j ih =>
    obtain ⟨mid, pre, hp, hr, hj', hu, frame⟩ := ih (by omega)
    let i : Fin N := ⟨j, by omega⟩
    have atI : scanAt j = test i false := dite_eq_left i.isLt
    rw [atI] at hp
    let miss := {mid with pc := loc (address N (test i true))}
    let d := miss.put (loc (address N (scanAt (j + 1)))) (scratch 3) ((j + 1 : ℕ) : Word w)
    have unequal : (target : Word w) ≠ (j : Word w) := by
      intro he
      have h := congrArg Fin.val he
      rw [Fin.val_natCast, Fin.val_natCast, Nat.mod_eq_of_lt (by omega : target < 2 ^ w),
        Nat.mod_eq_of_lt (by omega : j < 2 ^ w)] at h
      omega
    have step₀ : M.program.step mid = .localStep miss := by
      rw [atStep link (test i false) mid hp]
      change CallAction.localStep {mid with pc := if mid.reg _ = mid.reg _ then _ else _} = _
      rw [hr, hj', ite_eq_right unequal]
      rfl
    have step₁ : M.program.step miss = .localStep d := by
      rw [atStep link (test i true) miss rfl]
      change CallAction.localStep (miss.put _ _ (mid.reg (scratch 3) + mid.reg (scratch 0))) = _
      simp only [hj', hu, Nat.cast_add, Nat.cast_one, d, i, Function.comp_apply]
    have tail : Prefix M mid (List.replicate 2 .tick) d := .tick step₀ (.tick step₁ (.nil _))
    have f : Frame scratch c miss := ⟨frame.regs, frame.memory, frame.persistent⟩
    refine ⟨d, ?_, rfl, ?_, ?_, ?_, f.put _ _ _ (fun t h e ↦ h ⟨3,e.symm⟩)⟩
    · simpa only [← List.replicate_add, Nat.mul_succ] using pre.append tail
    all_goals simp [d, miss, Config.put, hr, hu]

/-- The old stage ordinal leads to its actual shrink entry. The only events
are the fixed literal setup, three arithmetic rows and the bounded stage scan. -/
theorem run (link : Linked M loc scratch src jump) (fresh : src ∉ Set.range scratch)
    (hN : N + 1 < 2 ^ w) (stage : ℕ) (hs : stage < 2 ^ w) (i : Fin N)
    (selects : stage % (N + 1) = i.val) (c : Config w p r) (hc : c.pc = loc (entry N))
    (source : c.reg src = (stage : Word w)) :
    ∃ out, Prefix M c (List.replicate (N + 7 + 2 * i.val) .tick) out ∧
      out.pc = jump i ∧ Frame scratch c out := by
  obtain ⟨a, first, hp, hr, hz, hu, f⟩ := prepare link fresh c hc hN
  rw [source, Fin.val_natCast, Nat.mod_eq_of_lt hs, selects] at hr
  obtain ⟨b, second, hb, hr', hi, _, g⟩ := scanTo link hN a hp i.val i.isLt.le hr hz hu i.val le_rfl
  rw [scanAt, dite_eq_left i.isLt] at hb
  let out := {b with pc := jump i}
  have last : M.program.step b = .localStep out := by
    rw [atStep link (test i false) b hb]
    change CallAction.localStep {b with pc := if b.reg _ = b.reg _ then _ else _} = _
    rw [hr', hi, ite_eq_left rfl]
  have htail : Prefix M b (List.replicate 1 .tick) out := .tick last (.nil _)
  have events := (first.append second).append htail
  rw [← List.replicate_add, ← List.replicate_add] at events
  have g' : Frame scratch a out := ⟨g.regs, g.memory, g.persistent⟩
  exact ⟨out, by convert events using 2; omega, rfl, f.trans g'⟩

/-- The refresh ordinal reaches the physical rejection row of the shrink dispatcher. -/
theorem run_reject (link : Linked M loc scratch src jump) (fresh : src ∉ Set.range scratch)
    (hN : N + 1 < 2 ^ w) (stage : ℕ) (hs : stage < 2 ^ w)
    (refresh : stage % (N + 1) = N) (c : Config w p r) (hc : c.pc = loc (entry N))
    (source : c.reg src = (stage : Word w)) :
    ∃ out, Prefix M c (List.replicate (N + 6 + 2 * N) .tick) out ∧
      M.program.step out = .reject ∧ Frame scratch c out := by
  obtain ⟨a, first, hp, hr, hz, hu, f⟩ := prepare link fresh c hc hN
  rw [source, Fin.val_natCast, Nat.mod_eq_of_lt hs, refresh] at hr
  obtain ⟨b, second, hb, _, _, _, g⟩ := scanTo link hN a hp N le_rfl hr hz hu N le_rfl
  rw [scanAt, dite_eq_right (Nat.lt_irrefl _)] at hb
  exact ⟨b, by simpa only [← List.replicate_add] using first.append second,
    atStep link reject b hb, f.trans g⟩

private theorem tickLog (t : ℕ) :
    countProbes (List.replicate t (.tick : Event w)) = 0 ∧
      choiceBits (List.replicate t (.tick : Event w)) = [] := by
  induction t with
  | zero => exact ⟨rfl,rfl⟩
  | succ t ih => simpa only [List.replicate_succ, countProbes, choiceBits] using ih

theorem trace_cost (i : Fin N) :
    N + 7 + 2 * i.val ≤ 3 * N + 5 ∧
      countProbes (List.replicate (N + 7 + 2 * i.val) (.tick : Event w)) = 0 ∧
      choiceBits (List.replicate (N + 7 + 2 * i.val) (.tick : Event w)) = [] := by
  exact ⟨by have := i.isLt; omega, tickLog _⟩

/-- The tick-only prefix composes with the surrounding depth-first parser
on every external memory and unconsumed binary suffix. -/
theorem run_prefix (link : Linked M loc scratch src jump) (fresh : src ∉ Set.range scratch)
    (hN : N + 1 < 2 ^ w) (stage : ℕ) (hs : stage < 2 ^ w) (i : Fin N)
    (selects : stage % (N + 1) = i.val) (c : Config w p r) (hc : c.pc = loc (entry N))
    (source : c.reg src = (stage : Word w)) (m : Memory w) :
    ∃ out, NodeArguments.ChildScan.Prefix M m c out []
      (List.replicate (N + 7 + 2 * i.val) .tick) ∧ out.pc = jump i ∧ Frame scratch c out := by
  obtain ⟨out, h, pc, frame⟩ := run link fresh hN stage hs i selects c hc source
  exact ⟨out, fun fuel tail ↦ by simpa only [(trace_cost i).2.2] using h.execute fuel m tail,
    pc, frame⟩

/-- A refresh residue has no successful continuation through the shrink
dispatcher, at any fuel bound or on any pending choice stream. -/
theorem reject_noReturns (link : Linked M loc scratch src jump) (fresh : src ∉ Set.range scratch)
    (hN : N + 1 < 2 ^ w) (stage : ℕ) (hs : stage < 2 ^ w)
    (refresh : stage % (N + 1) = N) (c : Config w p r) (hc : c.pc = loc (entry N))
    (source : c.reg src = (stage : Word w)) (m : Memory w) (bs : List Bool) :
    ¬ DFS.Returns M c m bs := by
  obtain ⟨out, h, bad, _⟩ := run_reject link fresh hN stage hs refresh c hc source
  have pre : NodeArguments.ChildScan.Prefix M m c out [] (List.replicate (N + 6 + 2 * N) .tick) :=
    fun fuel tail ↦ by simpa only [(tickLog _).2] using h.execute fuel m tail
  intro success
  obtain ⟨fuel, rep, ran⟩ := (pre.returns bs).mp success
  cases fuel with
  | zero => simp [execute] at ran
  | succ f => simp [execute, bad] at ran

end PairSimulation.VertexStageDispatch

end VPVNP
end Computability
end OAI
