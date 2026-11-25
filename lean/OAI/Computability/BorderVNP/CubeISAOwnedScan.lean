import OAI.Computability.BorderVNP.RoutingISACheckLoop

/-! # Native sparse iteration on one owned symbol row

Each counter position first prepares its physical address and computes a one-bit
flag. Only a set flag enters the supplied packet or singleton fragment. The
trace allowance charges the fragment only for the selected counter positions.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Owned

open VPVNP.BurstRAM Finset

/-- Natural image of one unsigned cursor increment. -/
def increment (r : Reg) (z : NatState) : NatState :=
  ⟨Function.update z.reg r (z.reg r + 1), z.mem⟩

/-- The callback must preserve the cursor and its unit increment register
and establish the next invariant after the scanner advances. -/
def nextAt (I : ℕ → NatState → Prop) (r : Reg) (i : ℕ) (z : NatState) : Prop :=
  z.reg 1 = 1 ∧ z.reg r = i ∧ I (i+1) (increment r z)

/-- The scalar offset loop used inside one accepted singleton pair. -/
def bitLoop (body : Code) : Code :=
  .seq (.copy 20 0) (.whileLt 20 21 (.seq body (.binary .add 20 20 1)))

/-- Fixed-control scan of the candidate interval in registers 18 and 19.
The address calculation returns its `0`/`1` flag in register 40. -/
def rowLoop (candidate body : Code) : Code :=
  .whileLt 18 19 (.seq candidate (.seq (.ifEq 40 1 body .nop) (.binary .add 18 18 1)))

variable {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}

private theorem incrementTest {r : Reg} {i : ℕ} {I : ℕ → NatState → Prop}
    {s : Bank w} {m : Memory w} (h : nextAt I r i (.ofWords s m)) (fit : i+1 < 2^w) :
    TestRun pub macros (.binary .add r r 1) s m 1 True (I (i+1)) := by
  obtain ⟨unit, cursor, hn⟩ := h
  have safe : (Code.binary .add r r 1).fixedSafe w (readings pub) (.ofWords s m) := by
    change (NatState.ofWords s m).reg r + (NatState.ofWords s m).reg 1 < _
    rwa [unit,cursor]
  apply ((Code.runFixed _ pub macros s m safe).mono le_rfl ?_).asTest rfl
  intro z hz
  rw [hz]
  change I (i+1) ⟨Function.update _ r ((NatState.ofWords s m).reg r + (NatState.ofWords s m).reg 1),_⟩
  rw [unit]
  exact hn

private theorem branchTest {s : Bank w} {m : Memory w} {a b : Code} {v : ℕ} {ok : Prop}
    {P : NatState → Prop}
    (chosen : TestRun pub macros (if s 40 = s 1 then a else b) s m v ok P) :
    TestRun pub macros (.ifEq 40 1 a b) s m (1+v) ok P := by
  constructor
  · intro good
    obtain ⟨es,t,mt,run,cap,post⟩ := chosen.complete good
    exact ⟨_,t,mt,Runs.ifEq run,show 1+traceCost es ≤ _ from Nat.add_le_add_left cap _,post⟩
  · intro es t mt run
    obtain ⟨_,_,ht⟩ := CellDispatch.eq_split run
    exact chosen.sound ht

/-- Iterate over scalar bits only when a caller actually enters this fragment.
The callback receives each offset once and its test must pass at every offset. -/
theorem bitLoop_run (body : Code) (bits : ℕ) (cost : ℕ → ℕ) (good : ℕ → Prop)
    (I : ℕ → NatState → Prop) (fit : bits < 2^w)
    (regs : ∀ j z, I j z → z.reg 20 = j ∧ z.reg 21 = bits)
    (visit : ∀ j < bits, ∀ s m, I j (.ofWords s m) →
      TestRun pub macros body s m (cost j) (good j) (nextAt I 20 j))
    (s : Bank w) (m : Memory w) (hz : readings s 0 = 0)
    (start : I 0 ⟨Function.update (readings s) 20 0, readings m⟩) :
    TestRun pub macros (bitLoop body) s m (2 + ∑ j ∈ range bits, (cost j + 2))
      (∀ j < bits, good j) (I bits) := by
  have init := ((Code.copy 20 0).runFixed pub macros s m trivial).asTest rfl
  let visitCost j := cost j + 1
  have step j (hj : j < bits) s m (hi : I j (.ofWords s m)) :=
    ((visit j hj s m hi).seq (fun _ _ hh => incrementTest hh (Nat.lt_of_le_of_lt hj fit))).mono
      le_rfl (show good j ∧ True ↔ good j by simp) (fun _ hh => hh)
  have scan := init.seq (fun t mt ht => test_counted_loop 20 21 (.seq body (.binary .add 20 20 1))
    bits visitCost good I regs step 0 (Nat.zero_le _) t mt (by
      rw [ht]
      change I 0 ⟨Function.update (readings s) 20 (readings s 0), readings m⟩
      rwa [hz]))
  apply scan.mono ?_ ?_ (fun _ h => h)
  · simp only [Code.slots, visitCost, Nat.add_assoc, Nat.reduceAdd, Nat.Ico_zero_eq_range]
    omega
  · simp

/-- Checked execution of the native row iterator. Its exact loop allowance
includes address/filter work per candidate and callback work only at the
owned packet or singleton addresses which pass the physical digit test. -/
theorem rowLoop_run (candidate body : Code) (N prep : ℕ) (cost : ℕ → ℕ) (emit : ℕ → Bool)
    (good : ℕ → Prop) (I P : ℕ → NatState → Prop) (fit : N < 2^w)
    (regs : ∀ i z, I i z → z.reg 18 = i ∧ z.reg 19 = N)
    (prepare : ∀ i < N, ∀ s m, I i (.ofWords s m) →
      TestRun pub macros candidate s m prep True (P i))
    (flag : ∀ i z, P i z → z.reg 1 = 1 ∧ z.reg 40 = (emit i).toNat)
    (visit : ∀ i < N, emit i = true → ∀ s m, P i (.ofWords s m) →
      TestRun pub macros body s m (cost i) (good i) (nextAt I 18 i))
    (skip : ∀ i < N, emit i = false → ∀ z, P i z → nextAt I 18 i z)
    (s : Bank w) (m : Memory w) (start : I 0 (.ofWords s m)) :
    TestRun pub macros (rowLoop candidate body) s m
      ((∑ i ∈ range N, (prep+3 + if emit i then cost i else 1))+1)
      (∀ i < N, emit i = true → good i) (I N) := by
  let v i := if emit i then cost i else 1
  have step i (hi : i < N) s m (hh : I i (.ofWords s m)) := by
    let g := emit i = true → good i
    have choose s m (p : P i (.ofWords s m)) :
        TestRun pub macros (.ifEq 40 1 body .nop) s m (1+v i) g (nextAt I 18 i) := by
      apply branchTest
      obtain ⟨h1,h40⟩ := flag i _ p
      cases he : emit i with
      | true =>
        have eqn : s 40 = s 1 := Fin.ext (h40.trans (he ▸ h1.symm))
        simpa [eqn, v, he, g] using visit i hi he s m p
      | false =>
        have ne : s 40 ≠ s 1 := by
          intro e
          have e' : (NatState.ofWords s m).reg 40 = (NatState.ofWords s m).reg 1 := congrArg Fin.val e
          simp [h1,h40,he] at e'
        have hn : TestRun pub macros .nop s m 1 True (nextAt I 18 i) := ((Code.nop.runFixed pub macros s m trivial).mono le_rfl
          (fun z eqn => by rw [eqn]; exact skip i hi he _ p)).asTest rfl
        simpa [ne,v,he,g] using hn
    have run := (prepare i hi s m hh).seq (fun t mt h =>
      (choose t mt h).seq (fun _ _ hnext => incrementTest hnext (Nat.lt_of_le_of_lt hi fit)))
    exact run.mono (Nat.le_refl _) (show True ∧ g ∧ True ↔ g by simp) (fun _ h => h)
  have run := test_counted_loop 18 19 _ N _ (fun i => emit i = true → good i) I
    regs step 0 (Nat.zero_le _) s m start
  apply run.mono ?_ ?_ (fun _ h => h)
  · rw [Nat.Ico_zero_eq_range]
    apply Nat.add_le_add_right
    apply sum_le_sum
    intro i _
    dsimp only [v]
    omega
  · simp

end RoutingISA.Owned

end BorderVNP
end Computability
end OAI
