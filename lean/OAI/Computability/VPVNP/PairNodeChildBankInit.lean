import OAI.Computability.VPVNP.PairNodeChildLoop

/-!
# Initializing the register bank of child slot ordinals

The first slot receives zero. When a second slot exists it receives one.
Every subsequent instruction adds this stored unit to the preceding slot.
The fixed program uses one private instruction per slot at every word width.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.NodeArguments.ChildBankInit

open BurstRAM BurstRAM.PrivateRAM
open scoped Fin.CommRing

variable {a w p r k : ℕ}

/-- Select the label for child slot `n` while it is in range and transfer to the return label
once the ordinal bank is full. -/
def next (pc : Fin (2 ^ a) → Fin p) (ret : Fin p) (n : ℕ) : Fin p :=
  if h : n < 2 ^ a then pc ⟨n, h⟩ else ret

/-- The label of each slot contains its entire initialization instruction. -/
def instruction (pc : Fin (2 ^ a) → Fin p) (bank : Fin (2 ^ a) ↪ Fin r) (ret : Fin p)
    (j : Fin (2 ^ a)) : Instr w p r k :=
  let target := next pc ret (j.val + 1)
  if hz : j.val = 0 then .constant (bank j) 0 target
  else if ho : j.val = 1 then .constant (bank j) 1 target
  else .binary .add (bank j) (bank ⟨j.val - 1, by have := j.isLt; omega⟩)
    (bank ⟨1, by have := j.isLt; omega⟩) target

theorem resize_instruction (pc : Fin (2 ^ a) → Fin p) (bank : Fin (2 ^ a) ↪ Fin r)
    (ret : Fin p) (j : Fin (2 ^ a)) :
    (instruction (w := 5) (k := k) pc bank ret j).resize w = instruction pc bank ret j := by
  unfold instruction
  split <;> first | rfl | split <;> rfl

/-- Every supplied slot label contains the instruction that initializes its ordinal register
and continues to the next slot or the return label. -/
def Linked (M : Machine w p r k) (pc : Fin (2 ^ a) → Fin p) (bank : Fin (2 ^ a) ↪ Fin r)
    (ret : Fin p) : Prop := ∀ j, M.code (pc j) = instruction pc bank ret j

variable {M : Machine w p r k} {pc : Fin (2 ^ a) → Fin p} {bank : Fin (2 ^ a) ↪ Fin r}
variable {ret : Fin p}

private theorem step (link : Linked M pc bank ret) (j : Fin (2 ^ a)) (c : Config w p r)
    (hc : c.pc = pc j)
    (ready : ∀ i : Fin (2 ^ a), i.val < j.val → c.reg (bank i) = (i.val : Word w)) :
    M.program.step c = .localStep (c.put (next pc ret (j.val + 1)) (bank j) (j.val : Word w)) := by
  change (M.code c.pc).run M.publicData c = _
  rw [hc, link]
  unfold instruction
  split
  · rename_i hz
    simp only [Instr.run, hz, Nat.cast_zero]
  · rename_i hz
    split
    · rename_i ho
      simp only [Instr.run, ho, Nat.cast_one]
    · rename_i ho
      let prev : Fin (2 ^ a) := ⟨j.val - 1, by have := j.isLt; omega⟩
      let unit : Fin (2 ^ a) := ⟨1, by have := j.isLt; omega⟩
      change CallAction.localStep (c.put _ _ (c.reg (bank prev) + c.reg (bank unit))) = _
      have pred : prev.val + 1 = j.val := by dsimp [prev]; omega
      rw [ready prev (by omega), ready unit (by dsimp [unit]; omega)]
      change CallAction.localStep (c.put _ _ ((prev.val : Word w) + ((1 : ℕ) : Word w))) = _
      rw [← Nat.cast_add, pred]

private theorem one_tick (m : Memory w) {c d : Config w p r}
    (h : M.program.step c = .localStep d) : ChildScan.Prefix M m c d [] [.tick] := by
  intro fuel tail
  simp only [List.nil_append, List.length_cons, List.length_nil, execute, h]
  rfl

/-- Execute the initializer from arbitrary registers. The argument suffix and
external memory are passed directly to the continuation. -/
theorem native (link : Linked M pc bank ret) (m : Memory w) (c : Config w p r)
    (hc : c.pc = pc 0) :
    ∃ d, d.pc = ret ∧ d.persistent = c.persistent ∧ d.privateMem = c.privateMem ∧
      (∀ j, d.reg (bank j) = (j.val : Word w)) ∧
      (∀ x, x ∉ Set.range bank → d.reg x = c.reg x) ∧
      ChildScan.Prefix M m c d [] (List.replicate (2 ^ a) .tick) := by
  have upto (n : ℕ) (hn : n ≤ 2 ^ a) :
      ∃ d, d.pc = next pc ret n ∧ d.persistent = c.persistent ∧ d.privateMem = c.privateMem ∧
        (∀ j : Fin (2 ^ a), j.val < n → d.reg (bank j) = (j.val : Word w)) ∧
        (∀ x, x ∉ Set.range bank → d.reg x = c.reg x) ∧
        ChildScan.Prefix M m c d [] (List.replicate n .tick) := by
    induction n with
    | zero =>
      have pos : 0 < 2 ^ a := pow_pos (by decide) _
      refine ⟨c, ?_, rfl, rfl, fun j hj => (Nat.not_lt_zero _ hj).elim, fun _ _ => rfl, ?_⟩
      · rw [next, dite_eq_left pos, hc]
        congr 1
      · intro fuel tail
        simp
    | succ n ih =>
      have room : n < 2 ^ a := hn
      let j : Fin (2 ^ a) := ⟨n, room⟩
      obtain ⟨d, atPC, state, priv, ready, frame, run⟩ := ih room.le
      let z := d.put (next pc ret (n + 1)) (bank j) (n : Word w)
      have hj : d.pc = pc j := by simpa only [next, dite_eq_left room, j] using atPC
      have single : ChildScan.Prefix M m d z [] [.tick] := one_tick m (step link j d hj ready)
      refine ⟨z, rfl, state, priv, ?_, ?_, ?_⟩
      · intro i hi
        by_cases e : i = j
        · subst i
          exact Config.put_same ..
        · have ne : i.val ≠ n := fun he => e (Fin.ext he)
          exact (Function.update_of_ne (bank.injective.ne e) ..).trans (ready i (by omega))
      · intro x hx
        have ne : x ≠ bank j := fun e => hx ⟨j, e.symm⟩
        exact (Function.update_of_ne ne ..).trans (frame x hx)
      · simpa only [List.nil_append, List.replicate_succ'] using run.trans single
  obtain ⟨d, atPC, state, priv, ready, frame, run⟩ := upto (2 ^ a) le_rfl
  exact ⟨d, by simpa only [next, lt_self_iff_false, ↓reduceDIte] using atPC, state, priv,
    fun j => ready j j.isLt, frame, run⟩

end PairSimulation.NodeArguments.ChildBankInit

end VPVNP
end Computability
end OAI
