import OAI.Computability.VPVNP.RAMTapeWordISAClear

/-!
# Fresh private workspace at every burst call

A call starts with one persistent word and its public constants. The processor
overwrites every private register with a width-correct zero and clears the
newest-first write log. Its cost depends on the stored entries, including for
the first call where the physical register stacks may be empty.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.ISA

open BurstRAM BurstRAM.PrivateRAM

variable {r k w : ℕ}

private def zeroList : List (Fin r) → FiniteRoutine (Port r k)
  | [] => .ret
  | i :: is => (loadLiteral 0 i).followedBy (zeroList is)

private def zeroed (is : List (Fin r)) (s : Stacks (Port r k)) : Stacks (Port r k)
  | .reg i => if i ∈ is then wordBits (0 : Word w) else s (.reg i)
  | j => s j

private theorem zeroList_run (is : List (Fin r)) (s : Stacks (Port r k)) (persist : Word w)
    (hp : s .persistent = wordBits persist) (h14 : s (.work 14) = []) (h15 : s (.work 15) = [])
    (hr : ∀ i, (s (.reg i)).length ≤ w) :
    ∃ t ≤ is.length * (8*w+3) + 1, (zeroList is).Runs t s (zeroed (w := w) is s) := by
  induction is generalizing s with
  | nil =>
    have he : zeroed (w := w) [] s = s := by funext j; cases j <;> simp [zeroed]
    exact ⟨1, by simp, he.symm ▸ Routine.runs_ret s⟩
  | cons i is ih =>
    let s' := Function.update s (.reg i) (wordBits (0 : Word w))
    have hhead : (loadLiteral 0 i).Runs ((s (.reg i)).length + 7*w+3) s s' :=
      loadLiteral_at 0 i s persist hp h14 h15
    obtain ⟨t, ht, htail⟩ := ih s' (by simpa [s'] using hp) (by simpa [s'] using h14)
      (by simpa [s'] using h15) (fun j => by
        by_cases he : i = j
        · subst j; simp [s']
        · simpa [s', Function.update_of_ne (show Port.reg j ≠ (Port.reg i : Port r k) by
            intro h; exact he (Port.reg.inj h).symm)] using hr j)
    have he : zeroed (w := w) is s' = zeroed (w := w) (i :: is) s := by
      funext j
      cases j with
      | reg j => by_cases hji : j = i <;> simp [zeroed, s', hji, Function.update_of_ne]
      | pub | persistent | work | logPort => simp [zeroed, s']
    rw [he] at htail
    refine ⟨_, ?_, hhead.followedBy htail⟩
    have := hr i
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

private def logPorts : List (Port r k) := [.logPort .keys, .logPort .values, .logPort .occupied]

/-- Start a private call with width-correct zeroes in all registers and clear the write log's
key, value and occupancy streams. -/
def freshCall : FiniteRoutine (Port r k) :=
  (zeroList (List.finRange r)).followedBy (clearList logPorts)

/-- Before a call the private register bank may still contain bits from a
previous call. The three log streams have a bounded total entry count. -/
def preCall (pub : Fin k → Word w) (persistent : Word w) (raw : Fin r → List Bool)
    (log : WriteLog w) : Stacks (Port r k)
  | .reg i => raw i
  | .pub i => wordBits (pub i)
  | .persistent => wordBits persistent
  | .work _ => []
  | .logPort i => logStacks log i

theorem freshCall_run (pub : Fin k → Word w) (persistent : Word w) (raw : Fin r → List Bool)
    (log : WriteLog w) (hr : ∀ i, (raw i).length ≤ w) :
    ∃ t ≤ r*(8*w+3)+3*(log.length*(w+1)+1)+2,
      (freshCall (r := r) (k := k)).Runs t (preCall pub persistent raw log)
        (bank pub persistent (fun _ => 0) []) := by
  let s := preCall pub persistent raw log
  let z := zeroed (w := w) (List.finRange r) s
  have hz := zeroList_run (List.finRange r) s persistent rfl rfl rfl hr
  obtain ⟨a, ha, h₁⟩ := hz
  have hl (l : WriteLog w) : (AddressLog.keys l).length = l.length*w ∧
      (AddressLog.values l).length = l.length*w := by
    induction l with
    | nil => simp [AddressLog.keys, AddressLog.values]
    | cons pair xs ih =>
      change (wordBits pair.1 ++ AddressLog.keys xs).length = (xs.length+1)*w ∧
        (wordBits pair.2 ++ AddressLog.values xs).length = (xs.length+1)*w
      simp [ih.1, ih.2, Nat.add_mul, Nat.add_comm]
  have hc : ∀ j ∈ logPorts, (z j).length ≤ log.length*(w+1) := by
    intro j hj
    have ⟨hk, hv⟩ := hl log
    rcases (show j = .logPort .keys ∨ j = .logPort .values ∨ j = .logPort .occupied by
      simpa [logPorts] using hj) with rfl | rfl | rfl <;>
      simp [z, zeroed, s, preCall, logStacks, hk, hv, Nat.mul_succ]
  obtain ⟨b, hb, h₂⟩ := clearList_runs logPorts z (log.length*(w+1)) hc
  have he : cleared logPorts z = bank pub persistent (fun _ => 0) [] := by
    funext j
    cases j with
    | reg j | pub j | work j => simp [z, s, zeroed, cleared, logPorts, preCall, bank]
    | persistent => simp [z, s, zeroed, cleared, logPorts, preCall, bank]
    | logPort j => cases j <;> simp [z, s, zeroed, cleared, logPorts, preCall, bank, logStacks,
        AddressLog.keys, AddressLog.values]
  rw [he] at h₂
  refine ⟨_, ?_, h₁.followedBy h₂⟩
  simp only [List.length_finRange] at ha
  change b ≤ 3*(log.length*(w+1)+1)+1 at hb
  omega

end RAMTape.ISA

end VPVNP
end Computability
end OAI
