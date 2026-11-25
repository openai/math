import OAI.Computability.BorderVNP.CubeISAOwnedScan

/-! # Checking precisely the selected finite row indices

This form of the native row iterator takes predicates and address readouts
on the actual finite candidate set. Only the callback supplied for a selected
index may write memory; classification preserves the low loop registers.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Owned

open VPVNP.BurstRAM Finset

/-- Natural row invariants that survive candidate calculation in high scratch registers. -/
def stableLow (I : ℕ → NatState → Prop) : Prop :=
  ∀ k z y, I k z → (∀ j : Reg, j.val < 24 → y.reg j = z.reg j) → y.mem = z.mem → I k y

/-- The fixed local scan runs each selected callback and returns exactly when
all of its tests pass. The callback receives the concrete readout at its
finite index, with the loop state retained. -/
theorem finiteRow_run {w N : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (candidate body : Code) (prep : ℕ) (cost : Fin N → ℕ) (selected good : Fin N → Prop)
    [DecidablePred selected] (read : Fin N → NatState → Prop) (I : ℕ → NatState → Prop)
    (fit : N < 2^w) (stable : stableLow I)
    (regs : ∀ k z, I k z → z.reg 1 = 1 ∧ z.reg 18 = k ∧ z.reg 19 = N)
    (prepare : ∀ (t : Fin N) s m, I t.val (.ofWords s m) →
      BoundedRun pub macros candidate s m prep (fun z =>
        read t z ∧ z.reg 40 = (if selected t then 1 else 0) ∧
        (∀ j : Reg, j.val < 24 → z.reg j = readings s j) ∧ z.mem = readings m))
    (det : candidate.deterministic = true)
    (visit : ∀ t, selected t → ∀ s m, I t.val (.ofWords s m) → read t (.ofWords s m) →
      TestRun pub macros body s m (cost t) (good t) (nextAt I 18 t.val))
    (skip : ∀ t, ¬ selected t → ∀ z, I t.val z → I (t.val+1) (increment 18 z))
    (s : Bank w) (m : Memory w) (start : I 0 (.ofWords s m)) :
    TestRun pub macros (rowLoop candidate body) s m
      ((∑ t : Fin N, (prep+3 + if selected t then cost t else 1))+1)
      (∀ t, selected t → good t) (I N) := by
  let pick (k : ℕ) := if h : k < N then decide (selected ⟨k,h⟩) else false
  let v (k : ℕ) := if h : k < N then cost ⟨k,h⟩ else 0
  let pass (k : ℕ) := ∀ h : k < N, good ⟨k,h⟩
  let P (k : ℕ) (z : NatState) := I k z ∧ z.reg 40 = (pick k).toNat ∧ ∀ h : k < N, read ⟨k,h⟩ z
  have front k (hk : k < N) u mu (hi : I k (.ofWords u mu)) :
      TestRun pub macros candidate u mu prep True (P k) := by
    apply ((prepare ⟨k,hk⟩ u mu hi).mono le_rfl ?_).asTest det
    rintro z ⟨hr,hflag,hl,hm⟩
    refine ⟨stable k _ z hi hl hm, ?_, fun _ => hr⟩
    by_cases h : selected ⟨k,hk⟩ <;> simpa [pick, hk,h] using hflag
  have callback k (hk : k < N) (he : pick k = true) u mu (hp : P k (.ofWords u mu)) :
      TestRun pub macros body u mu (v k) (pass k) (nextAt I 18 k) := by
    have sel : selected ⟨k,hk⟩ := by simpa [pick,hk] using he
    simpa [v,hk,pass] using visit ⟨k,hk⟩ sel u mu hp.1 (hp.2.2 hk)
  have bypass k (hk : k < N) (he : pick k = false) z (hp : P k z) : nextAt I 18 k z := by
    have ns : ¬selected ⟨k,hk⟩ := by simpa [pick,hk] using he
    obtain ⟨unit,cursor,_⟩ := regs k z hp.1
    exact ⟨unit,cursor,skip ⟨k,hk⟩ ns z hp.1⟩
  have run := rowLoop_run candidate body N prep v pick pass I P fit (fun k z h => (regs k z h).2)
    front (fun k z h => ⟨(regs k z h.1).1,h.2.1⟩) callback bypass s m start
  apply run.mono ?_ ?_ (fun _ h => h)
  · rw [← Fin.sum_univ_eq_sum_range]
    apply Nat.add_le_add_right
    apply sum_le_sum
    intro t _
    simp [pick,v,t.isLt]
  · constructor
    · intro h t hs
      exact h t.val t.isLt (by simp [pick,t.isLt,hs]) t.isLt
    · intro h k hk hp _
      exact h ⟨k,hk⟩ (by simpa [pick,hk] using hp)

end RoutingISA.Owned

end BorderVNP
end Computability
end OAI
