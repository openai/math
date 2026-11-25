import OAI.Computability.BorderVNP.RoutingISACheckLoop
import OAI.Computability.BorderVNP.RoutingISATableEvents

/-! # Native ordered-pair scan of both cable padding intervals

The endpoint code may have a different cost on every row and side. The bound sums
those costs, so a long interval contributes only at a site that actually visits it.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Padding

open RoutingISA VPVNP.BurstRAM Finset

/-- Check the source end, then the destination end, and advance the directory cursor. -/
def pairStep (endpoint : Bool → Code) : Code :=
  .seq (endpoint false) (.seq (endpoint true) (.binary .add 13 13 1))

/-- A runtime loop over the ordered-pair directory in register 5. -/
def forPairs (endpoint : Bool → Code) : Code :=
  .seq (.copy 13 0) (.whileLt 13 5 (pairStep endpoint))

/-- One copy, a final loop test, and per row one guard, one increment, and both endpoints. -/
def pairBudget (count : ℕ) (cost : ℕ → Bool → ℕ) : ℕ :=
  2 + ∑ i ∈ range count, (cost i false + cost i true + 2)

/-- The native ordered-pair loop returns precisely when both ends pass at every
row. In particular, the output of the first endpoint is the input to the second,
and the arithmetic increment is checked at the physical word width. -/
theorem test_forPairs {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (endpoint : Bool → Code) (count : ℕ) (cost : ℕ → Bool → ℕ) (good : ℕ → Bool → Prop)
    (stable : NatState → Prop)
    (regs : ∀ z, stable z → z.reg 0 = 0 ∧ z.reg 1 = 1 ∧ z.reg 5 = count)
    (write : ∀ z v, stable z → stable ⟨Function.update z.reg 13 v,z.mem⟩)
    (check : ∀ i < count, ∀ side s m, stable (.ofWords s m) → (s 13).val = i →
      TestRun pub mac (endpoint side) s m (cost i side) (good i side)
        (fun z => stable z ∧ z.reg 13 = i))
    (s : Bank w) (m : Memory w) (hs : stable (.ofWords s m)) :
    TestRun pub mac (forPairs endpoint) s m (pairBudget count cost)
      (∀ i < count, ∀ side, good i side) (fun z => stable z ∧ z.reg 13 = count) := by
  let Inv (i : ℕ) (z : NatState) := stable z ∧ z.reg 13 = i
  let budget (i : ℕ) := cost i false + (cost i true + 1)
  have bound : count < 2^w := (regs _ hs).2.2 ▸ (s 5).isLt
  have increment (i : ℕ) (hi : i < count) (t : Bank w) (mt : Memory w) (h : Inv i (.ofWords t mt)) :
      TestRun pub mac (.binary .add 13 13 1) t mt 1 True (Inv (i+1)) := by
    let z := NatState.ofWords t mt
    have one : z.reg 1 = 1 := (regs z h.1).2.1
    have cursor : z.reg 13 = i := h.2
    have safe : (Code.binary .add 13 13 1).fixedSafe w (readings pub) z := by
      change z.reg 13 + z.reg 1 < 2^w
      omega
    apply (((Code.binary .add 13 13 1).runFixed pub mac t mt safe).asTest rfl).mono le_rfl Iff.rfl
    rintro _ rfl
    change Inv (i+1) ⟨Function.update z.reg 13 (z.reg 13 + z.reg 1), z.mem⟩
    rw [cursor,one]
    exact ⟨write z (i+1) h.1,by simp⟩
  have step (i : ℕ) (hi : i < count) (t : Bank w) (mt : Memory w) (h : Inv i (.ofWords t mt)) :
      TestRun pub mac (pairStep endpoint) t mt (budget i) (∀ side, good i side) (Inv (i+1)) := by
    have a := (check i hi false t mt h.1 h.2).seq (fun u mu hu =>
      (check i hi true u mu hu.1 hu.2).seq (fun v mv hv => increment i hi v mv hv))
    apply a.mono le_rfl _ fun _ => id
    exact ⟨fun ⟨hf,ht,_⟩ side => by cases side <;> assumption,fun hg => ⟨hg false,hg true,trivial⟩⟩
  have initial : TestRun pub mac (.copy 13 0) s m 1 True (Inv 0) := by
    apply (((Code.copy 13 0).runFixed pub mac s m trivial).asTest rfl).mono le_rfl Iff.rfl
    rintro _ rfl
    let z := NatState.ofWords s m
    change Inv 0 ⟨Function.update z.reg 13 (z.reg 0),z.mem⟩
    rw [(regs z hs).1]
    exact ⟨write z 0 hs,by simp⟩
  have walk := initial.seq (fun t mt ht =>
    test_counted_loop 13 5 (pairStep endpoint) count budget (fun i => ∀ side, good i side)
      Inv (fun _ z h => ⟨h.2,(regs z h.1).2.2⟩) step 0 (Nat.zero_le _) t mt ht)
  apply walk.mono _ _ fun _ => id
  · simp only [Nat.Ico_zero_eq_range,budget,pairBudget,Nat.add_assoc,Nat.reduceAdd]
    omega
  · exact ⟨fun h i hi => h.2 i (Nat.zero_le _) hi,fun h => ⟨trivial,fun i _ hi => h i hi⟩⟩

/-- Summing endpoint allowances charges the per-bit cost only to the number of
owned slots and the metadata cost only to the number of ordered pairs. -/
theorem pairBudget_le (count overhead perBit : ℕ) (cost owned : ℕ → Bool → ℕ)
    (cap : ∀ i < count, ∀ side, cost i side ≤ overhead + perBit * owned i side) :
    pairBudget count cost ≤ 2 + count * (2*overhead+2) +
      perBit * ∑ i ∈ range count, (owned i false + owned i true) := by
  unfold pairBudget
  calc
    _ ≤ 2 + ∑ i ∈ range count, ((2*overhead+2) + perBit * (owned i false + owned i true)) := by
      apply Nat.add_le_add_left
      apply Finset.sum_le_sum
      intro i hi
      have a := cap i (mem_range.mp hi) false
      have b := cap i (mem_range.mp hi) true
      rw [Nat.mul_add]
      omega
    _ = _ := by simp [Finset.sum_add_distrib,← Finset.mul_sum,Nat.add_assoc,Nat.mul_add]

/-- A loop of deterministic endpoint checks has a unique event trace and return state. -/
theorem forPairs_deterministic (endpoint : Bool → Code)
    (hd : ∀ side, (endpoint side).deterministic = true) : (forPairs endpoint).deterministic = true := by
  simp [forPairs,pairStep,Code.deterministic,hd]

/-- Every event of a successful unsigned padding scan has sign plus and empty choices. -/
theorem forPairs_unsigned (endpoint : Bool → Code)
    (hu : ∀ side, (endpoint side).unsigned = true) : (forPairs endpoint).unsigned = true := by
  simp [forPairs,pairStep,Code.unsigned,hu]

end Cube.Padding

end BorderVNP
end Computability
end OAI
