import OAI.Computability.BorderVNP.CubeISAOwnedFiniteScan
import OAI.Computability.BorderVNP.CubeISAOwnedPrepare

/-! # Executing the physical packet and singleton iterators

The only varying code is the local work for a selected packet or bit family.
Candidate generation, digit validation, address preparation, counter advance,
and skipped candidates use fixed ordinary instructions.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Owned

open VPVNP.BurstRAM Cube Cube.Physical.Owned

variable {n d blocks w : ℕ}

/-- Input registers for an owned packet row. -/
def packetReady (i : Fin (n+1)) (pair : Symbols d) (stride base cursor : ℕ) (z : NatState) : Prop :=
  z.reg 0 = 0 ∧ z.reg 1 = 1 ∧ z.reg 2 = 2 ∧ z.reg 10 = d ∧ z.reg 11 = d*d ∧
  z.reg 12 = (d*d)^i.val ∧ z.reg 13 = blocks ∧ z.reg 14 = pair.val.1.val ∧
  z.reg 15 = pair.val.2.val ∧ z.reg 16 = stride ∧ z.reg 17 = base ∧ z.reg 18 = cursor ∧
  z.reg 19 = packetTrials n d blocks

/-- Register-level address delivered to the packet callback. -/
def packetAt (i : Fin (n+1)) (pair : Symbols d) (stride base : ℕ)
    (t : Fin (packetTrials n d blocks)) (z : NatState) : Prop :=
  let k := trialPacketIndex d ((d*d)^i.val) blocks pair.val.1.val pair.val.2.val t.val
  z.reg 24 = base+k*stride ∧ z.reg 25 = t.val/blocks%2 ∧ z.reg 26 = k

/-- The full local packet loop runs exactly the successful checks on the
physical row. Its output contains their accumulated state in the invariant. -/
theorem packetRow_run (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (i : Fin (n+1)) (pair : Symbols d) (stride base : ℕ) (body : Code)
    (cost : Fin (packetTrials n d blocks) → ℕ) (good : Fin (packetTrials n d blocks) → Prop)
    (I : ℕ → NatState → Prop) (stable : stableLow I)
    (regs : ∀ k z, I k z → packetReady (blocks := blocks) i pair stride base k z)
    (fit : packetTrials n d blocks < 2^w) (hs : 0 < stride)
    (room : ∀ t : Fin (packetTrials n d blocks),
      base + trialPacketIndex d ((d*d)^i.val) blocks pair.val.1.val pair.val.2.val t.val * stride < 2^w)
    (visit : ∀ t, packetTrialValid t → ∀ s m, I t.val (.ofWords s m) →
      packetAt i pair stride base t (.ofWords s m) →
      TestRun pub macros body s m (cost t) (good t) (nextAt I 18 t.val))
    (skip : ∀ t : Fin (packetTrials n d blocks), ¬packetTrialValid t →
      ∀ z, I t.val z → I (t.val+1) (increment 18 z))
    (s : Bank w) (m : Memory w) (start : I 0 (.ofWords s m)) :
    TestRun pub macros (rowLoop (packetCandidate n) body) s m
      ((∑ t : Fin (packetTrials n d blocks), (6*n+22 + if packetTrialValid t then cost t else 1))+1)
      (∀ t, packetTrialValid t → good t) (I (packetTrials n d blocks)) := by
  apply finiteRow_run pub macros (packetCandidate n) body (6*n+19) cost packetTrialValid good
    (packetAt i pair stride base) I fit stable ?_ ?_ (packetCandidate_deterministic n) visit skip s m start
  · intro k z hi
    obtain ⟨_,h1,_,_,_,_,_,_,_,_,_,hc,hN⟩ := regs k z hi
    exact ⟨h1,hc,hN⟩
  · intro t u mu hi
    obtain ⟨r0,r1,r2,r10,r11,r12,r13,r14,r15,r16,r17,r18,_⟩ := regs t.val _ hi
    apply (packetCandidate_run pub macros u mu i pair t r0 r1 r2 r10 r11 r12 r13 r14 r15
      r16 r17 r18 hs (room t)).mono le_rfl
    rintro z ⟨a,o,k,f,hl,hm⟩
    exact ⟨⟨a,o,k⟩,f,hl,hm⟩

/-- Input registers for one orientation of a singleton row. -/
def singleReady (i : Fin (n+1)) (a b : Fin d) (cursor : ℕ) (z : NatState) : Prop :=
  z.reg 0 = 0 ∧ z.reg 1 = 1 ∧ z.reg 10 = d ∧ z.reg 11 = d^n ∧ z.reg 12 = d^i.val ∧
  z.reg 14 = a.val ∧ z.reg 15 = b.val ∧ z.reg 18 = cursor ∧ z.reg 19 = singlePairTrials n d

/-- The callback reads the actual full label codes of the two endpoints. -/
def singleAt (i : Fin (n+1)) (a b : Fin d) (t : Fin (singlePairTrials n d)) (z : NatState) : Prop :=
  let p := (singleOrderedPairs i a b t).val
  z.reg 24 = (finFunctionFinEquiv p.1).val ∧ z.reg 25 = (finFunctionFinEquiv p.2).val

/-- The singleton family fragment is entered only for actual singleton pairs,
where registers 24 and 25 contain the true ordered endpoint labels. -/
theorem singleRow_run (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (i : Fin (n+1)) (a b : Fin d) (body : Code) (cost : Fin (singlePairTrials n d) → ℕ)
    (good : Fin (singlePairTrials n d) → Prop) (I : ℕ → NatState → Prop) (stable : stableLow I)
    (regs : ∀ k z, I k z → singleReady i a b k z)
    (fit : singlePairTrials n d < 2^w) (labels : d^(n+1) ≤ 2^w)
    (visit : ∀ t, singleTrialValid i a b t → ∀ s m, I t.val (.ofWords s m) →
      singleAt i a b t (.ofWords s m) →
      TestRun pub macros body s m (cost t) (good t) (nextAt I 18 t.val))
    (skip : ∀ t : Fin (singlePairTrials n d), ¬singleTrialValid i a b t →
      ∀ z, I t.val z → I (t.val+1) (increment 18 z))
    (s : Bank w) (m : Memory w) (start : I 0 (.ofWords s m)) :
    TestRun pub macros (rowLoop (singleCandidate n) body) s m
      ((∑ t : Fin (singlePairTrials n d), (6*n+20 + if singleTrialValid i a b t then cost t else 1))+1)
      (∀ t, singleTrialValid i a b t → good t) (I (singlePairTrials n d)) := by
  apply finiteRow_run pub macros (singleCandidate n) body (6*n+17) cost (singleTrialValid i a b)
    good (singleAt i a b) I fit stable ?_ ?_ (singleCandidate_deterministic n) visit skip s m start
  · intro k z hi
    obtain ⟨_,h1,_,_,_,_,_,hc,hN⟩ := regs k z hi
    exact ⟨h1,hc,hN⟩
  · intro t u mu hi
    obtain ⟨r0,r1,r10,r11,r12,r14,r15,r18,_⟩ := regs t.val _ hi
    apply (singleCandidate_run pub macros u mu i a b t r0 r1 r10 r11 r12 r14 r15 r18
      (Fin.isLt _ |>.trans_le labels) (Fin.isLt _ |>.trans_le labels)).mono le_rfl
    rintro z ⟨src,dst,f,hl,hm⟩
    exact ⟨⟨src,dst⟩,f,hl,hm⟩

end RoutingISA.Owned

end BorderVNP
end Computability
end OAI
