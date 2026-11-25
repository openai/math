import OAI.Computability.BorderVNP.CubeISAOwnedAddress
import OAI.Computability.BorderVNP.CubeISAOwnedEndpoints
import OAI.Computability.BorderVNP.CubeISAOwnedFilter

/-! # Preparing and classifying a physical row candidate

These fixed native fragments return stable packet or endpoint addresses together
with the mathematical validity bit for the local counter. The row loop can
branch directly on register 40 and hand the prepared addresses to its callback.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Owned

open VPVNP.BurstRAM Cube Cube.Physical.Owned

/-- Decode the row counter, compute its global packet address, and test its
other-coordinate symbol digits. -/
def packetCandidate (n : ℕ) : Code := .seq preparePacket (packetFilter n)

/-- Prepare both endpoint addresses and test whether the pair is a singleton. -/
def singleCandidate (n : ℕ) : Code := .seq prepareSingle (singleFilter n)

/-- Exact opcode count for a complete packet candidate. -/
theorem packetCandidate_slots (n : ℕ) : (packetCandidate n).slots = 6*n+19 := by
  change 18+(packetFilter n).slots = _
  rw [packetFilter_slots]
  omega

/-- Exact opcode count for a complete singleton candidate. -/
theorem singleCandidate_slots (n : ℕ) : (singleCandidate n).slots = 6*n+17 := by
  change 14+(singleFilter n).slots = _
  rw [singleFilter_slots]
  omega

/-- Packet preparation and classification have a unique native execution. -/
theorem packetCandidate_deterministic (n : ℕ) : (packetCandidate n).deterministic = true := by
  change (true && (packetFilter n).deterministic) = true
  simp [packetFilter_deterministic]

/-- Singleton preparation and classification have a unique native execution. -/
theorem singleCandidate_deterministic (n : ℕ) : (singleCandidate n).deterministic = true := by
  change (true && (singleFilter n).deterministic) = true
  simp [singleFilter_deterministic]

/-- Both halves of the packet fragment reserve the low registers for the row loop. -/
theorem packetCandidate_protects (n : ℕ) : (packetCandidate n).protects 24 = true := by
  change (true && (packetFilter n).protects 24) = true
  simp [packetFilter_protects n (by decide : 24 ≤ 29)]

/-- Both halves of the singleton fragment reserve the low registers for the row loop. -/
theorem singleCandidate_protects (n : ℕ) : (singleCandidate n).protects 24 = true := by
  change (true && (singleFilter n).protects 24) = true
  simp [singleFilter_protects n (by decide : 24 ≤ 29)]

/-- The native packet fragment returns the actual validity bit, packet-bank
address, orientation, and stable numeric index. On a passing candidate,
`trialPacketIndex_eq` identifies this index with that of the physical packet. -/
theorem packetCandidate_run {n d blocks w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (r : Bank w) (m : Memory w) (i : Fin (n+1)) (pair : Symbols d)
    (t : Fin (packetTrials n d blocks)) {stride base : ℕ}
    (r0 : readings r 0 = 0) (r1 : readings r 1 = 1) (r2 : readings r 2 = 2)
    (r10 : readings r 10 = d) (r11 : readings r 11 = d*d)
    (r12 : readings r 12 = (d*d)^i.val) (r13 : readings r 13 = blocks)
    (r14 : readings r 14 = pair.val.1.val) (r15 : readings r 15 = pair.val.2.val)
    (r16 : readings r 16 = stride) (r17 : readings r 17 = base) (r18 : readings r 18 = t.val)
    (hs : 0 < stride)
    (bound : base + trialPacketIndex d ((d*d)^i.val) blocks pair.val.1.val pair.val.2.val t.val * stride < 2^w) :
    BoundedRun pub macros (packetCandidate n) r m (6*n+19) (fun z =>
      let k := trialPacketIndex d ((d*d)^i.val) blocks pair.val.1.val pair.val.2.val t.val
      z.reg 24 = base + k*stride ∧ z.reg 25 = t.val/blocks%2 ∧ z.reg 26 = k ∧
      z.reg 40 = (if packetTrialValid t then 1 else 0) ∧
      (∀ j : Reg, j.val < 24 → z.reg j = readings r j) ∧ z.mem = readings m) := by
  have hd : 0 < d := Nat.zero_lt_of_lt pair.val.1.isLt
  have hb : 0 < blocks := by
    by_contra! h
    have hz : blocks = 0 := by omega
    have ht := t.isLt
    simp [packetTrials,hz] at ht
  have prep := preparePacket_run pub macros r m r2 r10 r11 r12 r13 r14 r15 r16 r17 r18
    (pow_pos (Nat.mul_pos hd hd) _) hb hs bound
  unfold packetCandidate
  rw [show 6*n+19 = 18+(6*n+1) by omega]
  apply prep.seq
  rintro u mu ⟨h24,h25,h26,h29,keep,hm⟩
  have run := packetFilter_run pub macros u mu n ((keep 0 (by decide)).trans r0)
    ((keep 1 (by decide)).trans r1) ((keep 10 (by decide)).trans r10)
    ((keep 11 (by decide)).trans r11) h29 hd
  apply run.mono le_rfl
  rintro z ⟨h40,stable,mem⟩
  refine ⟨(stable 24 (by decide)).trans h24, (stable 25 (by decide)).trans h25,
    (stable 26 (by decide)).trans h26, ?_,fun j hj => (stable j (by omega)).trans (keep j hj),mem.trans hm⟩
  simpa only [strictDigits_iff_trial t] using h40

/-- The singleton fragment returns the true whole endpoint label codes and
the exact validity bit for the ordered row. It preserves the low loop registers
and all shared memory, on accepted and rejected candidates alike. -/
theorem singleCandidate_run {n d w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (r : Bank w) (m : Memory w) (i : Fin (n+1)) (a b : Fin d)
    (t : Fin (singlePairTrials n d))
    (r0 : readings r 0 = 0) (r1 : readings r 1 = 1) (r10 : readings r 10 = d)
    (r11 : readings r 11 = d^n) (r12 : readings r 12 = d^i.val)
    (r14 : readings r 14 = a.val) (r15 : readings r 15 = b.val) (r18 : readings r 18 = t.val)
    (srcFit : (finFunctionFinEquiv (singleOrderedPairs i a b t).val.1).val < 2^w)
    (dstFit : (finFunctionFinEquiv (singleOrderedPairs i a b t).val.2).val < 2^w) :
    BoundedRun pub macros (singleCandidate n) r m (6*n+17) (fun z =>
      let p := (singleOrderedPairs i a b t).val
      z.reg 24 = (finFunctionFinEquiv p.1).val ∧ z.reg 25 = (finFunctionFinEquiv p.2).val ∧
      z.reg 40 = (if singleTrialValid i a b t then 1 else 0) ∧
      (∀ j : Reg, j.val < 24 → z.reg j = readings r j) ∧ z.mem = readings m) := by
  have hd : 0 < d := Nat.zero_lt_of_lt a.isLt
  obtain ⟨src,dst⟩ := singleEndpointCodes i a b t
  have prep := prepareSingle_run pub macros r m r10 r11 r12 r14 r15 r18 (pow_pos hd _) (pow_pos hd _)
    (src ▸ srcFit) (dst ▸ dstFit)
  unfold singleCandidate
  rw [show 6*n+17 = 14+(6*n+3) by omega]
  apply prep.seq
  rintro u mu ⟨h24,h25,h29,h30,keep,hm⟩
  have run := singleFilter_run pub macros u mu n ((keep 0 (by decide)).trans r0)
    ((keep 1 (by decide)).trans r1) ((keep 10 (by decide)).trans r10)
    ((keep 14 (by decide)).trans r14) ((keep 15 (by decide)).trans r15) h29 h30 hd
  apply run.mono le_rfl
  rintro z ⟨h40,stable,mem⟩
  refine ⟨(stable 24 (by decide)).trans (h24.trans src.symm),
    (stable 25 (by decide)).trans (h25.trans dst.symm), ?_,
    fun j hj => (stable j (by omega)).trans (keep j hj),mem.trans hm⟩
  simpa only [commonDigits_iff_trial i a b t] using h40

end RoutingISA.Owned

end BorderVNP
end Computability
end OAI
