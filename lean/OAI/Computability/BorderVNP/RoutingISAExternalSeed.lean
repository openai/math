import OAI.Computability.BorderVNP.RoutingISAExternalSeedRead

/-! # Native seed-prefix execution and memory image -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.ExternalSeed

open VPVNP.BurstRAM DiagonalResidueRAM Packing.Directory.ISA CompactMachine

variable {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}

/-- The physical prefix invariant, measured in processed boundary words. -/
structure At (initial : Bank w) (original : Memory w) (xs : List Bool) (src dst i : ℕ) (z : NatState) : Prop
    extends Frame initial src xs.length z where
  /-- Number of source bits already processed. -/
  index : z.reg 6 = i
  /-- Next free destination address. -/
  cursor : z.reg 20 = dst+12*i
  /-- Exact completed records, with the original memory everywhere else. -/
  memory : z.mem = readings (putWords original dst (recordPrefix w xs i))

/-- The next reverse source read is still the original word, even after the prefix stores. -/
theorem source_unchanged {initial s : Bank w} {m original : Memory w} {src dst i : ℕ}
    {xs : List Bool} (h : At initial original xs src dst i (.ofWords s m)) (hi : i < xs.length)
    (separate : CompactWrite.Disjoint src xs.length dst (12*xs.length)) :
    m (src+(xs.length-i-1)) = original (src+(xs.length-i-1)) := by
  apply Fin.ext
  have e := congrFun h.memory (src+(xs.length-i-1))
  change _ = (putWords original dst (recordPrefix w xs i) _).val at e
  rw [putWords_outside] at e
  · exact e
  · rw [length_prefix xs hi.le]
    rcases separate with left | right <;> omega

/-- One successful native iteration consumes one reverse input bit and appends its actual record. -/
theorem step_run {initial s : Bank w} {m original : Memory w} {src dst i : ℕ} {xs : List Bool}
    (h : At initial original xs src dst i (.ofWords s m)) (hi : i < xs.length)
    (separate : CompactWrite.Disjoint src xs.length dst (12*xs.length))
    (srcFit : src+xs.length ≤ 2^w) (dstFit : dst+12*xs.length < 2^w)
    (value : (original (src+(xs.length-i-1))).val = xs[xs.length-i-1].toNat) :
    BoundedRun pub macros step s m step.slots (At initial original xs src dst (i+1)) := by
  let bit := xs[xs.length-i-1]
  let a := dst+12*i
  have live : (m (src+(xs.length-i-1))).val = bit.toNat := (source_unchanged h hi separate) ▸ value
  obtain ⟨es,t,readRun,cost,f,index,digit,cursor⟩ :=
    read_run (pub := pub) (macros := macros) bit h.toFrame hi h.index srcFit live
  have hw : 1 < 2^w := f.one.symm.trans_lt (t 1).isLt
  have regOne : t 1 = word w 1 := Fin.ext (f.one.trans (word_val w 1 hw).symm)
  have regZero : t 0 = word w 0 := Fin.ext (f.zero.trans (word_val w 0 (by omega)).symm)
  have address : t 20 = word w a := by
    rw [cursor]
    exact Fin.ext (h.cursor.trans (word_val w a (by dsimp [a]; omega)).symm)
  have fit : a+recordRegs.length < 2^w := by change dst+12*i+12 < 2^w; omega
  obtain ⟨fs,push,cost'⟩ := pushWords_runs pub macros recordRegs t m a address regOne fit (by decide)
  rw [recordRegs_map t bit regZero regOne digit] at push
  have mem : m = putWords original dst (recordPrefix w xs i) := funext fun j => Fin.ext (congrFun h.memory j)
  have updated : putWords m a ((literalRecord bit).map (fun b => word w b.toNat)) =
      putWords original dst (recordPrefix w xs (i+1)) := by
    rw [prefix_succ xs hi, putWords_append, length_prefix xs hi.le, ← mem]
  rw [updated] at push
  refine ⟨_,_,_,readRun.seq push,?_,?_⟩
  · rw [show traceCost (es++fs) = traceCost es + traceCost fs from VPVNP.RAMBuckets.cost_append .., cost']
    change traceCost es + 25 ≤ read.slots + 25
    omega
  · have keep (j : Reg) (hj : j ≠ 20) : (Function.update t 20 (word w (a+recordRegs.length)) j).val =
        (t j).val := congrArg Fin.val (Function.update_of_ne hj ..)
    refine ⟨⟨(keep 0 (by decide)).trans f.zero, (keep 1 (by decide)).trans f.one,
      (keep 3 (by decide)).trans f.source, (keep 4 (by decide)).trans f.length,
      (keep 7 (by decide)).trans f.saved, fun j hj hn => (keep j hn).trans (f.keep j hj hn)⟩,
      (keep 6 (by decide)).trans index,?_,rfl⟩
    change (Function.update t 20 (word w (a+recordRegs.length)) 20).val = dst+12*(i+1)
    rw [Function.update_self, word_val _ _ fit]
    change dst+12*i+12 = dst+12*(i+1)
    omega

/-- The fixed entry routine initializes the scan from the caller's three argument registers. -/
theorem setup_run (s : Bank w) (m : Memory w) (xs : List Bool) {src dst : ℕ}
    (hw : 0 < w) (base : (s 3).val = src) (count : (s 4).val = xs.length)
    (dest : (s 5).val = dst) :
    BoundedRun pub macros setup s m setup.slots (At s m xs src dst 0) := by
  have one := Nat.one_lt_two_pow hw.ne'
  have safe : setup.fixedSafe w (readings pub) (.ofWords s m) := by
    simp (config := {decide := true}) [setup, Code.block, Code.fixedSafe, Code.safeReadOnly, one]
  apply (setup.runFixed pub macros s m safe).mono le_rfl
  rintro _ rfl
  constructor
  · constructor
    all_goals try simp (config := {decide := true}) [setup, Code.block, Code.fixedEval, Code.evalNat,
      NatState.ofWords, readings, base, count]
    intro r hr hn
    have ne (j : Reg) (hj : ¬ Preserved j) : r ≠ j := fun e => hj (e ▸ hr)
    simp [readings, Function.update_of_ne, hn, ne 0 (by unfold Preserved; decide), ne 1 (by unfold Preserved; decide),
      ne 6 (by unfold Preserved; decide), ne 7 (by unfold Preserved; decide)]
  · simp (config := {decide := true}) [setup, Code.block, Code.fixedEval, Code.evalNat]
  · simpa (config := {decide := true}) [setup, Code.block, Code.fixedEval, Code.evalNat, NatState.ofWords,
      readings] using dest
  · rfl

/-- The native writer emits the reverse-chronological external records and restores all
caller registers outside the six documented scratch registers. -/
theorem writer_runs (s : Bank w) (m : Memory w) (xs : List Bool) {src dst : ℕ}
    (hw : 0 < w) (base : (s 3).val = src) (count : (s 4).val = xs.length)
    (dest : (s 5).val = dst) (source : CompactWrite.Source m src xs)
    (separate : CompactWrite.Disjoint src xs.length dst (12*xs.length))
    (srcFit : src+xs.length ≤ 2^w) (dstFit : dst+12*xs.length < 2^w) :
    ∃ es t, Runs pub macros writer s m es t
      (putWords m dst ((externalRecords xs).map (fun b => word w b.toNat))) ∧
      traceCost es ≤ setup.slots + (step.slots+1)*xs.length + 2 ∧
      ∀ r, Preserved r → t r = s r := by
  obtain ⟨es,u,mu,r,ct,h⟩ := setup_run (pub := pub) (macros := macros) s m xs hw base count dest
  let I := At s m xs src dst
  have loop := run_counted_loop pub macros 6 4 step xs.length step.slots I
    (fun _ _ f => ⟨f.index, f.length⟩)
    (fun i hi _ _ f => step_run f hi separate srcFit dstFit (source _ (by omega)))
    0 (Nat.zero_le _) u mu h
  obtain ⟨fs,t,mt,loop,cost,final⟩ := loop
  let result := Function.update t 20 (t 7)
  have last : Runs pub macros (.copy 20 7) t mt [tick w] result mt := Runs.localStep _ rfl rfl
  have image : mt = putWords m dst ((externalRecords xs).map (fun b => word w b.toNat)) := by
    have all : recordPrefix w xs xs.length = (externalRecords xs).map (fun b => word w b.toNat) := by
      simp [recordPrefix, externalRecords, List.take_of_length_le (show xs.reverse.length ≤ xs.length by simp)]
    apply funext; intro j; apply Fin.ext
    change (NatState.ofWords t mt).mem j = readings (putWords m dst _) j
    rw [← all]
    exact congrFun final.memory j
  rw [← image]
  refine ⟨_,result,r.seq (loop.seq last),?_,?_⟩
  · simp only [VPVNP.RAMBuckets.cost_append]
    change traceCost es + (traceCost fs + 1) ≤ _
    rw [Nat.sub_zero, Nat.mul_comm xs.length] at cost
    omega
  · intro j hj
    by_cases he : j = 20
    · subst j
      exact (Function.update_self ..).trans (Fin.ext final.saved)
    · exact (Function.update_of_ne he ..).trans (Fin.ext (final.keep j hj he))

end RoutingISA.ExternalSeed

end BorderVNP
end Computability
end OAI
