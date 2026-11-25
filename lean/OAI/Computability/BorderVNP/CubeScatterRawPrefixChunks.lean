import OAI.Computability.BorderVNP.CubeISAOwnedVertexCapacity
import OAI.Computability.BorderVNP.CubeScatterTrialPrefix
import OAI.Computability.BorderVNP.CubeScatterSelectorPrefix

/-! # Reconstructing the physical selector prefix from the native trial reads

A valid packet trial consumes one fixed-width chunk at the compact rank of
that trial. An invalid trial consumes zero bits. These chunks reconstruct
the entire received selector stream and its decoding, also for width zero.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Scatter

open Physical Physical.Owned RoutingISA.OwnedVertex Tally VPVNP.BurstRAM

variable {n d blocks w : ℕ}

/-- Bits read from the received list at a fixed start and width. -/
def rawChunk (raw : List Bool) (off width : ℕ) : List Bool := (raw.drop off).take width

/-- A completely represented chunk has the native read width. -/
theorem rawChunk_length (raw : List Bool) (off width : ℕ) (fits : off+width ≤ raw.length) :
    (rawChunk raw off width).length = width := by
  simp only [rawChunk,List.length_take,List.length_drop]
  omega

/-- The chunk is present at the physical shared-row base plus its exact offset. -/
theorem Resident.chunk {src : Set ℕ} {m : Memory w} {base : ℕ} {raw : List Bool}
    (res : Resident src m base raw) (off width : ℕ) (bound : off ≤ raw.length) :
    Resident src m (base+off) (rawChunk raw off width) := by
  let preBits := raw.take off
  let suffix := raw.drop off
  let endWords := suffix.drop width
  have split : preBits ++ rawChunk raw off width ++ endWords = raw := by
    simp only [preBits,rawChunk,endWords,suffix,List.append_assoc,List.take_append_drop]
  have slice := Resident.slice preBits (rawChunk raw off width) endWords (split ▸ res)
  simpa only [preBits,List.length_take,Nat.min_eq_left bound] using slice

/-- The exact compact selector interval of one native packet trial. -/
def selectorChunk (K h : ℕ) (raw : List Bool) (i : Fin (n+1)) (pair : Symbols d)
    (t : Fin (packetTrials n d blocks)) : List Bool :=
  rawChunk raw (selectedPrefix (blocks := blocks) i pair t.val * selectorWidth n K h) (selectorWidth n K h)

/-- Every valid trial's selector interval is in range in the received fixed-width row. -/
theorem selectorChunk_fits (K h : ℕ) (raw : List Bool) (i : Fin (n+1)) (pair : Symbols d)
    (len : raw.length = 2*blocks*(d.choose 2)^n*selectorWidth n K h)
    (t : Fin (packetTrials n d blocks)) (ht : packetTrialValid t) :
    selectedPrefix (blocks := blocks) i pair t.val * selectorWidth n K h + selectorWidth n K h ≤ raw.length := by
  rw [len,← Nat.succ_mul]
  exact Nat.mul_le_mul_right _ (selectedPrefix_capacity i pair t ht)

/-- The compact counter advances exactly on valid native trials. -/
theorem selectedPrefix_next (i : Fin (n+1)) (pair : Symbols d) (t : Fin (packetTrials n d blocks)) :
    selectedPrefix (blocks := blocks) i pair (t.val+1) = selectedPrefix (blocks := blocks) i pair t.val +
      (if packetTrialValid t then 1 else 0) := by
  unfold selectedPrefix
  rw [Finset.sum_range_succ]
  by_cases good : packetTrialValid t <;> simp [packetAtNat,packetTrial,t.isLt,good]

/-- The actual common prefix of a row is fixed by the chunks consumed at all
valid native trials. The accumulator skips invalid trials in their native order. -/
theorem raw_eq_commonSelectors_of_chunks {K h : ℕ} (u : Packet n d blocks → Selector n K h)
    (i : Fin (n+1)) (pair : Symbols d) (raw : List Bool)
    (len : raw.length = 2*blocks*(d.choose 2)^n*selectorWidth n K h)
    (chunks : ∀ (t : Fin (packetTrials n d blocks)) (ok : packetTrialValid t),
      selectorChunk K h raw i pair t = selectorStream (u (packetRowEquiv i pair ⟨t,ok⟩).val)) :
    raw = commonSelectors u i pair := by
  let emit (t : Fin (packetTrials n d blocks)) := (packetTrial i pair t).toList.flatMap (selectorStream ∘ u)
  let off (k : ℕ) := selectedPrefix (blocks := blocks) i pair k * selectorWidth n K h
  have pre (k : ℕ) (hk : k ≤ packetTrials n d blocks) : raw.take (off k) = trialPrefix emit k := by
    induction k with
    | zero => simp [off,selectedPrefix,trialPrefix]
    | succ k ih =>
      let t : Fin (packetTrials n d blocks) := ⟨k,hk⟩
      rw [show k+1 = t.val+1 from rfl,trialPrefix_step emit t]
      by_cases ok : packetTrialValid t
      · have inc : off (t.val+1) = off t.val + selectorWidth n K h := by
          simp only [off,selectedPrefix_next,ite_eq_left ok,Nat.add_mul,Nat.one_mul]
        rw [inc,List.take_add,ih (by omega)]
        change trialPrefix emit t.val ++ selectorChunk K h raw i pair t = trialPrefix emit t.val ++ emit t
        rw [chunks t ok]
        simp only [emit,packetTrial,dite_eq_left ok,Option.toList_some,List.flatMap_cons,List.flatMap_nil,
          List.append_nil,Function.comp_apply]
      · have skip : off (t.val+1) = off t.val := by simp only [off,selectedPrefix_next,ite_eq_right ok,Nat.add_zero]
        rw [skip,ih (by omega)]
        change trialPrefix emit t.val = trialPrefix emit t.val ++ emit t
        simp only [emit,packetTrial,dite_eq_right ok,Option.toList_none,List.flatMap_nil,List.append_nil]
  have all := pre _ le_rfl
  rw [show off (packetTrials n d blocks) = raw.length from (congrArg (· * selectorWidth n K h)
    (selectedPrefix_end i pair)).trans len.symm,List.take_length,trialPrefix_full] at all
  simpa only [commonSelectors,packetVisits,List.filterMap_eq_flatMap_toList,List.flatMap_assoc,emit] using all

/-- Per-trial physical witnesses, including any observed packet-bank property,
glue to a single selector function on this row. Extending it to packets in
other rows uses the same valid trial ordinal, even when there are no selectors. -/
theorem exists_selectors_of_chunks {K h : ℕ} (i : Fin (n+1)) (pair : Symbols d) (raw : List Bool)
    (len : raw.length = 2*blocks*(d.choose 2)^n*selectorWidth n K h)
    (P : Packet n d blocks → Selector n K h → Prop)
    (chunks : ∀ (t : Fin (packetTrials n d blocks)) (ok : packetTrialValid t), ∃ x : Selector n K h,
      selectorChunk K h raw i pair t = selectorStream x ∧ P (packetRowEquiv i pair ⟨t,ok⟩).val x) :
    ∃ u : Packet n d blocks → Selector n K h, raw = commonSelectors u i pair ∧
      ∀ p : {p : Packet n d blocks // p.1.1 i = pair}, P p.val (u p.val) := by
  classical
  choose x hit holds using chunks
  let rank (p : Packet n d blocks) := (packetRowEquiv i (p.1.1 i)).symm ⟨p,rfl⟩
  let u (p : Packet n d blocks) := x (rank p).val (rank p).property
  have here (t : {t : Fin (packetTrials n d blocks) // packetTrialValid t}) :
      u (packetRowEquiv i pair t).val = x t.val t.property := by
    have back : rank (packetRowEquiv i pair t).val = t := (packetRowEquiv i pair).symm_apply_apply t
    exact congrArg (fun z => x z.val z.property) back
  refine ⟨u,raw_eq_commonSelectors_of_chunks u i pair raw len (fun t ok => (hit t ok).trans
    (congrArg selectorStream (here ⟨t,ok⟩)).symm),?_⟩
  intro p
  obtain ⟨t,rfl⟩ := (packetRowEquiv i pair).surjective p
  rw [here]
  exact holds t.val t.property

/-- Accepted per-trial chunks make the literal row decoder succeed on the whole incoming prefix. -/
theorem decodeSelectors_of_chunks {K h : ℕ} (i : Fin (n+1)) (pair : Symbols d) (raw : List Bool)
    (len : raw.length = 2*blocks*(d.choose 2)^n*selectorWidth n K h)
    (chunks : ∀ (t : Fin (packetTrials n d blocks)), packetTrialValid t → ∃ x : Selector n K h,
      selectorChunk K h raw i pair t = selectorStream x) :
    (decodeSelectors n K h (packetVisits blocks i pair).length raw).isSome := by
  obtain ⟨u,rfl,_⟩ := exists_selectors_of_chunks i pair raw len (fun _ _ => True)
    (fun t ok => (chunks t ok).imp (fun _ eq => ⟨eq,trivial⟩))
  rw [commonSelectors_decode]
  rfl


/-- The native trial checks over all strict rows determine exactly one global
selector tuple, including when the declared alphabet has no strict pairs. -/
theorem unique_selectors_of_chunks {K h : ℕ} (i : Fin (n+1)) (raw : Symbols d → List Bool)
    (len : ∀ pair, (raw pair).length = 2*blocks*(d.choose 2)^n*selectorWidth n K h)
    (chunks : ∀ pair (t : Fin (packetTrials n d blocks)), packetTrialValid t → ∃ x : Selector n K h,
      selectorChunk K h (raw pair) i pair t = selectorStream x) :
    ∃! u : Packet n d blocks → Selector n K h, ∀ pair, raw pair = commonSelectors u i pair :=
  (validPrefixes_iff_existsUnique i raw).mp (fun pair => decodeSelectors_of_chunks i pair (raw pair)
    (len pair) (chunks pair))

end Cube.Scatter

end BorderVNP
end Computability
end OAI
