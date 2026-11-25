import OAI.Computability.BorderVNP.TeamContractionPaths

/-! # Weight-preserving reindexing of the capped RAM paths by team histories

The register replays may use claimed old words, while the physical checks recover the true
memory trace. Below the charged scheduling bound, each chronological accepting path extends
uniquely to all blocks, sorting exchanges, and predecessor fields. The placement of records
can be selected from the path, as it is for physically interleaved processor rows. -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP TeamRAM
open BurstRAM (Word)
open scoped BigOperators Classical

/-- Geometry and clock bounds of one team. The block capacity leaves enough idle ticks at
each handoff for the largest admissible burst. -/
structure Bounds (r I : ℕ) where
  /-- Tick block per processor. -/
  block : ℕ
  /-- Maximum burst length. -/
  burst : ℕ
  /-- Logical charged clock for the native path. -/
  ticks : ℕ
  /-- Maximum binary choices in any individual private instruction. -/
  privateClock : ℕ
  /-- There is at least one real processor. -/
  positive : 0 < r
  /-- All allowed ticks can be placed despite the worst-case idle suffixes. -/
  capacity : ticks ≤ r*(block-burst)
  /-- The literal, exterior and pin fields fit in the time-zero sorting array. -/
  headerSize : I ≤ r*(3*block)

variable {r I w : ℕ} {S : Type*}

/-- Height of one local power-of-two sorting block. -/
abbrev Bounds.height (b : Bounds r I) := Nat.clog 2 (4*b.block)

/-- The path can determine the physical interleaving, for example by the computed start
position and occupied length of each real processor's local record row. -/
abbrev Placement (b : Bounds r I) (w : ℕ) :=
  List (Event w) → Equiv.Perm (Fin (2^(b.height+Nat.clog 2 r)))

private theorem fits (M : MachineInput w S) (b : Bounds r M.inputSize) (es : List (Event w))
    (h : Within b.ticks b.burst b.privateClock es) :
    (TeamTranscript.accesses Event.action M.inputSize M.header es).length ≤ 2^(b.height+Nat.clog 2 r) := by
  have ht := (h.cost.trans b.capacity).trans (Nat.mul_le_mul_left r (Nat.sub_le ..))
  have hp := (TeamTranscript.probes_spec Event.action 1 es).1
  rw [TeamTranscript.accesses,List.length_append,TeamRecords.initialization,List.length_map,List.length_range]
  calc
    _ ≤ r*(3*b.block) + r*b.block := Nat.add_le_add b.headerSize (hp.trans ht)
    _ = 4*b.block*r := by ring
    _ ≤ 2^b.height * 2^Nat.clog 2 r := Nat.mul_le_mul
      (Nat.le_pow_clog (by decide) _) (Nat.le_pow_clog (by decide) _)
    _ = _ := (Nat.pow_add ..).symm

/-- Successful team histories are defined by the local instruction, block, sorting and
memory predicates. Native execution is reconstructed by the proof. -/
abbrev CheckedHistory (M : MachineInput w S) (b : Bounds r M.inputSize) (place : Placement b w) :=
  {t : TeamTranscript.History (Event w) (Word w) r b.height //
    let es := t.chunks.flatten
    t.Valid b.positive b.block Event.action M.inputSize M.header (place es) es ∧
    Local M.program M.start es ∧ Claims 1 es (t.records.drop M.inputSize) ∧
    Within b.ticks b.burst b.privateClock es }

private theorem unique_history (M : MachineInput w S) (b : Bounds r M.inputSize)
    (place : Placement b w) (p : NativePath M b.ticks b.burst b.privateClock) :
    ∃! t : TeamTranscript.History (Event w) (Word w) r b.height,
      t.Valid b.positive b.block Event.action M.inputSize M.header (place p.val) p.val :=
  TeamTranscript.existsUnique_history b.positive b.height b.block b.burst Event.action M.inputSize M.header
    (place p.val) p.val p.property.2.length (p.property.2.cost.trans b.capacity) (fits M b _ p.property.2)

private noncomputable def extend (M : MachineInput w S) (b : Bounds r M.inputSize) (place : Placement b w)
    (p : NativePath M b.ticks b.burst b.privateClock) : CheckedHistory M b place := by
  let h := unique_history M b place p
  let t := h.exists.choose
  have hv := h.exists.choose_spec
  have hpath := hv.2.1
  refine ⟨t,?_⟩
  change t.Valid _ _ _ _ _ (place t.chunks.flatten) t.chunks.flatten ∧ _
  rw [hpath]
  obtain ⟨hl,hc,_⟩ := execute_spec p.property.1
  exact ⟨hv,hl,(claims_of_history_iff hv (fits M b p.val p.property.2)).mpr hc,p.property.2⟩

private def recover (M : MachineInput w S) (b : Bounds r M.inputSize) (place : Placement b w)
    (t : CheckedHistory M b place) : NativePath M b.ticks b.burst b.privateClock :=
  ⟨t.val.chunks.flatten, by
    obtain ⟨hv,hl,hc,hw⟩ := t.property
    exact ⟨execute_iff.mpr ⟨hl,(claims_of_history_iff hv (fits M b _ hw)).mp hc,rfl⟩,hw⟩⟩

/-- The two maps reconstruct exactly the original choice-labeled accepting trace and its
unique validating history. Identical control destinations reached by different choices are
still separate paths. -/
noncomputable def pathEquivHistory (M : MachineInput w S) (b : Bounds r M.inputSize) (place : Placement b w) :
    NativePath M b.ticks b.burst b.privateClock ≃ CheckedHistory M b place where
  toFun := extend M b place
  invFun := recover M b place
  left_inv p := Subtype.ext (unique_history M b place p).exists.choose_spec.2.1
  right_inv t := by
    apply Subtype.ext
    let p := recover M b place t
    exact (unique_history M b place p).unique (unique_history M b place p).exists.choose_spec t.property.1

instance finiteCheckedHistory (M : MachineInput w S) (b : Bounds r M.inputSize) (place : Placement b w) :
    Finite (CheckedHistory M b place) := Finite.of_equiv _ (pathEquivHistory M b place)

/-- Weighted sum over all successful local typed histories. -/
noncomputable def historyValue (M : MachineInput w S) (b : Bounds r M.inputSize) (place : Placement b w) : ℤ :=
  letI := Fintype.ofFinite (CheckedHistory M b place)
  ∑ t : CheckedHistory M b place, t.val.weight (Sign.value ∘ Event.sign)

/-- Summing local signs over the entire typed histories gives exactly the paper's
signed computation value up to its charged cutoff, with no path multiplicity factor. -/
theorem historyValue_eq_native (M : MachineInput w S) (b : Bounds r M.inputSize) (place : Placement b w) :
    historyValue M b place = nativeValue M b.ticks b.burst b.privateClock := by
  unfold historyValue nativeValue
  apply Finset.sum_equiv (pathEquivHistory M b place).symm (by simp)
  intro t _
  exact t.property.1.weight_eq (Sign.value ∘ Event.sign)

/-- The paper's actual exponents meet the numerical assumptions on the path bijection
and weighted finite sum, uniformly in positive team size. -/
theorem eventually_bounds {ξ : ℝ} (hξ : 0 < ξ) (hξ' : ξ < 3/2) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ r I, 0 < r → I ≤ r*(3*TeamScales.block ξ n) →
      ∃ b : Bounds r I, b.block = TeamScales.block ξ n ∧ b.burst = TeamScales.width n (1/2) ∧
        b.ticks = TeamScales.ticks ξ r n ∧ b.privateClock = n^25 := by
  filter_upwards [TeamScales.eventually_ticks_fit hξ hξ'] with n hn
  intro r I hr hi
  exact ⟨⟨_,_,_,_,hr,(hn r hr).le,hi⟩,rfl,rfl,rfl,rfl⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
