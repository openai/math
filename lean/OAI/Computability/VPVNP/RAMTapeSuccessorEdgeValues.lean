import OAI.Computability.VPVNP.RAMTapeSuccessorEdge

/-!
# Successor values returned by the physical edge check

For a present edge the validity flag recognizes the entire canonical encoding.
The running bit, cumulative cost, state and record on a valid return agree with
the typed message. At a missing edge the only valid input is the zero clamp.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SuccessorEdge

open BurstRAM RAMSerialization Successor

variable {w cap : ℕ}

private theorem zeroArray {k : ℕ} :
    (arrayBits k w).symm (fun _ => false) = fun _ => (0 : Word w) := by
  apply (arrayBits k w).injective
  rw [Equiv.apply_symm_apply]
  funext j
  obtain ⟨⟨i, t⟩, rfl⟩ := finProdFinEquiv.surjective j
  exact ((arrayBits_at _ i t).trans (RAMSerialization.wordBits_zero t)).symm

/-- The returning validity bit on a present edge agrees with successful decoding. -/
theorem present_verdict_iff (hw : 2 ≤ w) (hc : cap < 2^w) (s : Stacks Port)
    (bits : Fin (8*w) → Bool) (suffix : List Bool) :
    edgeResult s true bits ⟨cap, hc⟩ suffix .verdict = true :: s .verdict ↔
      ∃ x, (successorFormat hw hc).decode bits = some x := by
  let a := (arrayBits 8 w).symm bits
  change (valid true (wordTags a) (decide ((a 1).val ≤ cap)) :: _) = _ ↔ _
  simp only [List.cons.injEq, and_true, valid_present_iff hw hc, successor_decode_iff, Format.encode]
  apply exists_congr
  intro x
  exact ((arrayBits 8 w).eq_symm_apply).trans eq_comm

private theorem encodedRecord (hw : 2 ≤ w) (hc : cap < 2^w) (x : RAMSerialization.Successor w cap) :
    recordBits ((successorFormat hw hc).words x) = List.ofFn ((recordFormat hw).encode x.lastRecord) := by
  rw [SuccessorFields.raw_eq_flatten_words, Format.encode, Equiv.symm_apply_apply]
  change (List.ofFn fun i : Fin 5 => BurstRAM.wordBits
    (Fin.append _ ((recordFormat hw).words x.lastRecord) (Fin.natAdd 3 i))).flatten = _
  simp only [Fin.append_right]

/-- On a successful present-edge check, the saved cost includes the possible
endpoint value `cap`. A halt supplies the zero state word. -/
theorem present_values (hw : 2 ≤ w) (hc : cap < 2^w) (s : Stacks Port)
    (bits : Fin (8*w) → Bool) (suffix : List Bool) (x : RAMSerialization.Successor w cap)
    (hx : (successorFormat hw hc).decode bits = some x) :
    let out := edgeResult s true bits ⟨cap, hc⟩ suffix
    out .verdict = true :: s .verdict ∧ out .running = x.state.isSome :: s .running ∧
      out (.word 1) = BurstRAM.wordBits
        (⟨x.cost.val, (Nat.le_of_lt_succ x.cost.isLt).trans_lt hc⟩ : Word w) ∧
      out (.word 2) = BurstRAM.wordBits (x.state.getD 0) ∧
      out .record = List.ofFn ((recordFormat hw).encode x.lastRecord) ++ s .record := by
  refine ⟨(present_verdict_iff hw hc s bits suffix).mpr ⟨x, hx⟩, ?_⟩
  have ha : (arrayBits 8 w).symm bits = (successorFormat hw hc).words x := by
    rw [(successor_decode_iff hw hc bits x).mp hx, Format.encode, Equiv.symm_apply_apply]
  simp only [edgeResult, ha, encodedRecord]
  refine ⟨?_, rfl, rfl, trivial⟩
  cases x with
  | mk state cost last => cases state <;> rfl

/-- On a missing edge the verdict bit tests every incident bit against zero. -/
theorem clamp_verdict_iff (s : Stacks Port) (bits : Fin (8*w) → Bool) (bound : Word w)
    (suffix : List Bool) :
    edgeResult s false bits bound suffix .verdict = true :: s .verdict ↔ bits = fun _ => false := by
  simp only [edgeResult, List.cons.injEq, and_true, valid_clamp_iff]
  rw [← zeroArray]
  exact (arrayBits 8 w).symm.injective.eq_iff

/-- The only valid missing field supplies eight zero words, a zero record
of exactly five word widths, and the nonrunning flag before site normalization. -/
theorem clamped_values (s : Stacks Port) (bound : Word w) (suffix : List Bool) :
    let out := edgeResult s false (fun _ => false) bound suffix
    out .verdict = true :: s .verdict ∧ out .running = false :: s .running ∧
      (∀ i, out (.word i) = BurstRAM.wordBits (0 : Word w)) ∧
      out .record = List.replicate (5*w) false ++ s .record := by
  refine ⟨(clamp_verdict_iff s _ bound suffix).mpr rfl, ?_⟩
  simp only [edgeResult, zeroArray]
  refine ⟨rfl, fun _ => True.intro, ?_⟩
  have h := SuccessorFields.raw_eq_flatten_words (fun _ : Fin (5*w) => false)
  rw [zeroArray, List.ofFn_const] at h
  exact congrArg (· ++ s .record) h.symm

end RAMTape.SuccessorEdge

end VPVNP
end Computability
end OAI
