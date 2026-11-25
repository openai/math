import OAI.Computability.BorderVNP.CrossingCellBoxRecords

/-!
# Sparse copies of a local row into a fixed-stride bank

The incident cable lanes of a site can have different copy strides. A
single sparse equality record per fixed one-copy lane gathers them into
rows of a common stride. All temporary bits are forced, so staging neither
changes the path multiplicity nor replicates a box description per copy.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.CellBox

open CellSparse

/-- The location of one lane in each consecutive staged row. -/
def stagePort {d : ℕ} (base : ℕ) (k : Fin d) : Port := ⟨base + k.val, d, 1⟩

/-- Copy the lane into every occurrence with one strided equality record. -/
def stageRecords {d : ℕ} (copies base : ℕ) (src : Fin d → Port) : List Record :=
  List.ofFn fun k => .equal copies 1 (src k) (stagePort base k)

/-- The public record count is the fixed one-copy lane count. -/
theorem stageRecords_length {d : ℕ} (copies base : ℕ) (src : Fin d → Port) :
    (stageRecords copies base src).length = d := by simp [stageRecords]

private theorem stagePort_addr {d : ℕ} (base i : ℕ) (k : Fin d) :
    (stagePort base k).atBit i 0 = base + (i*d+k.val) := by
  change base + k.val + i*d + 0*1 = _
  omega

/-- Checking the actual sparse equality records is precisely the assertion
that every staged bit equals its source. -/
theorem stageRecords_valid_iff {d copies : ℕ} (base : ℕ) (src : Fin d → Port)
    (boxes : List (List Factor)) (bank : ℕ → Bool) :
    (∀ r ∈ stageRecords copies base src, r.Valid boxes bank) ↔
      ∀ (i : Fin copies) (k : Fin d), bank (base + (i.val*d+k.val)) = bank ((src k).atBit i.val 0) := by
  constructor
  · intro h i k
    have hv := h (.equal copies 1 (src k) (stagePort base k)) (List.mem_ofFn.mpr ⟨k,rfl⟩)
    simpa only [stagePort_addr] using (hv i.val i.isLt 0 (by decide)).symm
  · intro h r hr
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hr
    intro i hi l hl
    have hzero : l = 0 := by omega
    subst l
    simpa only [stagePort_addr] using (h ⟨i,hi⟩ k).symm

/-- Adjoin the unique canonical row-major staging bank after the old cell storage. -/
def stageBank {d copies : ℕ} (old : ℕ → Bool) (base : ℕ) (src : Fin d → Port) (t : ℕ) : Bool :=
  if t < base then old t else
    packedBank (copies := copies) (fun i k => old ((src k).atBit i.val 0)) (t-base)

/-- The appended bank respects every strided lane equality and preserves the old prefix. -/
theorem stageBank_valid {d copies : ℕ} (old : ℕ → Bool) (base : ℕ) (src : Fin d → Port)
    (hsrc : ∀ (i : Fin copies) (k : Fin d), (src k).atBit i.val 0 < base)
    (boxes : List (List Factor)) :
    (∀ t < base, stageBank (copies := copies) old base src t = old t) ∧
    ∀ r ∈ stageRecords copies base src, r.Valid boxes (stageBank (copies := copies) old base src) := by
  refine ⟨fun t ht => by simp [stageBank, ht], (stageRecords_valid_iff ..).mpr ?_⟩
  intro i k
  simp [stageBank, hsrc i k, packedBank_read]

/-- The new assignment is uniquely determined throughout the allocated
prefix and all `copies * d` appended bits. -/
theorem stageBank_unique {d copies : ℕ} (old bank : ℕ → Bool) (base : ℕ) (src : Fin d → Port)
    (hsrc : ∀ (i : Fin copies) (k : Fin d), (src k).atBit i.val 0 < base)
    (hold : ∀ t < base, bank t = old t) (boxes : List (List Factor))
    (hvalid : ∀ r ∈ stageRecords copies base src, r.Valid boxes bank) :
    ∀ t < base + copies*d, bank t = stageBank (copies := copies) old base src t := by
  intro t ht
  by_cases h : t < base
  · simp [stageBank, h, hold t h]
  · let u : Fin (copies*d) := ⟨t-base, by omega⟩
    obtain ⟨⟨i,k⟩, hik⟩ := finProdFinEquiv.surjective u
    have hi : i.val*d+k.val = t-base := by
      simpa [u, Nat.add_comm, Nat.mul_comm] using congrArg Fin.val hik
    have he : t = base + (i.val*d+k.val) := by omega
    have hv := (stageRecords_valid_iff base src boxes bank).mp hvalid i k
    rw [he, hv, hold _ (hsrc i k)]
    simp [stageBank, packedBank_read]

end Crossing.CellBox

end BorderVNP
end Computability
end OAI
