import OAI.Computability.VPVNP.CompressorBundleTableReadback
import OAI.Computability.VPVNP.CompressorRecordsPortRankScan

/-!
# Array layout for gathering keys and ranking every original arc

The rank pass shares the append pass's owner, stride, and count parameters.
It reads the classifier's key column and the new rectangular key rows. Static
interval bounds verify its memory frame even for probes in the padding at the
end of a short thick row.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.BundleGather

open BurstRAM Compression.PackingData PortRankRAM

variable {w A n d c : ℕ}

/-- Construct the six operands of the bundle ranking pass from the inherited parameters and the
supplied key, output and destination words. -/
def rankPublic (p : Fin 6 → Word w) (keys out dest : Word w) : Fin 6 → Word w :=
  ![p 1,keys,out,p 4,p 3,dest]

/-- Two disjoint half-open intervals, in either physical order. -/
def separated (base₁ size₁ base₂ size₂ : ℕ) : Prop :=
  base₁+size₁ ≤ base₂ ∨ base₂+size₂ ≤ base₁

variable (p : Fin 6 → Word w) (keys out widths dest : Word w)
local notation "T" => table A n d c p keys out widths
local notation "R" => rankPublic p keys out dest

/-- The materialized key rectangle must preserve the owner/count columns.
The rank destination column is separate from all four arrays read by ranking. -/
structure RankLayout (p : Fin 6 → Word w) (keys out dest : Word w) (A buckets : ℕ) : Prop where
  keepOwners : separated (p 1).val A out.val (buckets*(p 4).val)
  keepCounts : separated (p 3).val buckets out.val (buckets*(p 4).val)
  destFits : dest.val + A ≤ 2^w
  owners : separated (p 1).val A dest.val A
  counts : separated (p 3).val buckets dest.val A
  keys : separated keys.val A dest.val A
  rows : separated out.val (buckets*(p 4).val) dest.val A

theorem separated.outside {a m b n i : ℕ} (h : separated a m b n) (hi : i < m) :
    a+i < b ∨ b+n ≤ a+i := by unfold separated at h; omega

theorem rank_start (reg : (T).Layout) (mem : Memory w) (i : Word w)
    (hu : (ownerAt p mem i).val < 2*(n*d)) :
    (start R mem i).val = (T).outStart (ownerAt p mem i).val := by
  let u := ownerAt p mem i
  have fit := reg.outputFits
  change out.val + (2*(n*d))*(p 4).val ≤ 2^w at fit
  change (out + u*p 4).val = out.val+u.val*(p 4).val
  rw [Fin.val_add, Fin.val_mul, Nat.add_mod_mod]
  by_cases h : (p 4).val = 0
  · simp [h,Nat.mod_eq_of_lt out.isLt]
  · have hh := Nat.mul_le_mul_right (p 4).val (Nat.succ_le_of_lt hu)
    rw [Nat.succ_mul] at hh
    exact Nat.mod_eq_of_lt (by change u.val*_+_ ≤ _ at hh; omega)

theorem rank_row_fits (reg : (T).Layout) (u : ℕ) (hu : u < 2*(n*d)) :
    (T).outStart u + pieceCount d c ≤ 2^w := by
  have fit := reg.outputFits
  have cap := reg.motifFits
  have hh := Nat.mul_le_mul_right (p 4).val (Nat.succ_le_of_lt hu)
  rw [Nat.succ_mul] at hh
  change out.val + (2*(n*d))*(p 4).val ≤ 2^w at fit
  change pieceCount d c ≤ (p 4).val at cap
  change out.val+u*(p 4).val+pieceCount d c ≤ 2^w
  omega

theorem rank_regions (reg : (T).Layout) (sep : RankLayout p keys out dest A (2*(n*d)))
    (pre : RowRegions p) (hA : (p 0).val = A) (hB : (p 2).val = n*d+n*d)
    (mem : Memory w) (legal : ∀ i : Word w, i.val < A → (ownerAt p mem i).val < 2*(n*d)) :
    Regions R mem (pieceCount d c) A := by
  constructor
  · exact sep.destFits
  · intro j hj v hv
    let i := Fin.ofNat (2^w) j
    let u := ownerAt p mem i
    have hf := sep.destFits
    have hi : i.val = j := Nat.mod_eq_of_lt (by omega)
    have hu : u.val < 2*(n*d) := legal i (hi ▸ hj)
    change v ∈ [p 1+i,keys+i,p 3+u] ++ (List.range (pieceCount d c)).map (fun z ↦ start R mem i + Fin.ofNat _ z) at hv
    change v.val < dest.val ∨ dest.val+A ≤ v.val
    rcases List.mem_append.mp hv with h | h
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl | rfl | rfl
      · have hb := pre.ownersBeforeCounts
        rw [Fin.val_add,hi,Nat.mod_eq_of_lt (by have := (p 3).isLt; omega)]
        exact sep.owners.outside hj
      · have hb := reg.keysFit
        change keys.val+A ≤ 2^w at hb
        rw [Fin.val_add,hi,Nat.mod_eq_of_lt (by omega)]
        exact sep.keys.outside hj
      · have hb := pre.countsBeforeRows
        rw [Fin.val_add,Nat.mod_eq_of_lt (by have := (p 5).isLt; omega)]
        exact sep.counts.outside hu
    · obtain ⟨z,hz,rfl⟩ := List.mem_map.mp h
      have hz' := List.mem_range.mp hz
      have fits := rank_row_fits p keys out widths reg u.val hu
      have cap := reg.motifFits
      change pieceCount d c ≤ (p 4).val at cap
      rw [Fin.val_add,rank_start p keys out widths dest reg mem i hu,Fin.val_ofNat,Nat.add_mod_mod,
        Nat.mod_eq_of_lt (by change (T).outStart u.val + z < _; omega)]
      change out.val+u.val*(p 4).val+z < dest.val ∨ dest.val+A ≤ out.val+u.val*(p 4).val+z
      simp only [Nat.add_assoc]
      have hh := Nat.mul_le_mul_right (p 4).val (Nat.succ_le_of_lt hu)
      rw [Nat.succ_mul] at hh
      exact sep.rows.outside (by omega)

end CompressorRecords.BundleGather

end VPVNP
end Computability
end OAI
