import OAI.Computability.VPVNP.CompressorRecordRefreshAllocation

/-!
# Preparing a refresh in its packed allocation

The six old incidence columns end before the seven new scratch columns. The gather reads
a permutation of the old actual slots and the directory reads the two old base columns.
The demand table and every strided term record begin after the last scratch column.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh.Allocation

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM Compression Compression.Refresh Compression.DegreeRefresh
open NewSlots

variable {bits a g : ℕ}

private theorem packed_lt {x j n d : ℕ} (hx : x < n) (hj : j < d) : x*d+j < n*d := by
  have h := Nat.mul_le_mul_right d (Nat.succ_le_of_lt hx)
  rw [Nat.succ_mul] at h; omega

/-- Transposing port and residual lane in the gather index stays inside the old
site-major width table, including when the dimensions are powers of two of size one. -/
theorem gather_index_lt (D R i : W bits) (v : ℕ) (hd : 0 < D.val) (hr : 0 < R.val)
    (hi : i.val < v*D.val*R.val*D.val) :
    (RefreshGather.oldIndex D R i).val < v*D.val*R.val*D.val := by
  let b := i.val/D.val
  let j := i.val%D.val
  let x := b/R.val
  let l := b%R.val
  have hb : b < v*D.val*R.val := (Nat.div_lt_iff_lt_mul hd).mpr hi
  have hx : x < v*D.val := (Nat.div_lt_iff_lt_mul hr).mpr hb
  have hj : j < D.val := Nat.mod_lt _ hd
  have hl : l < R.val := Nat.mod_lt _ hr
  have outer : i.val = b*D.val+j := (Nat.div_add_mod' ..).symm
  have inner : b = x*R.val+l := (Nat.div_add_mod' ..).symm
  have key := RefreshGather.oldIndex_val D R i hj hl (inner ▸ outer)
  rw [key]
  exact (Nat.mod_le ..).trans_lt (packed_lt (packed_lt (packed_lt ((Nat.div_lt_iff_lt_mul hd).mpr hx) hj) hl)
    (Nat.mod_lt _ hd))

theorem Plan.scratch_interval (P : Plan) (room : P.demand ≤ 2^bits) (c : Fin 8) (hc : c ≠ 0)
    (j : W bits) (hj : j.val < P.segments) : P.start ≤ (P.scratch bits c+j).val ∧ (P.scratch bits c+j).val < P.demand := by
  have h := Nat.mul_le_mul_right P.segments (show (c.val-1)+1 ≤ 7 by have := c.isLt; omega)
  rw [Nat.add_mul,Nat.one_mul] at h
  change P.start+7*P.segments ≤ 2^bits at room
  have baseFits : P.start+(c.val-1)*P.segments < 2^bits := by omega
  have cellFits : P.start+(c.val-1)*P.segments+j.val < 2^bits := by omega
  rw [Plan.scratch,ite_eq_right hc,Fin.val_add,
    show (word (bits := bits) (P.start+(c.val-1)*P.segments)).val = _ from Nat.mod_eq_of_lt baseFits,
    Nat.mod_eq_of_lt cellFits]
  change P.start ≤ _ ∧ _ < P.start+7*P.segments
  constructor <;> omega

variable (X : State a (a+g)) (T : IncidenceDirectory bits) (a₀ dH t stride start : ℕ)

local notation "P" => plan X a₀ dH t stride start
local notation "Q" => Plan.scratch P bits
local notation "L" => (word (bits := bits) (2^g))
local notation "V" => Fintype.card X.Base
local notation "B" => V*2^g
local notation "N" => V*2^a*2^g
local notation "S" => N*2^a

/-- The exact inputs for `prepare_demands` and the term reader. The term row intervals
are disjoint from all segment descriptors, so their native writes preserve the endpoints. -/
structure PrepareLayout : Prop where
  degree : (Q 0).val = 2^a
  lanes : (L).val = 2^g
  regions : RefreshRAM.Regions Q S
  directory : BundleDirectory.Layout (directoryWords Q L T.baseOut T.shift) (V*2^a) (2^g)
  gather : RefreshGather.SourcesDisjoint (gatherWords Q L T.width) S
  baseApart : baseOutsideGather X (IncidenceDirectory.baseOrder X) Q T.baseOut T.shift
  demandRoom : (word (bits := bits) (P).demand).val+B*t ≤ 2^bits
  demandApart : demandApart (t := t) X Q (word (P).demand)
  demandTerm : (word (bits := bits) (P).demand).val+B*t ≤ (word (bits := bits) (P).term).val
  termRoom : (word (bits := bits) (P).term).val+B*stride < 2^bits
  termApart : ∀ c : Fin 8, c ≠ 0 → ∀ j : W bits, j.val < S → ∀ b : Fin B,
    (Q c+j).val < (word (bits := bits) ((P).term+b.val*stride)).val

private theorem directory_layout (before : ∀ c : Fin 6, (T.column c).val+S ≤ start)
    (regions : RefreshRAM.Regions Q S) (droom : (P).demand ≤ 2^bits) :
    BundleDirectory.Layout (directoryWords Q L T.baseOut T.shift) (V*2^a) (2^g) := by
  let p := directoryWords Q L T.baseOut T.shift
  have ns : N ≤ S := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos a)
  have bn : V*2^a ≤ N := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos g)
  have fixed (i : Fin 8) (h₂ : 2 ≤ i.val) (h₄ : i.val ≤ 4) : p i = Q i := by
    fin_cases i <;> first | rfl | simp at h₂ h₄
  refine ⟨ns.trans regions.fits,fun c u x y hc₁ hc₅ hu₂ hu₄ hx hy => ?_⟩
  have hu₀ : u ≠ 0 := by rintro rfl; simp at hu₂
  change (p c+x).val = (p u+y).val ↔ c=u ∧ x=y
  rw [fixed u hu₂ hu₄]
  have hafter := ((P).scratch_interval droom u hu₀ y (hy.trans_le ns)).1
  change start ≤ (Q u+y).val at hafter
  by_cases hread : c=1 ∨ c=5
  · rw [ite_eq_left hread] at hx
    have hbefore (i : Fin 6) : (T.column i+x).val < start :=
      (Nat.mod_le ((T.column i).val+x.val) _).trans_lt (by have := before i; have := hx.trans_le (bn.trans ns); omega)
    have hne : c ≠ u := by rcases hread with rfl | rfl <;> rintro rfl <;> simp at hu₂ hu₄
    have he : (p c+x).val ≠ (Q u+y).val := by
      rcases hread with rfl | rfl
      · exact Nat.ne_of_lt ((hbefore 0).trans_le hafter)
      · exact Nat.ne_of_lt ((hbefore 2).trans_le hafter)
    simp [he,hne]
  · rw [ite_eq_right hread] at hx
    have hn₁ : c.val ≠ 1 := fun h => hread (Or.inl (Fin.ext h))
    have hn₅ : c.val ≠ 5 := fun h => hread (Or.inr (Fin.ext h))
    rw [fixed c (by omega) (by omega)]
    exact regions.apart c u (by rintro rfl; simp at hc₁) hu₀ x y (hx.trans_le ns) (hy.trans_le ns)

/-- Packed prepass allocation. The six scalar end bounds on the old columns and one
total allocation bound replace all the per-cell separation conditions of the native scans. -/
theorem prepare_layout (before : ∀ c : Fin 6, (T.column c).val+S ≤ start) (room : (P).stop < 2^bits) :
    PrepareLayout X T a₀ dH t stride start := by
  have spos : 0 < N := by positivity
  have capPos : 0 < (P).capacity := Nat.mul_pos spos (Nat.two_pow_pos a₀)
  have regions := (P).scratch_regions room.le capPos
  have hs : 2^a ≤ (P).segments := Nat.le_mul_of_pos_left _ spos
  have hR : 2^g ≤ N := Nat.le_mul_of_pos_left _ (Nat.mul_pos Fintype.card_pos (Nat.two_pow_pos a))
  have ns : N ≤ S := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos a)
  have bn : V*2^a ≤ N := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos g)
  have stopRoom : (P).supply < 2^bits := by
    dsimp only [Plan.stop,Plan.next,Plan.reverseSlot,Plan.targetPort] at room; omega
  have hsrc : start+7*S = (P).demand := rfl
  have hterm : (P).demand+B*t = (P).term := rfl
  have hsup : (P).term+B*stride = (P).supply := rfl
  change 2^a ≤ S at hs
  have hd : (Q 0).val = 2^a := by change (word (bits := bits) (2^a)).val = _; exact Nat.mod_eq_of_lt (by omega)
  have hr : (L).val = 2^g := Nat.mod_eq_of_lt (show 2^g < 2^bits by omega)
  have hm : (word (bits := bits) (P).demand).val = (P).demand := Nat.mod_eq_of_lt (by omega)
  have ht : (word (bits := bits) (P).term).val = (P).term := Nat.mod_eq_of_lt (by omega)
  have dir := directory_layout X T a₀ dH t stride start before regions (by omega)
  have low (c : Fin 6) (i : W bits) (hi : i.val < S) : (T.column c+i).val < start :=
    (Nat.mod_le ((T.column c).val+i.val) _).trans_lt (by have := before c; omega)
  have scratch (c : Fin 8) (hc : c ≠ 0) (j : W bits) (hj : j.val < S) :=
    (P).scratch_interval (by omega : (P).demand ≤ 2^bits) c hc j hj
  refine ⟨hd,hr,regions,dir,?_,?_,by rw [hm]; omega,?_,by rw [hm,ht]; omega,by rw [ht]; omega,?_⟩
  · intro i j hi hj
    have h := gather_index_lt (Q 0) L i V (by rw [hd]; exact Nat.two_pow_pos a) (by rw [hr]; exact Nat.two_pow_pos g)
      (by simpa only [hd,hr] using hi)
    rw [hd,hr] at h
    exact Nat.ne_of_lt ((low 5 _ h).trans_le (scratch 1 (by decide) j hj).1)
  · intro e j hj
    have he : (Fin.ofNat (2^bits) (IncidenceDirectory.baseOrder X e).val).val < S :=
      (Nat.mod_le ..).trans_lt ((IncidenceDirectory.baseOrder X e).isLt.trans_le (bn.trans ns))
    have ha := (scratch 1 (by decide) j hj).1
    exact ⟨Nat.ne_of_lt ((low 0 _ he).trans_le ha),Nat.ne_of_lt ((low 2 _ he).trans_le ha)⟩
  · intro c hc i hi
    exact Or.inl (by rw [hm]; exact (scratch c hc i hi).2)
  · intro c hc j hj b
    have upper := Nat.mul_le_mul_right stride b.isLt.le
    have hb : (P).term+b.val*stride < 2^bits := by omega
    rw [show (word (bits := bits) ((P).term+b.val*stride)).val = _ from Nat.mod_eq_of_lt hb]
    have ha := (scratch c hc j hj).2; omega

end CompressorRecords.PortRefresh.Allocation

end VPVNP
end Computability
end OAI
