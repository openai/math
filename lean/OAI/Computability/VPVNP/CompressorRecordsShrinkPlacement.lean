import OAI.Computability.VPVNP.CompressorRecordsShrinkRankSpace

/-!
# Four consecutive placement columns for a shrinking pass

The two short greedy columns are indexed by old base vertex. The mate and
shift columns are indexed by old base port. The output rectangles are
indexed by all old sites. These separate extents allow the four rectangles
to begin immediately after the old directories.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkPlacement

open BurstRAM Compression PrimedStackRAM ShrinkRAM

variable {a g w : ℕ} (X : State a (packingLaneBits a g)) (T : IncidenceDirectory w)
local notation "N" => Fintype.card X.Base
local notation "S" => N*2^(packingLaneBits a g)
local notation "D" => (2:ℕ)^a
local notation "C" => Shrink.colors a
local notation "J" => Shrink.J a

/-- The fourteen public placement operands, including radices, layout choice, old incidence and
greedy data, and four output column bases. -/
def bank (color offset : Word w) (base : ℕ) (layout : Bool) : Fin 14 → Word w :=
  ![word w (2^g), word w (2^J), word w D, word w (2^C), word w (C-1),
    if layout then 1 else 0, color, offset, T.baseOut,T.shift,
    word w (base+0*S),word w (base+1*S),word w (base+2*S),word w (base+3*S)]

/-- The first address after the four placement columns, each of which has one entry per old
site. -/
def stop (base : ℕ) := base+4*S

variable (color offset : Word w) (base : ℕ) (layout : Bool)
local notation "p" => bank X T color offset base layout

theorem params (room : stop X base < 2^w) : Params p a C J g layout := by
  have hsite : S < 2^w := by change base+4*S < _ at room; omega
  have hp : 2^(packingLaneBits a g) < 2^w := (Nat.le_mul_of_pos_left _ (Fintype.card_pos : 0 < N)).trans_lt hsite
  have fit (j : ℕ) (hj : j ≤ packingLaneBits a g) : 2^j < 2^w :=
    (Nat.pow_le_pow_right Nat.zero_lt_two hj).trans_lt hp
  have hg := fit g (by simp only [packingLaneBits]; omega)
  have hj := fit J (by simp only [packingLaneBits,Shrink.J]; omega)
  have hd := fit a (by simp only [packingLaneBits]; omega)
  have hc := fit C (by simp only [packingLaneBits,Shrink.colors]; omega)
  have hlow := fit (J+g) (by simp only [packingLaneBits,Shrink.J]; omega)
  have hc' := (Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp hc
  have he : C-1 < 2^w := (Nat.sub_le ..).trans_lt (hc'.trans Nat.lt_two_pow_self)
  have h2 : 2 < 2^w := (Nat.pow_le_pow_right Nat.zero_lt_two (show 1 ≤ C by unfold Shrink.colors; omega)).trans_lt hc
  exact ⟨Nat.mod_eq_of_lt hg,Nat.mod_eq_of_lt hj,Nat.mod_eq_of_lt hd,Nat.mod_eq_of_lt hc,Nat.mod_eq_of_lt he,
    rfl,hlow,by omega,h2⟩

theorem starts (room : stop X base < 2^w) (i : Fin 4) :
    (p (i.natAdd 10)).val = base+i.val*S := by
  have h : base+i.val*S < 2^w := by
    have hi := Nat.mul_le_mul_right S i.isLt.le
    change base+4*S < _ at room; omega
  fin_cases i <;> exact Nat.mod_eq_of_lt h

private theorem divWord (x y : Word w) : (div x y).val = x.val / y.val :=
  Nat.mod_eq_of_lt ((Nat.div_le_self ..).trans_lt x.isLt)

private theorem modWord (x y : Word w) : (mod x y).val = x.val % y.val :=
  Nat.mod_eq_of_lt ((Nat.mod_le ..).trans_lt x.isLt)

private theorem offsets (hp : Params p a C J g layout) (i : Word w) (hi : i.val < S) :
    (decode p i).base.val < N ∧ (baseArc p (decode p i)).val < N*D := by
  have hchunk : (p 1*p 0).val = 2^(J+g) := by rw [Fin.val_mul,hp.tag,hp.lane,← pow_add,Nat.mod_eq_of_lt hp.low_fit]
  have hb : (decode p i).base.val < N := by
    change (div (div (div i (p 1*p 0)) (p 2)) (p 3)).val < _
    rw [divWord,divWord,divWord,hchunk,hp.degree,hp.mask]
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
    simpa only [packingLaneBits,Shrink.J,Shrink.colors,pow_add,Nat.mul_assoc] using hi
  have hs : (decode p i).slot.val < D := by
    change (mod (div i (p 1*p 0)) (p 2)).val < _
    rw [modWord,hp.degree]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  refine ⟨hb,?_⟩
  have hh := Nat.mul_le_mul_right D hb
  rw [Nat.succ_mul] at hh
  rw [baseArc,Fin.val_add,Fin.val_mul,hp.degree,Nat.mod_add_mod]
  exact (Nat.mod_le ..).trans_lt (by omega)

theorem regions (room : stop X base < 2^w) (colorBefore : color.val+N ≤ base) (offBefore : offset.val+N ≤ base)
    (old : ∀ t : Fin 6, (T.column t).val+S*D ≤ base) : Regions p S := by
  have hp := params X T color offset base layout room
  apply Regions.packed p room.le (starts X T color offset base layout room)
  intro c i hi
  obtain ⟨hb, ha⟩ := offsets X T color offset base layout hp i hi
  have hsmall : N*D ≤ S*D := Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))
  have access (addr k : Word w) (h : addr.val+k.val < base) : (addr+k).val < base :=
    (Nat.mod_le ..).trans_lt h
  left
  fin_cases c
  · exact access color _ ((Nat.add_lt_add_left hb _).trans_le colorBefore)
  · exact access offset _ ((Nat.add_lt_add_left hb _).trans_le offBefore)
  · exact access T.baseOut _ ((Nat.add_lt_add_left (ha.trans_le hsmall) _).trans_le (old 0))
  · exact access T.shift _ ((Nat.add_lt_add_left (ha.trans_le hsmall) _).trans_le (old 2))

theorem actual_run (m : Memory w) (dir : Shrink.Directory X.slots X.baseIndex
    (column p m 6) (column p m 7) (column p m 8) (column p m 9))
    (room : stop X base < 2^w) (colorBefore : color.val+N ≤ base) (offBefore : offset.val+N ≤ base)
    (old : ∀ t : Fin 6, (T.column t).val+S*D ≤ base) :
    ∃ rs, runSegment ((template ShrinkRAM.visit 0).instantiate w p).program 65 (some (word w 0)) m
      (List.replicate S []) = some rs ∧ ScanResult p S 0 S m rs ∧
      PlacementColumns X.slots X.baseIndex p layout (after m (eventLog rs)) ∧
      ∀ z < base, after m (eventLog rs) z = m z := by
  have reg := regions X T color offset base layout room colorBefore offBefore old
  have hx : N*(2^J*2^g)*D ≤ S := by
    simp only [packingLaneBits,pow_add,Shrink.J]
    have h := Nat.le_mul_of_pos_left (N*2^(packingTagBits (2^a))*2^g*2^a) (Nat.two_pow_pos (2*2^a+1))
    rw [Nat.mul_assoc N (2^(packingTagBits (2^a))) (2^g)] at h
    convert h using 1; ring
  obtain ⟨rs,he,scan,rows⟩ := placement_run X.slots X.baseIndex p layout m
    (params X T color offset base layout room) dir reg (hx.trans reg.fits)
  refine ⟨rs,he,scan,rows,?_⟩
  intro z hz
  apply scan.preserve
  intro t i _ hi
  have hi' : i.val<S := by simpa only [Nat.zero_add] using hi
  have hpos := Nat.mul_le_mul_right S t.isLt
  rw [Nat.succ_mul] at hpos
  have hbound : base+t.val*S+i.val < 2^w := by change base+4*S<2^w at room; omega
  rw [outAddr,Fin.val_add,starts X T color offset base layout room,Nat.mod_eq_of_lt hbound]
  omega

end CompressorRecords.ShrinkPlacement

end VPVNP
end Computability
end OAI
