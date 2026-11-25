import OAI.Computability.BorderVNP.CubeISAHeaderSpellingCard
import OAI.Computability.BorderVNP.CubeISAHeaderDecodeReadout
import OAI.Computability.BorderVNP.CubeISALengthVerified

/-! # The native common-header decoder computes the physical cube broadcast

Each field value below is the formal little-endian value in the manuscript's
raw declaration. The bounds checked by the machine accept every passing raw
declaration. Dense claimed rows and every column total have their mathematical
values after the ordinary word program, including empty or zero-valued fields.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.DeclarationBits

open Physical RoutingISA VPVNP.BurstRAM TeamContraction.JointHeader

variable {n d cap w : ℕ}

/-- Instantiate the native layout with the fixed widths of the physical cube broadcast. -/
def layout (n d cap header source dense totals : ℕ) : HeaderDecode.Layout :=
  ⟨header,source,d,n+1,Nat.clog 2 (n+1),Nat.clog 2 (cap+1),cap,dense,totals⟩

/-- The source fields are binary, and the only additional native input tests
are the legal ranges for the grouping coordinate and for the actual row words. -/
theorem valid_iff {f : Broadcast n d cap} (header source dense totals : ℕ)
    (hw : 0 < w) {m : Memory w} (hs : FlatAt m source (spelling f)) :
    HeaderDecode.Valid (layout n d cap header source dense totals) (readings m) ↔
      readCode (n+1) f.1 < n+1 ∧ ∀ r j, readCode (cap+1) (f.2 r j) < cap+1 := by
  let l := layout n d cap header source dense totals
  have coord := read_bits (coordinate_bits hw hs)
  have check (k : Fin (d*d*(n+1))) (h : upper d (n+1) k.val) :
      SelectorRead.Valid (readings m) (l.start k.val) l.rw (cap+1) ↔ readCode (cap+1) (field f k) < cap+1 := by
    have digits := row_bits hw hs k h
    have hd := read_bits digits
    exact ⟨fun ok => hd ▸ ok.2, fun hr =>
      ⟨fun j hj => (digits ⟨j,hj⟩).trans_lt (Nat.lt_succ_of_le (Bool.toNat_le _)), hd.symm ▸ hr⟩⟩
  constructor
  · rintro ⟨hc,hr⟩
    refine ⟨coord ▸ hc.2, fun pair j => ?_⟩
    let st := Sym2.sortEquiv pair
    let k := CubeLengths.entryOrder d (n+1) (st.val,j)
    have h : upper d (n+1) k.val := (upper_iff _).mpr (by simpa [k] using st.property)
    have hh := (check k h).mp (hr k.val k.isLt h)
    simpa only [field,k,Equiv.symm_apply_apply,show Sym2.mk st.val.1 st.val.2 = pair from
      Sym2.sortEquiv.symm_apply_apply pair] using hh
  · rintro ⟨hc,hr⟩
    exact ⟨⟨fun j hj => (coordinate_bits hw hs ⟨j,hj⟩).trans_lt (Nat.lt_succ_of_le (Bool.toNat_le _)),
      coord.symm ▸ hc⟩, fun k hk h => (check ⟨k,hk⟩ h).mpr (hr _ _)⟩

/-- The row values of the decoder's actual shared-memory image agree with
all of the compact input words, with canonical zero padding below the diagonal. -/
theorem final_rows {f : Broadcast n d cap} (header source dense totals : ℕ)
    (hw : 0 < w) {m : Memory w} (hs : FlatAt m source (spelling f))
    (apart : dense+d*d*(n+1) ≤ totals ∨ totals+(n+1) ≤ dense) :
    let l := layout n d cap header source dense totals
    CubeLengths.StoredRows (l.finalImage (readings m)) dense (fun r j => readCode _ (f.2 r j)) := by
  intro l a b j
  let k := CubeLengths.entryOrder d (n+1) ((a,b),j)
  change l.finalImage (readings m) (l.dense+k.val) = _
  rw [l.finalEntry (readings m) k.isLt apart]
  have hu : upper d (n+1) k.val ↔ a ≤ b := by simpa only [k,Equiv.symm_apply_apply] using upper_iff k
  by_cases hab : a ≤ b
  · have h := hu.mpr hab
    have he := read_bits (row_bits hw hs k h)
    change (if upper d (n+1) k.val then _ else 0) = if a ≤ b then _ else _
    rw [ite_eq_left h, ite_eq_left hab]
    simpa only [l,layout,HeaderDecode.Layout.start,field,k,Equiv.symm_apply_apply] using he
  · change (if upper d (n+1) k.val then _ else 0) = if a ≤ b then _ else _
    rw [ite_eq_right (mt hu.mp hab),ite_eq_right hab]

/-- The columns built by the word program are the genuine sums over unordered
physical row declarations, counted once even on the diagonal. -/
theorem final_totals {f : Broadcast n d cap} (header source dense totals : ℕ)
    (hw : 0 < w) {m : Memory w} (hs : FlatAt m source (spelling f))
    (apart : dense+d*d*(n+1) ≤ totals ∨ totals+(n+1) ≤ dense) (j : Fin (n+1)) :
    let l := layout n d cap header source dense totals
    l.finalImage (readings m) (totals+j.val) = ∑ r, readCode _ (f.2 r j) := by
  intro l
  let z : CubeLengths.Layout := ⟨0,dense,l.entries,totals,n+1,0⟩
  have col := (final_rows header source dense totals hw hs apart).column_sum (l := z) rfl j
  change l.finalImage (readings m) (l.totals+j.val) = _
  rw [l.finalTotal (readings m) j.isLt,← col]
  apply Finset.sum_congr rfl
  intro k hk
  have lt : k*(n+1)+j.val < l.entries := by
    have h := Finset.mem_range.mp hk
    change k < d*d at h
    change k*(n+1)+j.val < (d*d)*(n+1)
    exact (Nat.add_lt_add_left j.isLt _).trans_le (by simpa only [Nat.succ_mul] using Nat.mul_le_mul_right (n+1) h)
  exact (l.finalEntry (readings m) lt apart).symm

/-- A physically passing declaration always meets the native decoder's range
tests, because its entries are bounded by the actual column widths. -/
theorem valid_of_passing {blocks B K h s : ℕ} (select : Packet n d blocks → Selector n K h)
    (f : Broadcast n d (declarationCap n d blocks B h s)) (hf : passesBroadcast B s select f)
    (header source dense totals : ℕ) (hw : 0 < w) {m : Memory w} (hs : FlatAt m source (spelling f)) :
    HeaderDecode.Valid (layout n d (declarationCap n d blocks B h s) header source dense totals) (readings m) := by
  apply (valid_iff header source dense totals hw hs).mpr
  obtain ⟨i,hi,hr⟩ := hf
  exact ⟨hi ▸ i.isLt,fun r j => Nat.lt_succ_of_le
    ((declared_entry_le B s select _ hr r j).trans (cutWidth_le_cap B s select j))⟩

end Cube.DeclarationBits

end BorderVNP
end Computability
end OAI
