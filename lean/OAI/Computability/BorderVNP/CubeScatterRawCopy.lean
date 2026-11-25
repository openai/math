import OAI.Computability.BorderVNP.CubeISAOwnedScatterPacket
import OAI.Computability.BorderVNP.CubeScatterTrialPrefix

/-! # Copying and validating arbitrary received selector digits

The native selector-copy program needs the delivered binary words and the
two disjoint address ranges. Whether they encode an available selector is
decided only by the subsequent reader's actual rank guard.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Scatter

open RoutingISA VPVNP.BurstRAM DiagonalResidueRAM Tally

variable {w n K h : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}

/-- Raw copied selector digits, before any selector tuple has been decoded. -/
def rawImage (bs : List Bool) (base : ℕ) (m : Memory w) := image (bs.map Position.selector) base m

private theorem selectorFields (bs : List Bool) :
    (bs.map Position.selector).filterMap Position.selectorBit = bs ∧
    (bs.map Position.selector).filterMap Position.crossBit = [] := by
  induction bs with
  | nil => exact ⟨rfl,rfl⟩
  | cons bit bs ih => simp only [List.map_cons,List.filterMap_cons,Position.selectorBit,Position.crossBit,ih.1,ih.2,and_self]

/-- Copy any delivered selector word to its reserved prefix. The following
reader may still reject it as an out-of-range selector. -/
theorem rawCopy_run (src : Set ℕ) (c : Cursor) (bs : List Bool) (len : bs.length = selectorWidth n K h)
    (r : Bank w) (m : Memory w) (sel : r 36 = word w c.selector) (cross : r 37 = word w c.crossing)
    (base : r 24 = word w c.dest) (input : Resident src m c.selector bs)
    (dest : ∀ j < bs.length, c.dest+j ∉ src ∧ c.dest+j < 2^w) :
    ∃ t es, Runs pub mac (copySelectors n K h) r m es t (rawImage bs c.dest m) ∧
      (Cursor.mk (c.selector+bs.length) c.crossing (c.dest+bs.length)).loaded t ∧
      ∀ j : Reg, j ∉ ([36,37,38,59,60] : List Reg) → t j = r j := by
  let ps := bs.map Position.selector
  obtain ⟨ls,cs⟩ := selectorFields bs
  have ready : Prepared src ps c m := prepared_of_streams src ps c m (ls ▸ input.bits)
    (cs ▸ (Resident.nil src m c.crossing).bits) (ls ▸ input.addresses)
    (cs ▸ (Resident.nil src m c.crossing).addresses) (fun j hj => dest j (by simpa only [ps,List.length_map] using hj))
  let pre := effect false r m startPacket
  have head := effect_runs pub mac false r m startPacket (by decide)
  have hc : c.loaded pre.bank := by
    simp (config := {decide := true}) [pre,startPacket,Code.block,effect,Cursor.loaded,Function.update,sel,cross,base]
    rfl
  let ds := ps.map Position.digit
  let tail := result ds pre.bank m
  have loop := program_run pub mac ds pre.bank m
  have modes : ds.map Digit.mode = List.replicate (selectorWidth n K h) .selector := by
    simp [ds,ps,List.map_map,Function.comp_def,Position.digit,Digit.mode,len,List.map_const']
  rw [modes] at loop
  obtain ⟨loaded,mem,keep⟩ := result_image src ps c pre.bank m hc ready
  have cur : advance ps c = ⟨c.selector+bs.length,c.crossing,c.dest+bs.length⟩ := by
    rw [advance_counts,ls,cs,List.length_nil,Nat.add_zero,List.length_map]
  have hmem : tail.mem = rawImage bs c.dest m := mem
  have execution : Runs pub mac (copySelectors n K h) r m (pre.trace++tail.trace) tail.bank tail.mem := head.seq loop
  exact ⟨tail.bank,pre.trace++tail.trace,hmem ▸ execution,cur ▸ loaded,fun j hj => by
    simp at hj
    exact (keep j (by simp [hj])).trans (by simp [pre,startPacket,Code.block,effect,Function.update,hj])⟩

/-- Every word at the copy destination equals the corresponding original raw bit. -/
theorem rawImage_bits (bs : List Bool) (base : ℕ) (m : Memory w) : BitsAt (rawImage bs base m) base bs := by
  intro j
  apply image_at (bs.map Position.selector) base m ⟨j.val,by simp⟩
  simp [Position.value]

/-- Successful decoding of a copied raw word recovers an actual physical selector whose
canonical source spelling is exactly the original list. -/
theorem rawImage_selector {bs : List Bool} {m : Memory w} {base : ℕ} (len : bs.length = selectorWidth n K h)
    (one : 1 < 2^w) (valid : SelectorRead.Valid (readings (rawImage bs base m)) base (selectorWidth n K h)
      (Fintype.card (Selector n K h))) :
    ∃ u : Selector n K h, bs = selectorStream u ∧ SelectorRead.Stored (readings (rawImage bs base m)) base u := by
  obtain ⟨u,stored,_⟩ := (SelectorRead.valid_iff_existsUnique ..).mp valid
  refine ⟨u,List.ext_getElem (len.trans (selectorStream_length u).symm) ?_,stored⟩
  intro j hj hj'
  let k : Fin (selectorWidth n K h) := ⟨j,len ▸ hj⟩
  have raw := congrArg Fin.val (rawImage_bits bs base m ⟨j,hj⟩)
  change (rawImage bs base m (base+j)).val = (word w bs[j].toNat).val at raw
  rw [word_val _ _ (bs[j].toNat_le.trans_lt one)] at raw
  have eqn := raw.symm.trans (stored k)
  have bit : (selectorStream u)[j] = VPVNP.RAMSerialization.wordBits _
      ⟨(selectorOrder n K h u).val,(selectorOrder n K h u).isLt.trans_le (Nat.le_pow_clog (by decide) _)⟩ k := by
    simp [selectorStream,k]
  rw [bit]
  exact (by decide : ∀ a b : Bool, a.toNat = b.toNat → a = b) _ _ eqn

end Cube.Scatter

end BorderVNP
end Computability
end OAI
