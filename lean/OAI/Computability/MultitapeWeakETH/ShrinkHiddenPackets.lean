import OAI.Computability.MultitapeWeakETH.ShrinkHiddenScan
import OAI.Computability.VPVNP.PairShrinkHiddenTypedDecode

/-! # Recovering the typed absorbed edges from their private bit prefix -/

namespace OAI.Computability.MultitapeWeakETH.ShrinkHidden

open IntegerMultiplication Code VPVNP Compression Compression.ShrinkMotif NetworkKernel
open CompressorRecords PairSimulation ShrinkHiddenGuess ShrinkHiddenSlots NativeGrid
open scoped Fin.CommRing
noncomputable section

abbrev Metadata := List (Bits.Word × Tally)
abbrev Parsed := List Bits.Word × Option (List Bits.Word × Bits.Word)

/-- Keep IDs in a parallel list for the two incidences that share each hidden field. -/
def parse (q : Metadata × Bits.Word) : Parsed :=
  (q.1.map Prod.fst,ChildScan.splitPackets (q.1.map Prod.snd,q.2))

theorem parse_poly : Poly parse := by
  exact (Easy.fst.poly.compose (Poly.maps _ Easy.fst.poly)).pair
    (((Easy.fst.poly.compose (Poly.maps _ Easy.snd.poly)).pair Easy.snd.poly).compose ChildScan.splitPackets_poly)

def metadata (w : ℕ) (rs : List Row) : Metadata :=
  rs.map fun e => (BurstRAM.wordBits (e.1 : BurstRAM.Word w),tally e.2.length)

variable {a g : ℕ} (X : State a (packingLaneBits a g)) (layout : Bool)
  (widths : X.packingData.Motif → Bool × Fin 4 → ℕ) (v : (X.Base × BitWord (Shrink.J a)) × BitWord g)

local notation "Rows" => ShrinkHiddenSlots.rows X layout widths v
local notation "Hidden" => Placed (X.packingData.shrinkInternalOwner layout) (internalLabel widths layout) v

set_option maxHeartbeats 1600000 in
/-- Starting from one placeholder row, the bit-stack parser accepts precisely the
encodings of actual assignments at this owner and preserves the entire suffix. -/
theorem parse_iff (w : ℕ) (seed : Hidden) (bits : Bits.Word) (ids fields : List Bits.Word) (tail : Bits.Word) :
    parse (metadata w (Rows seed),bits) = (ids,some (fields,tail)) ↔
      ∃ h : Hidden, ids = (Rows h).map (fun e => BurstRAM.wordBits (e.1 : BurstRAM.Word w)) ∧
        fields = (Rows h).map Prod.snd ∧ bits = stream (Rows h) ++ tail := by
  let sizes := ((Rows seed).map Prod.snd).map (tally ∘ List.length)
  let names := (Rows seed).map fun e => BurstRAM.wordBits (e.1 : BurstRAM.Word w)
  have shape (h : Hidden) : ((Rows h).map Prod.snd).map (tally ∘ List.length) = sizes ∧
      (Rows h).map (fun e => BurstRAM.wordBits (e.1 : BurstRAM.Word w)) = names := by
    simp only [sizes,names,ShrinkHiddenSlots.rows,List.map_ofFn,Function.comp_def,List.length_ofFn,and_self]
  have exactRead (h : Hidden) (rest : Bits.Word) (eqn : bits = stream (Rows h) ++ rest) :
      ChildScan.splitPackets (sizes,bits) = some ((Rows h).map Prod.snd,rest) :=
    (ChildScan.splitPackets_iff ..).mpr ⟨(shape h).1,by simpa only [stream,List.flatMap_def] using eqn⟩
  have program : parse (metadata w (Rows seed),bits) = (names,ChildScan.splitPackets (sizes,bits)) := by
    simp only [parse,metadata,names,sizes,List.map_map,Function.comp_def]
  rw [program,Prod.mk.injEq]
  constructor
  · rintro ⟨rfl,ok⟩
    have enough : (stream (Rows seed)).length ≤ bits.length := by
      have len : sizes.flatten.length = (stream (Rows seed)).length := by
        simp [sizes,stream,List.flatMap_def,List.length_flatten,List.map_map,Function.comp_def]
      rw [← len]
      by_contra! sm
      simp only [ChildScan.splitPackets,Iter.small,decide_eq_true sm,Bool.cond_true] at ok
      cases ok
    obtain ⟨h,_,part⟩ := decode_rows X layout widths v seed bits enough
    have same := Prod.mk.inj (Option.some.inj (ok.symm.trans (exactRead h _ part)))
    exact ⟨h,(shape h).2.symm,same.1,part.trans (congrArg _ same.2.symm)⟩
  · rintro ⟨h,rfl,rfl,part⟩
    exact ⟨(shape h).2.symm,exactRead h _ part⟩

end
end OAI.Computability.MultitapeWeakETH.ShrinkHidden
