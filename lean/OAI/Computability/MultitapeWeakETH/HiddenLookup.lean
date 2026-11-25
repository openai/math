import OAI.Computability.MultitapeWeakETH.ShrinkHiddenPackets
import OAI.Computability.IntegerMultiplication.Match

/-! # Addressing both ends of an absorbed wire in the parsed bit fields -/

namespace OAI.Computability.MultitapeWeakETH.ShrinkHidden

open IntegerMultiplication Code VPVNP BurstRAM Compression Compression.ShrinkMotif
open CompressorRecords ShrinkHistoryRows NetworkKernel PairSimulation ShrinkHiddenSlots NativeGrid
open NearSquareRoot.InterchangeAffineMask
open private hits firstOr from OAI.Computability.MultitapeWeakETH.ExternalMemoryProgram
open scoped Classical Fin.CommRing
noncomputable section

/-- Return the packet at a binary ID in the paired lists from the hidden-field parser. -/
def fetch (q : Bits.Word × List Bits.Word × List Bits.Word) : Bits.Word :=
  lookup ((q.1,zipFair [] [] q.2),[])

theorem fetch_poly : Poly fetch :=
  (((Easy.fst.poly.pair (Easy.snd.poly.compose (easy_zip [] []).poly))).pair (Code.Poly.const [])).compose lookup_poly

private theorem lookup_cons (key id field : Bits.Word) (xs : WriteBytes) :
    lookup ((key,(id,field)::xs),[]) =
      (bif eqWord (key,id) then field else lookup ((key,xs),[])) := by
  by_cases h : Bits.value key = Bits.value id <;> simp [lookup,hits,firstOr,h]

/-- An ID hit returns the specified payload whenever all entries with that ID agree. -/
theorem fetch_at {E : Type} {w : ℕ} (num : E → Word w) (field : E → Bits.Word) (es : List E) (e : E)
    (member : e ∈ es) (agrees : ∀ d ∈ es, num d = num e → field d = field e) :
    fetch (wordBits (num e),es.map (wordBits ∘ num),es.map field) = field e := by
  unfold fetch
  change lookup ((wordBits (num e),zipFair [] [] (es.map (wordBits ∘ num),es.map field)),[]) = _
  rw [fair]
  induction es with
  | nil => cases member
  | cons j js ih =>
    simp only [List.map_cons,Function.comp_apply,lookup_cons]
    by_cases eq : num e = num j
    · have yes : eqWord (wordBits (num e),wordBits (num j)) = true := by simp [eq]
      rw [yes,Bool.cond_true]
      exact agrees _ List.mem_cons_self eq.symm
    · have no : eqWord (wordBits (num e),wordBits (num j)) = false := by
        apply Bool.eq_false_iff.mpr
        intro h
        exact Fin.val_ne_of_ne eq (by simpa only [value_native] using (eqWord_true _ _).mp h)
      rw [no,Bool.cond_false]
      exact ih ((List.mem_cons.mp member).resolve_left (fun h => eq (congrArg num h)))
        (fun d hd => agrees d (List.mem_cons_of_mem _ hd))

variable {a g : ℕ} (X : State a (packingLaneBits a g)) (side : Bool)
  (widths : X.packingData.Motif → Bool × Fin 4 → ℕ) (v : (X.Base × BitWord (Shrink.J a)) × BitWord g)

set_option maxHeartbeats 1200000 in
/-- The dense key shared by the source and target retrieves exactly the physical
little-endian field of the placed hidden assignment. -/
theorem hidden_field {w : ℕ} (room : (hiddenOrder X).length ≤ 2^w)
    (h : Placed (X.packingData.shrinkInternalOwner side) (internalLabel widths side) v)
    (e : X.packingData.Motif × Fin 4) (atSite : v = X.packingData.shrinkInternalOwner side e) :
    let rs := ShrinkHiddenSlots.rows X side widths v h
    fetch (wordBits (id X e : Word w),rs.map (fun r => wordBits (r.1 : Word w)),rs.map Prod.snd) =
      List.ofFn (RAMSerialization.wordBits _ (h e atSite)) := by
  intro rs
  let bits := List.ofFn (RAMSerialization.wordBits _ (h e atSite))
  let row : ℕ × Bits.Word := (id X e,bits)
  have mem : row ∈ rs := mem_rows X side widths v h e atSite
  have fit (r : ℕ × Bits.Word) (hr : r ∈ rs) : r.1 < 2^w := by
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr
    exact ((hiddenOrder X).entries.symm _).isLt.trans_le room
  have nd : (rs.map Prod.fst).Nodup := rows_nodup X side widths v h
  let num (r : ℕ × Bits.Word) := (r.1 : Word w)
  have agrees (d : ℕ × Bits.Word) (hd : d ∈ rs) (eqn : num d = num row) : d.2 = row.2 := by
    have val := congrArg Fin.val eqn
    change ((d.1 : Word w).val) = ((row.1 : Word w).val) at val
    rw [Fin.val_cast_of_lt (fit d hd),Fin.val_cast_of_lt (fit row mem)] at val
    exact congrArg Prod.snd (List.inj_on_of_nodup_map nd hd mem val)
  exact fetch_at num Prod.snd rs row mem agrees

end
end OAI.Computability.MultitapeWeakETH.ShrinkHidden
