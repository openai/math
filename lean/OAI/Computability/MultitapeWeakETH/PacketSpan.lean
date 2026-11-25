import OAI.Computability.MultitapeWeakETH.PlacedMemory

/-! # Bit ranges from an addressable bank of placed packets -/

namespace OAI.Computability.MultitapeWeakETH.NamedPackets

open IntegerMultiplication Code VPVNP BurstRAM Compression Compression.ShrinkMotif
open NetworkKernel PairSimulation LocalHistory NodeArguments NativeGrid TerminalWords CompressorRecords
open private address address_poly address_eq from OAI.Computability.MultitapeWeakETH.TerminalColumns
open scoped Classical Fin.CommRing
noncomputable section

variable {D : Type} [Codec D] (read : D × Bits.Word → Bool)

def range (q : (D × Bits.Word) × Tally) : Bits.Word :=
  (Iter.lineup q.2).map fun i => read (q.1.1,address (q.1.2,i))

theorem range_poly (hr : Poly read) : Poly (range read) := by
  classical
  by_cases live : Nonempty D
  · have base : Poly (fun q : (D × Bits.Word) × Tally => q.1.2) := by fun_prop
    have one := ((Easy.fst.compose Easy.fst).poly.pair ((base.pair Easy.snd.poly).compose address_poly)).compose hr
    exact (Easy.fst.poly.pair (Easy.snd.poly.compose Iter.poly_line)).compose (Poly.push (live.some,[]) [] one)
  · convert (Code.Poly.const (X:=(D × Bits.Word) × Tally) ([] : Bits.Word)) using 1
    funext x
    exact (live ⟨x.1.1⟩).elim

omit [Codec D] in
theorem range_eq {w l : ℕ} (wide : 0 < w) (ctx : D) (start : ℕ) (v : Fin l → Bool)
    (data : ∀ i : Fin l,
      PrivateFields.bitValue w (read (ctx,wordBits ((start+i.val : ℕ) : Word w))) =
      PrivateFields.bitValue w (v i)) :
    range read ((ctx,wordBits (start : Word w)),tally l) = List.ofFn v := by
  simp only [range,Iter.lined,List.map_ofFn,Function.comp_def,address_eq]
  apply congrArg List.ofFn
  funext i
  have h := data i
  simp only [Nat.cast_add] at h
  have one : (1 : Word w) ≠ 0 := fun eq => by
    have clash := congrArg Fin.val eq
    simp at clash
    omega
  cases hr : read (ctx,wordBits ((start : Word w)+(i.val : Word w))) <;> cases hb : v i <;>
    simp_all [PrivateFields.bitValue]

variable {k : Type} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
  {g w : ℕ} (X : State (ShrinkBlockInputs.a i) (packingLaneBits (ShrinkBlockInputs.a i) g))
  (sel : SelectedScore.Selection B X)
local notation "side" => SelectedFinish.chosen B X sel
local notation "place" => X.packingData.shrinkPlace side ∘ X.packingInputIso.site.symm

set_option maxHeartbeats 1800000 in
/-- The packing isomorphism transports stored native packets to precisely
the placed halves read by each resident at its six-party site. -/
theorem placed_readback (site : Compression.Site X.Base (BitWord (packingTagBits (2^ShrinkBlockInputs.a i))) (BitWord g))
    (v : (X.Base × BitWord (packingTagBits (2^ShrinkBlockInputs.a i))) × BitWord g)
    (hv : v = packedSiteEquiv site) (x : Placed (place) X.network.Half v)
    (A : Arena) (priv : Word w → Word w)
    (packets : ∀ u (hu : v = (place) u),
      let P := Packet.mk ((siteOrder X).entries.symm u).val (packed X u (x u hu))
      P.Fits A w 0 ∧ P.Stored A (DFS.scratch 0 priv)) :
    ShrinkOldHalves.PlacedPackets X side A (PortRefresh.ArgumentAddress.siteOrdinal X) priv site
      (X.packingData.shrinkPlacedHalf X.packingWidth side site hv (ShrinkRole.MapWitness.placedOld B i X sel v x)) 0 := by
  intro u hu
  let actual := X.packingInputIso.site u
  have atChild : v = (place) actual := by
    change v = packedSiteEquiv (X.packingData.placement side (X.packingInputIso.site.symm (X.packingInputIso.site u)))
    rw [Equiv.symm_apply_apply,← hu,hv]
  let z := (X.packingHalfEquiv u).symm (X.packingHalfEquiv u (x actual atChild))
  change (Packet.mk _ (packed X actual z)).Fits _ _ _ ∧ (Packet.mk _ (packed X actual z)).Stored _ _
  have ord : ((siteOrder X).entries.symm actual).val = PortRefresh.ArgumentAddress.siteOrdinal X actual := by
    let lanes := packingLaneBits (ShrinkBlockInputs.a i) g
    let lane := ((bitWordFinEquiv lanes) actual.2).val
    let base := (X.baseIndex actual.1).val
    change lane + 2^lanes * base = base * 2^lanes + lane
    ring
  have h := packets actual atChild
  dsimp only at h
  rw [ord] at h
  simpa only [z,Equiv.symm_apply_apply] using h

end
end OAI.Computability.MultitapeWeakETH.NamedPackets
