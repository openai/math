import OAI.Computability.MultitapeWeakETH.ShrinkABTape

/-! # The assembled AB word on the actual child assignment of a resident -/

namespace OAI.Computability.MultitapeWeakETH.ShrinkMap

open IntegerMultiplication Code VPVNP BurstRAM Compression Compression.ShrinkMotif
open NetworkKernel PairSimulation LocalHistory NodeArguments NativeGrid CompressorRecords
open DescriptorSpace ShrinkBlockInputs MapResidentRows
open private publicWords from OAI.Computability.MultitapeWeakETH.ShrinkHiddenRecipe
open scoped Classical Fin.CommRing
noncomputable section

variable {D k : Type} [Codec D] [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
  (read : D × Bits.Word → Bits.Word) (hr : Poly read) (bank : D → NamedPackets.Bank) (hb : Poly bank)
local notation "Q" => ShrinkHidden.Indexed D

include hr hb in
set_option maxHeartbeats 1200000 in
theorem ab_placed (dir : Bool) :
    ∃ run : Q × Tally → Bits.Word, Poly run ∧ ∀ {g w : ℕ} (ctx : D)
      (X : State (a i) (packingLaneBits (a i) g)) (sel : SelectedScore.Selection B X)
      (base : Word w) (positions blocks n cur cap : ℕ) (mem : Memory w)
      (v : Site X) (j : Fin (order X (SelectedFinish.chosen B X sel) v).length),
      let side := SelectedFinish.chosen B X sel
      let m := rowMotif X side v j
      let L := BlockProgram.layout B base.val positions blocks
      let q : Q := (ShrinkHidden.query ctx ((levelStart L cur : ℕ) : Word w) cap (siteIndex X v).val,tally j.val)
      let place := X.packingData.shrinkPlace side ∘ X.packingInputIso.site.symm
      let width := X.packingData.abWidth X.shrinkNumber X.packingWidth m
      ∀ (o : Order {u // v = place u}) (x : Placed place X.network.Half v),
      (∀ p : Word w, read (ctx,wordBits p) = wordBits (mem p.val)) →
      CompiledResident.ShrinkPayload B base positions blocks n cur i X sel mem →
      bank ctx = NamedPackets.placedBank X place v o x w →
      (siteOrder X).length ≤ 2^w → 2*n*n < 2^w → (siteOrder X).length * (2*n*n) ≤ 2^w →
      2^(a i) ≤ n → X.maxWireWidth ≤ n → width ≤ 2^w →
      ∀ h : v = packedSiteEquiv (ShrinkOldHalves.abSite X m dir),
      let arg := X.packingData.shrinkPlacedHalf X.packingWidth side _ h (ShrinkRole.MapWitness.placedOld B i X sel v x)
      run (q,tally width) = List.ofFn (ShrinkAB.operand X.packingData X.shrinkNumber X.shrinkOrder
        X.packingWidth ⟨m,rfl⟩ (State.two_le_packingColors _) (Nat.two_pow_pos _) (ShrinkOldHalves.abData X side m dir arg)) := by
  obtain ⟨cell,cc,stored⟩ := NamedPackets.placed_memory
  obtain ⟨stride,sc,se⟩ := ShrinkHidden.expression read hr packetStride
  let src (q : Q) := (bank q.1.1.1.1,stride q)
  have cp : Poly src := ((show Poly (fun q : Q => q.1.1.1.1) by fun_prop).compose hb).pair sc
  let get (s : Q × Bits.Word) := cell (src s.1,s.2)
  have gc : Poly get := ((Easy.fst.poly.compose cp).pair Easy.snd.poly).compose cc
  obtain ⟨run,cost,actual⟩ := ab_program B i read hr get gc dir
  refine ⟨run,cost,?_⟩
  intro g w ctx X sel base positions blocks n cur cap mem v j side m L q place width o x rd data bk sites sf space degree maxW fit h arg
  let head := ((levelStart L cur : ℕ) : Word w)
  let p : Fin 5 → Word w := publicWords (siteIndex X v).val j.val
  let reg := (NamedPackets.placedBank X place v o x w,wordBits ((2*n*n : ℕ) : Word w))
  let priv (addr : Word w) := PrivateFields.bitValue w (cell (reg,wordBits addr))
  have fields := stored X place v o x (2*n*n) sites sf space (fun u hu =>
    (packed_length_le X u (x u hu)).trans (Nat.mul_le_mul (Nat.mul_le_mul_left _ degree) maxW))
  have srcEq : src q = reg := Prod.ext bk ((se ctx head cap _ _ mem rd).trans
    (congrArg wordBits (packetStride_eval B i X sel base positions blocks n cur mem data p)))
  have eqn : SliceLookup.physical (w:=w) q get = priv := by
    funext addr
    change PrivateFields.bitValue w (cell (src q,wordBits addr)) = _
    rw [srcEq]
  apply actual ctx X sel base positions blocks n cur cap mem v j arg rd data _ fit
  change ShrinkOldHalves.PlacedPackets X side _ _ (SliceLookup.physical q get) _ arg 0
  rw [eqn]
  exact NamedPackets.placed_readback B i X sel _ v h x ⟨0,2*n*n⟩ priv fields

end
end OAI.Computability.MultitapeWeakETH.ShrinkMap
