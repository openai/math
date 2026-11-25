import OAI.Computability.MultitapeWeakETH.ShrinkDemandAddress
import OAI.Computability.MultitapeWeakETH.PacketSpan

/-! # Reading the unsplit shrinking demand directly from the placed child packets -/

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
local notation "a₀" => a i
local notation "pieces" => Compression.PackingData.pieceCount (2^a₀) (Shrink.colors a₀)

include hr hb in
set_option maxHeartbeats 2400000 in
/-- One fixed program reads both ends of the unsplit CD demand. The bank is
the ordered placement fiber and contains the actual decoded child assignments. -/
theorem cd_program (atD : Bool) :
    ∃ run : Q × Tally → Bits.Word, Poly run ∧ ∀ {g w : ℕ} (ctx : D)
      (X : State a₀ (packingLaneBits a₀ g)) (sel : SelectedScore.Selection B X)
      (base : Word w) (positions blocks n cur cap : ℕ) (mem : Memory w)
      (v : Site X) (j : Fin (order X (SelectedFinish.chosen B X sel) v).length),
      let side := SelectedFinish.chosen B X sel
      let motif := (entry X side v j).1
      let L := BlockProgram.layout B base.val positions blocks
      let q : Q := (ShrinkHidden.query ctx ((levelStart L cur : ℕ) : Word w) cap (siteIndex X v).val,tally j.val)
      let place := X.packingData.shrinkPlace side ∘ X.packingInputIso.site.symm
      ∀ (o : Order {u // v = place u}) (x : Placed place X.network.Half v),
      (∀ p : Word w, read (ctx,wordBits p) = wordBits (mem p.val)) →
      CompiledResident.ShrinkPayload B base positions blocks n cur i X sel mem →
      bank ctx = NamedPackets.placedBank X place v o x w →
      (siteOrder X).length ≤ 2^w → 2*n*n < 2^w → (siteOrder X).length * (2*n*n) ≤ 2^w →
      2^a₀ ≤ n → X.maxWireWidth ≤ n →
      let old := ShrinkRole.MapWitness.placedOld B i X sel v x
      let bits := run (q,tally (X.packingWidth motif.1))
      (∀ (h : v = packedSiteEquiv (X.packingData.placement side (X.packingData.C motif))), atD = false →
        bits = List.ofFn (X.packingData.localCWord X.packingWidth side motif
          (X.packingData.shrinkPlacedHalf X.packingWidth side _ h old))) ∧
      (∀ (h : v = packedSiteEquiv (X.packingData.roleD side motif)), atD = true →
        bits = List.ofFn (X.packingData.localDWord X.packingWidth side motif
          (X.packingData.shrinkPlacedHalf X.packingWidth side _ h old))) := by
  obtain ⟨cell,cc,stored⟩ := NamedPackets.placed_memory
  obtain ⟨offset,oc,oe⟩ := ShrinkHidden.expression read hr ((demandHeader a₀).field (2^a₀) pieces atD)
  obtain ⟨stride,sc,se⟩ := ShrinkHidden.expression read hr packetStride
  let src (q : Q) := (bank q.1.1.1.1,stride q)
  have cp : Poly src := ((show Poly (fun q : Q => q.1.1.1.1) by fun_prop).compose hb).pair sc
  let run (s : Q × Tally) := NamedPackets.range cell (((src s.1,offset s.1)),s.2)
  have pc : Poly run := (((Easy.fst.poly.compose (cp.pair oc)).pair Easy.snd.poly)).compose
    (NamedPackets.range_poly cell cc)
  refine ⟨run,pc,?_⟩
  intro g w ctx X sel base positions blocks n cur cap mem v j side motif L q place o x rd data bk sites sf space degree width old bits
  let head := ((levelStart L cur : ℕ) : Word w)
  let p : Fin 5 → Word w := publicWords (siteIndex X v).val j.val
  let A : Arena := ⟨0,2*n*n⟩
  let reg := (NamedPackets.placedBank X place v o x w,wordBits ((2*n*n : ℕ) : Word w))
  let priv (addr : Word w) := PrivateFields.bitValue w (cell (reg,wordBits addr))
  have fields := stored X place v o x (2*n*n) sites sf space (fun u hu =>
    (packed_length_le X u (x u hu)).trans (Nat.mul_le_mul (Nat.mul_le_mul_left _ degree) width))
  have srcEq : src q = reg := Prod.ext bk ((se ctx head cap _ _ mem rd).trans
    (congrArg wordBits (packetStride_eval B i X sel base positions blocks n cur mem data p)))
  have ptr := (oe ctx head cap (siteIndex X v).val j.val mem rd).trans (congrArg wordBits
    (cd_address B i X sel base positions blocks n cur mem data v j p rfl rfl atD))
  have wide : 0 < w := by
    have bound := data.words.oldRoom
    by_contra! h
    simp [Nat.eq_zero_of_le_zero h] at bound
  have span : bits = NamedPackets.range cell ((reg,offset q),tally (X.packingWidth motif.1)) :=
    congrArg (fun s => NamedPackets.range cell ((s,offset q),tally (X.packingWidth motif.1))) srcEq
  constructor
  · intro h dir
    rw [dir] at ptr
    rw [span,ptr]
    apply NamedPackets.range_eq cell wide
    exact ShrinkOldHalves.read_C X side motif
      (NamedPackets.placed_readback B i X sel _ v h x A priv fields)
  · intro h dir
    rw [dir] at ptr
    rw [span,ptr]
    apply NamedPackets.range_eq cell wide
    exact ShrinkOldHalves.read_D X side motif
      (NamedPackets.placed_readback B i X sel _ v h x A priv fields)

end
end OAI.Computability.MultitapeWeakETH.ShrinkMap
