import OAI.Computability.MultitapeWeakETH.ShrinkSupplyFrame
import OAI.Computability.MultitapeWeakETH.SliceColumn
import OAI.Computability.MultitapeWeakETH.SupplyPacket

/-! # Gathering a surviving supply word from a selected parent packet -/

namespace OAI.Computability.MultitapeWeakETH.ShrinkMap

open IntegerMultiplication Code VPVNP BurstRAM Compression Compression.ShrinkMotif
open NetworkKernel PairSimulation LocalHistory NodeArguments NativeGrid CompressorRecords
open DescriptorSpace ShrinkBlockInputs MapResidentRows ShrinkSlots ShrinkSliceSweep
open ShrinkSurvivingOperands
open private publicWords from OAI.Computability.MultitapeWeakETH.ShrinkHiddenRecipe
open scoped Classical Fin.CommRing
noncomputable section

variable {D k : Type} [Codec D] [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
  (read : D × Bits.Word → Bits.Word) (hr : Poly read) (packet : D → Bits.Word) (hp : Poly packet)
local notation "Q" => ShrinkHidden.Indexed D
local notation "profile" => subdivisions (2^(a i)) (Shrink.colors (a i)) (2^(b i))

include hr hp in
set_option maxHeartbeats 1600000 in
/-- The reverse copies reassemble exactly the incident endpoint of the surviving
supply. Incoming and outgoing calls read their respective native half-slots. -/
theorem surviving_program (dir : Bool) (t : Fin 4) :
    ∃ run : Q × Tally → Bits.Word, Poly run ∧ ∀ {g w : ℕ} (ctx : D)
      (X : State (a i) (packingLaneBits (a i) g)) (sel : SelectedScore.Selection B X)
      (base : Word w) (positions blocks n cur cap : ℕ) (mem : Memory w)
      (v : Site X) (j : Fin (order X (SelectedFinish.chosen B X sel) v).length),
      let side := SelectedFinish.chosen B X sel
      let m := rowMotif X side v j
      let L := BlockProgram.layout B base.val positions blocks
      let q : Q := (ShrinkHidden.query ctx ((levelStart L cur : ℕ) : Word w) cap (siteIndex X v).val,tally j.val)
      let Y := X.shrinkNext B.shrink (S.shrink i) sel
      let u := ShrinkSurvivingOperands.site X side m t dir
      let width := branchWidth X B.shrink sel
      ∀ z : Y.network.Half u,
      (∀ p : Word w, read (ctx,wordBits p) = wordBits (mem p.val)) →
      CompiledResident.ShrinkPayload B base positions blocks n cur i X sel mem →
      packet ctx = packed Y u z → (packed Y u z).length ≤ 2*n*n → (packed Y u z).length ≤ 2^w →
      width m t ≤ 2^w →
      run (q,tally (width m t)) = List.ofFn (operand X side profile width (X.shrinkStateIndex (S.shrink i) side)
        (S.shrink i).count_pos m t dir z) := by
  choose eval ep ev using ShrinkHidden.expression read hr
  let cell (q : Q × Bits.Word) := OperandSpan.cell (packet q.1.1.1.1.1,q.2)
  have cp : Poly cell := (((show Poly (fun q : Q × Bits.Word => q.1.1.1.1.1) by fun_prop).compose hp).pair
    Easy.snd.poly).compose OperandSpan.cell_poly
  let prior : Q × Bits.Word → Bool := fun _ => false
  let setups (l : Fin (profile t)) := (supplyHeader (a i)).setup (2^(b i)) profile t dir l
  let col := SliceLookup.column eval cell prior setups (List.finRange (profile t))
  have cc : Poly col := SliceLookup.column_poly eval ep cell prior cp (Code.Poly.const false) setups _
  let run (x : Q × Tally) := NamedPackets.range col ((x.1,eval (.lit 0) x.1),x.2)
  have cost : Poly run := (((Easy.fst.poly.pair (Easy.fst.poly.compose (ep (.lit 0)))).pair Easy.snd.poly)).compose
    (NamedPackets.range_poly col cc)
  refine ⟨run,cost,?_⟩
  intro g w ctx X sel base positions blocks n cur cap mem v j side m L q Y u width z rd data pk plen words endFit
  let head := ((levelStart L cur : ℕ) : Word w)
  let p : Fin 5 → Word w := publicWords (siteIndex X v).val j.val
  let arena : Arena := ⟨0,2*n*n⟩
  let slots := X.shrinkStateIndex (S.shrink i) side
  let term := ShrinkInput.termHead (w:=w) X (tableBase L cur (0 : Fin 6))
  let alloc := selectedAllocation B.shrink X sel term 10 (tableBase L cur (2 : Fin 6)) profile
  let bank := alloc.row (ShrinkMotifOrder.stateNumber X m,t)
  let rows := ShrinkSurvivingColumn.row X side profile width slots m t dir z arena 0 0 bank
  have one (e : PhaseRecipe.Expr) := ev e ctx head cap (siteIndex X v).val j.val mem rd
  have stored := OperandSpan.packet_at_zero (w:=w) (packed Y u z) (2*n*n) plen words
  have record (l) : (rows l).Recorded (setups l) p head mem :=
    supply_recorded B i X sel base positions blocks n cur mem data v j p rfl rfl t dir l z
  have priv : SliceLookup.physical (w:=w) q cell = OperandSpan.memory (packed Y u z) := by
    funext addr
    change PrivateFields.bitValue w (OperandSpan.cell (packet ctx,wordBits addr)) = _
    rw [pk]
    rfl
  have reads (l) : (rows l).reads (SliceLookup.physical (w:=w) q cell) := by
    rw [priv]
    exact ShrinkSurvivingColumn.reads X side profile width slots m t dir z arena 0 0 bank
      _ stored.1 stored.2 l
  have room (l) (_ : 0 < (rows l).bits.length) :
      (rows l).destination + (rows l).targetOffset + (rows l).bits.length ≤ 2^w := by
    change 0 + ShrinkSurvivingFrames.start (width m t) (profile t) l + (rows l).bits.length ≤ _
    rw [Nat.zero_add,ShrinkSurvivingColumn.row_length X side profile width slots m t dir z arena 0 0 bank
      (S.shrink i).count_pos l]
    exact (ShrinkSurvivingFrames.end_le (width m t) (profile t) ((S.shrink i).count_pos t) l).trans endFit
  have image := SliceLookup.column_eq eval cell prior q p head mem one setups rows (List.finRange _) record reads room
  have write := ShrinkSurvivingColumn.writes_operand X side profile width slots m t dir z arena 0 0 bank
    (S.shrink i).count_pos (SliceLookup.physical (w:=w) q prior)
  have wide : 0 < w := by
    by_contra! h
    have bound := data.words.oldRoom
    simp [Nat.eq_zero_of_le_zero h] at bound
  change NamedPackets.range col ((q,eval (.lit 0) q),tally _) = _
  rw [one (.lit 0)]
  apply NamedPackets.range_eq col wide q 0
  intro l
  have fit : 0 + (List.ofFn (operand X side profile width slots (S.shrink i).count_pos m t dir z)).length ≤ 2^w := by
    simpa only [List.length_ofFn,Nat.zero_add] using endFit
  have bit := PrivateFields.storeBits_read 0 _ (SliceLookup.physical (w:=w) q prior) fit
    (Fin.cast List.length_ofFn.symm l)
  have result := (congrFun (image.trans write) _).trans bit
  simp only [List.getElem_ofFn,Fin.val_cast] at result
  exact result

end
end OAI.Computability.MultitapeWeakETH.ShrinkMap
