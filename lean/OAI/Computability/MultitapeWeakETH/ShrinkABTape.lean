import OAI.Computability.MultitapeWeakETH.ShrinkDemandAddress
import OAI.Computability.MultitapeWeakETH.SliceColumn
import OAI.Computability.VPVNP.PairShrinkCanonicalJob

/-! # Gathering the repartitioned AB shrinking demand on tapes -/

namespace OAI.Computability.MultitapeWeakETH.ShrinkMap

open IntegerMultiplication Code VPVNP BurstRAM Compression Compression.ShrinkMotif
open NetworkKernel PairSimulation LocalHistory NodeArguments NativeGrid CompressorRecords
open DescriptorSpace ShrinkBlockInputs MapResidentRows
open private publicWords from OAI.Computability.MultitapeWeakETH.ShrinkHiddenRecipe
open scoped Classical Fin.CommRing
noncomputable section

variable {D k : Type} [Codec D] [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
  (read : D × Bits.Word → Bits.Word) (hr : Poly read)
local notation "Q" => ShrinkHidden.Indexed D
variable (cell : ShrinkHidden.Indexed D × Bits.Word → Bool) (hc : Poly cell)
local notation "a₀" => a i
local notation "pieces" => Compression.PackingData.pieceCount (2^a₀) (Shrink.colors a₀)
local notation "count" => 2^(Shrink.colors a₀) * 2^a₀ / 4

include hr hc in
set_option maxHeartbeats 1500000 in
/-- Read the old independent halves of every member of the thick fiber,
copy its recorded slice and return the AB word in its new coordinate order. -/
theorem ab_program (dir : Bool) :
    ∃ run : Q × Tally → Bits.Word, Poly run ∧ ∀ {g w : ℕ} (ctx : D)
      (X : State a₀ (packingLaneBits a₀ g)) (sel : SelectedScore.Selection B X)
      (base : Word w) (positions blocks n cur cap : ℕ) (mem : Memory w)
      (v : Site X) (j : Fin (order X (SelectedFinish.chosen B X sel) v).length),
      let side := SelectedFinish.chosen B X sel
      let m := rowMotif X side v j
      let L := BlockProgram.layout B base.val positions blocks
      let q : Q := (ShrinkHidden.query ctx ((levelStart L cur : ℕ) : Word w) cap (siteIndex X v).val,tally j.val)
      let arena : Arena := ⟨0,2*n*n⟩
      let nodes := PortRefresh.ArgumentAddress.siteOrdinal X
      let priv := SliceLookup.physical (w:=w) q cell
      let width := X.packingData.abWidth X.shrinkNumber X.packingWidth m
      ∀ x : X.packingData.PlacedHalf X.packingWidth side (ShrinkOldHalves.abSite X m dir),
      (∀ p : Word w, read (ctx,wordBits p) = wordBits (mem p.val)) →
      CompiledResident.ShrinkPayload B base positions blocks n cur i X sel mem →
      ShrinkOldHalves.PlacedPackets X side arena nodes priv _ x 0 → width ≤ 2^w →
      run (q,tally width) = List.ofFn (ShrinkAB.operand X.packingData X.shrinkNumber X.shrinkOrder X.packingWidth
        ⟨m,rfl⟩ (State.two_le_packingColors _) (Nat.two_pow_pos _) (ShrinkOldHalves.abData X side m dir x)) := by
  choose eval ep ev using ShrinkHidden.expression read hr
  let setups (k : Fin count) := (demandHeader a₀).fields.setup (2^a₀) count pieces dir k.val
  let prior : Q × Bits.Word → Bool := fun _ => false
  let col := SliceLookup.column eval cell prior setups (List.finRange count)
  have cp : Poly col := SliceLookup.column_poly eval ep cell prior hc (Code.Poly.const false) setups _
  let run (x : Q × Tally) := NamedPackets.range col ((x.1,eval (.lit 0) x.1),x.2)
  have rp : Poly run := (((Easy.fst.poly.pair (Easy.fst.poly.compose (ep (.lit 0)))).pair Easy.snd.poly)).compose
    (NamedPackets.range_poly col cp)
  refine ⟨run,rp,?_⟩
  intro g w ctx X sel base positions blocks n cur cap mem v j side m L q arena nodes priv width x rd data ready size
  let head := ((levelStart L cur : ℕ) : Word w)
  let p : Fin 5 → Word w := publicWords (siteIndex X v).val j.val
  let cut := tableBase L cur (0 : Fin 6)
  let first := tableBase L cur (1 : Fin 6)
  let T := packedIncidence L w cur (DemandRAM.oldCount X)
  have one (e : PhaseRecipe.Expr) := ev e ctx head cap (siteIndex X v).val j.val mem rd
  obtain ⟨ab,child,_,_,space⟩ := demand_heads B i X sel base positions blocks n cur mem data v j p rfl rfl
  have G := ShrinkCallHeader.geometry X T cut space
  have geom := ShrinkCanonicalJob.geometry B i X (S.shrink i) sel m base positions blocks cur data.bounds
  let rows (k : Fin count) := ShrinkAB.Physical.row X m G.arcFit G.bucketFit k arena nodes side dir x (first:=first) (dest:=0)
  have record (k : Fin count) : (rows k).Recorded (setups k) p head mem := by
    have countBound : count ≤ pieces := by unfold Compression.PackingData.pieceCount; omega
    have result := ShrinkAB.Physical.recorded X (demandHeader a₀).fields p head mem m ab G.arcFit G.bucketFit
      G.piecesFit k arena side dir x T 0 1 child data.sources.old.incidence G.degreeFit G.regions G.nrows
      (countBound.trans G.cap) data.sources.old.preimages data.sources.old.ranked geom.ab ⟨mem,data.sources.slices.abFields _,fun _ _ _ => rfl⟩
    simpa only [Nat.one_mul,Nat.zero_add] using result
  have reads (k : Fin count) : (rows k).reads priv :=
    ShrinkAB.Physical.reads X m G.arcFit G.bucketFit k arena nodes side dir x priv ready
  have room (k : Fin count) (pos : 0 < (rows k).bits.length) :
      (rows k).destination + (rows k).targetOffset + (rows k).bits.length ≤ 2^w := by
    let member := ShrinkAB.Physical.members X G.arcFit G.bucketFit (X.packingData.bundle m) k
    let slice := X.packingData.demandSlice X.shrinkNumber X.shrinkOrder X.packingWidth _ member ⟨m,rfl⟩
    have len : (rows k).bits.length = slice.length := List.length_ofFn
    have h := ShrinkAB.target_bound X.packingData X.shrinkNumber X.shrinkOrder X.packingWidth
      (⟨m,rfl⟩ : X.packingData.MotifFiber (X.packingData.bundle m)) member (len ▸ pos)
    change 0 + slice.targetOffset + (rows k).bits.length ≤ _
    rw [Nat.zero_add,len]
    exact h.trans size
  have image := SliceLookup.column_eq eval cell prior q p head mem one setups rows (List.finRange count) record reads room
  have wide : 0 < w := by
    by_contra! h
    have bound := data.words.oldRoom
    simp [Nat.eq_zero_of_le_zero h] at bound
  change NamedPackets.range col ((q,eval (.lit 0) q),tally width) = _
  rw [one (.lit 0)]
  apply NamedPackets.range_eq col wide q 0
  intro k
  exact (congrFun image _).trans (ShrinkAB.Physical.writes_operand X m G.arcFit G.bucketFit arena nodes side dir x
    (first:=first) (dest:=0) _ (by simpa only [Nat.zero_add] using size) k)

end
end OAI.Computability.MultitapeWeakETH.ShrinkMap
