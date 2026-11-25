import OAI.Computability.MultitapeWeakETH.ShrinkDemandAddress
import OAI.Computability.MultitapeWeakETH.HiddenLookup

/-! # Reading a selected shrinking map's shared hidden wire by its dense ID -/

namespace OAI.Computability.MultitapeWeakETH.ShrinkMap

open IntegerMultiplication Code VPVNP BurstRAM Compression Compression.ShrinkMotif
open NetworkKernel PairSimulation LocalHistory NativeGrid CompressorRecords ShrinkHistoryRows
open DescriptorSpace PhaseRecipe ShrinkBlockInputs MapResidentRows
open private publicWords from OAI.Computability.MultitapeWeakETH.ShrinkHiddenRecipe
open scoped Classical Fin.CommRing
noncomputable section

def sharedKey (a : ℕ) (t : Fin 4) := ((ordinal a).mul (.lit 4)).add (.lit t.val)

private theorem shared_room {w a g : ℕ} (X : State a (packingLaneBits a g)) (cut : ℕ)
    (fit : ShrinkInput.termEnd X cut 10 < 2^w) : (hiddenOrder X).length ≤ 2^w := by
  change ShrinkTermInputs.motifCount X * 4 ≤ _
  rw [ShrinkTermSelection.motifCount_eq]
  let M := ShrinkTermSelection.bundles X * ShrinkTermSelection.ranks a
  change ShrinkInput.stop X cut + 2*M + M*10 < 2^w at fit
  change M*4 ≤ _
  omega

variable {D k : Type} [Codec D] [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
  (read : D × Bits.Word → Bits.Word) (hr : Poly read) (bank : D → List Bits.Word × List Bits.Word) (hb : Poly bank)

include hr hb in
set_option maxHeartbeats 600000 in
/-- Both ends of each absorbed edge read the same ID and field, even if
the selected row lies at either end of a loop. -/
theorem shared_program (t : Fin 4) :
    ∃ run : ShrinkHidden.Indexed D → Bits.Word, Poly run ∧ ∀ {g w : ℕ} (ctx : D)
      (X : State (a i) (packingLaneBits (a i) g)) (sel : SelectedScore.Selection B X)
      (base : Word w) (positions blocks n cur cap : ℕ) (mem : Memory w)
      (v : Site X) (j : Fin (order X (SelectedFinish.chosen B X sel) v).length),
      let side := SelectedFinish.chosen B X sel
      let m := rowMotif X side v j
      let L := BlockProgram.layout B base.val positions blocks
      let q := (ShrinkHidden.query ctx ((levelStart L cur : ℕ) : Word w) cap (siteIndex X v).val,tally j.val)
      ∀ (widths : X.packingData.Motif → Bool × Fin 4 → ℕ)
        (h : Placed (X.packingData.shrinkInternalOwner side) (internalLabel widths side) v)
        (own : v = X.packingData.shrinkInternalOwner side (m,t)),
      let rows := ShrinkHiddenSlots.rows X side widths v h
      (∀ p : Word w, read (ctx,wordBits p) = wordBits (mem p.val)) →
      CompiledResident.ShrinkPayload B base positions blocks n cur i X sel mem →
      bank ctx = (rows.map (fun r => wordBits (r.1 : Word w)),rows.map Prod.snd) →
      run q = List.ofFn (RAMSerialization.wordBits _ (h (m,t) own)) := by
  obtain ⟨key,cost,correct⟩ := ShrinkHidden.expression read hr (sharedKey (a i) t)
  let run (q : ShrinkHidden.Indexed D) := ShrinkHidden.fetch (key q,bank q.1.1.1.1)
  have cp : Poly run := (cost.pair ((show Poly (fun q : ShrinkHidden.Indexed D => q.1.1.1.1) by fun_prop).compose hb)).compose ShrinkHidden.fetch_poly
  refine ⟨run,cp,?_⟩
  intro g w ctx X sel base positions blocks n cur cap mem v j side m L q widths h own rows rd data bk
  let p : Fin 5 → Word w := publicWords (siteIndex X v).val j.val
  let head := ((levelStart L cur : ℕ) : Word w)
  have dense := (item_read B i X sel base positions blocks n cur mem data v j p rfl rfl).1
  have kword : (sharedKey (a i) t).eval p head mem = (ShrinkHiddenSlots.id X (m,t) : Word w) := by
    change (ordinal (a i)).eval p head mem * 4 + (t.val : Word w) = _
    rw [dense,ShrinkHiddenSlots.id_eq,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
    rfl
  have selected := (correct ctx head cap (siteIndex X v).val j.val mem rd).trans (congrArg wordBits kword)
  change ShrinkHidden.fetch (key q,bank ctx) = _
  rw [bk,selected]
  exact ShrinkHidden.hidden_field X side widths v (shared_room X _ data.bounds.termRoom) h (m,t) own

end
end OAI.Computability.MultitapeWeakETH.ShrinkMap
