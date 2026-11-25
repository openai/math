import OAI.Computability.MultitapeWeakETH.HistoryShrink

/-! # Reading the private kernel choice of a selected shrinking site -/

namespace OAI.Computability.MultitapeWeakETH.NativeGrid

open IntegerMultiplication Code VPVNP BurstRAM Compression Compression.ShrinkMotif PairSimulation LocalHistory
open NetworkKernel CompressorRecords ShrinkBlockInputs ShrinkMap MotifConversion
open private bind_poly from OAI.Computability.MultitapeWeakETH.TerminalProgram
open scoped Classical Fin.CommRing
noncomputable section

abbrev ShrinkReadQuery := (HistorySite × (NamedPackets.Bank × Bits.Word)) × Bits.Word

/-- Parse the owned hidden edges once and pass the same keyed fields to all
resident maps. The local result retains the unconsumed private suffix. -/
def readKernel (hidden : HistorySite × Bits.Word → ShrinkHidden.Parsed)
    (kernel : ShrinkQuery → Option (List Tally)) (q : ShrinkReadQuery) : Option (List Tally × Bits.Word) :=
  let h := hidden (q.1.1,q.2)
  h.2.bind fun v => (kernel (q.1.1,q.1.2,h.1,v.1)).bind fun labels => some (labels,v.2)

theorem readKernel_poly {hidden : HistorySite × Bits.Word → ShrinkHidden.Parsed}
    {kernel : ShrinkQuery → Option (List Tally)} (hh : Poly hidden) (hk : Poly kernel) :
    Poly (readKernel hidden kernel) := by
  let h (q : ShrinkReadQuery) := hidden (q.1.1,q.2)
  have hc : Poly h := (show Poly (fun q : ShrinkReadQuery => (q.1.1,q.2)) by fun_prop).compose hh
  let X := ShrinkReadQuery × (List Bits.Word × Bits.Word)
  let query (q : X) : ShrinkQuery := (q.1.1.1,q.1.1.2,(h q.1).1,q.2.1)
  have call : Poly query := by
    exact (show Poly (fun q : X => q.1.1.1) by fun_prop).pair
      ((show Poly (fun q : X => q.1.1.2) by fun_prop).pair
        ((Easy.fst.poly.compose hc.fstCompose).pair (Easy.snd.compose Easy.fst).poly))
  let emit (q : X × List Tally) := some (q.2,q.1.2.2)
  have he : Poly emit := (Easy.snd.pair ((Easy.fst.compose Easy.snd).compose Easy.snd)).poly.compose Easy.some.poly
  let finish (q : X) := (kernel (query q)).bind (fun labels => emit (q,labels))
  have save : Poly finish := bind_poly [] (call.compose hk) he
  exact bind_poly ([],[]) hc.sndCompose save

theorem readKernel_iff (hidden : HistorySite × Bits.Word → ShrinkHidden.Parsed)
    (kernel : ShrinkQuery → Option (List Tally)) (q : ShrinkReadQuery) (labels : List Tally) (tail : Bits.Word) :
    readKernel hidden kernel q = some (labels,tail) ↔ ∃ ids fields,
      hidden (q.1.1,q.2) = (ids,some (fields,tail)) ∧ kernel (q.1.1,q.1.2,ids,fields) = some labels := by
  unfold readKernel
  cases e : hidden (q.1.1,q.2) with
  | mk ids body =>
    cases body with
    | none => simp
    | some v =>
      rcases v with ⟨fields,rest⟩
      cases h : kernel (q.1.1,q.1.2,ids,fields) <;> simp [h,eq_comm,and_comm]

variable {k R : Type} [_root_.Field k] [CommRing R] {S : BlockSchedule k} {B : S.Templates}
  {i : Fin S.steps} {g : ℕ} (z : SiteArguments B i g)

abbrev HiddenAt := Placed (z.state.packingData.shrinkInternalOwner (SelectedFinish.chosen B z.state z.choice))
  (internalLabel (ShrinkPreparedCall.width B.shrink z.state z.choice) (SelectedFinish.chosen B z.state z.choice)) z.owner

def hiddenRows (h : HiddenAt z) := ShrinkHiddenSlots.rows z.state (SelectedFinish.chosen B z.state z.choice)
  (ShrinkPreparedCall.width B.shrink z.state z.choice) z.owner h

def assign (h : HiddenAt z) : SiteArguments B i g := {z with hidden := h}

variable (number : (parameterData B.shrink).Entry → ℕ) (f : B.Entry → R) (hf : B.IsSolution f)
local notation "W" => B.shrinkPassWitnesses f hf i rfl z.state z.choice z.owner z.old z.parent

set_option maxHeartbeats 1100000 in
/-- At fixed child and parent arguments the complete ordered result is exactly
the coefficient sequence of a scheduled witness with the given hidden fields. -/
theorem assigned_labels (h : HiddenAt z) (labels : List Tally) :
    checked ((assign z h).results number) = some labels ↔ ∃ x : (W).Choice,
      x.1 = h ∧ labels = (ShrinkRole.MapWitness.emitted B f hf i z.state z.choice z.owner z.old z.parent x).map
        (tally ∘ number) := by
  let y := assign z h
  constructor
  · intro hit
    obtain ⟨x,same,_⟩ := (y.accepts_iff number f hf).mp (by rw [show checked (y.results number) = some labels from hit]; rfl)
    exact ⟨x,same,Option.some.inj (hit.symm.trans (y.labels number f hf x same))⟩
  · rintro ⟨x,same,rfl⟩
    exact y.labels number f hf x same

end
end OAI.Computability.MultitapeWeakETH.NativeGrid
