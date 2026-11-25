import OAI.Computability.MultitapeWeakETH.ShrinkKernelReader

/-! # Private shrinking-kernel choices on the native chronological history -/

namespace OAI.Computability.MultitapeWeakETH.NativeGrid

open IntegerMultiplication Code VPVNP BurstRAM Compression Compression.ShrinkMotif PairSimulation LocalHistory
open NetworkKernel CompressorRecords DescriptorSpace TraversalRows TraversalRoles DyadicBudget ShrinkBlockInputs ShrinkMap MotifConversion
open scoped Classical Fin.CommRing
noncomputable section

private theorem readChoices {H X : Type} (secret : X → H) (word : H → Bits.Word)
    (names : X → List Tally) (keys fields : H → List Bits.Word)
    (hidden : HistorySite × Bits.Word → ShrinkHidden.Parsed) (kernel : ShrinkQuery → Option (List Tally))
    (point : HistorySite) (args : NamedPackets.Bank × Bits.Word) (bits tail : Bits.Word) (labels : List Tally)
    (decode : ∀ ids vs, hidden (point,bits) = (ids,some (vs,tail)) ↔
      ∃ h, ids = keys h ∧ vs = fields h ∧ bits = word h ++ tail)
    (check : ∀ h, kernel (point,args,keys h,fields h) = some labels ↔
      ∃ x, secret x = h ∧ labels = names x) :
    readKernel hidden kernel ((point,args),bits) = some (labels,tail) ↔
      ∃ x, bits = word (secret x) ++ tail ∧ labels = names x := by
  rw [readKernel_iff]
  constructor
  · rintro ⟨ids,vs,found,ran⟩
    obtain ⟨h,rfl,rfl,suffix⟩ := (decode ids vs).mp found
    obtain ⟨x,same,emitted⟩ := (check h).mp ran
    exact ⟨x,same.symm ▸ suffix,emitted⟩
  · rintro ⟨x,suffix,emitted⟩
    exact ⟨_,_,(decode _ _).mpr ⟨_,rfl,rfl,suffix⟩,(check _).mpr ⟨_,rfl,emitted⟩⟩

variable {k R : Type} [_root_.Field k] [CommRing R] {S : BlockSchedule k} (B : S.Templates)
attribute [local irreducible] BlockProgram.script BlockProgram.layout source scale entryMemory executeLevels

set_option allowUnsafeReducibility true in
attribute [local reducible] PackingData.shrinkTermLayout
set_option allowUnsafeReducibility true in
attribute [local irreducible] ShrinkEnergy.chosenLayout
set_option maxRecDepth 7000 in
set_option maxHeartbeats 5000000 in
/-- With the old and parent packets supplied, acceptance reads exactly a hidden
assignment and the resident coefficient sequence of one scheduled kernel choice. -/
theorem history_shrink_read (i : Fin S.steps) (number : (parameterData B.shrink).Entry → ℕ)
    (f : B.Entry → R) (hf : B.IsSolution f) :
    ∃ run : ShrinkReadQuery → Option (List Tally × Bits.Word), Poly run ∧ ∃ s₀ : ℕ, ∀ volume : Tally,
      let s := index (4*stepSize B) volume.length
      let n := scale B s
      let w := CursorBounds.wordBits 1 n
      let u := stepSize B*s
      let X := source B s
      let initial : TaggedLayer := ⟨leafLayer (siteOrder X),.cursor⟩
      let L := gridLayout B volume
      let base := entryMemory B (3*u) u n s w
      let E := B.execute f hf s (lanes_fit B s) X
      s₀ ≤ s → ∀ (path : E.Choices) (log : CallProgram.Stores w),
        let past := executeLevels B f hf s (lanes_fit B s) X path
        let m := memory base log
        CompiledResident.resident B f hf 0 X.positions s n initial
          (Frame.data (k:=8) (BlockHeaderRun.header w L 0+6) base) past (E.finalState path) m →
        ∀ (j : Fin past.length) {g : ℕ} (z : SiteArguments B i g) (selector : List Bool),
          (past[j.val]'j.isLt) = shrinkLevel B f hf i z.state z.choice selector →
          ∀ (bits tail : Bits.Word) (labels : List Tally),
          let buffers := z.buffers (tally s,writes log) w
          let point : HistorySite := (((volume,writes log),tally j.val),tally (MapResidentRows.siteIndex z.state z.owner).val)
          run ((point,buffers.1.1.2,buffers.1.2),bits) = some (labels,tail) ↔
            ∃ x : (B.shrinkPassWitnesses f hf i rfl z.state z.choice z.owner z.old z.parent).Choice,
              bits = ShrinkHiddenGuess.stream (hiddenRows z x.1) ++ tail ∧
              labels = (ShrinkRole.MapWitness.emitted B f hf i z.state z.choice z.owner z.old z.parent x).map (tally ∘ number) := by
  obtain ⟨hidden,hp,N,he⟩ := history_hidden B i f hf
  obtain ⟨kernel,kp,M,ke⟩ := history_shrink B i number f hf
  refine ⟨readKernel hidden kernel,readKernel_poly hp kp,max N M,?_⟩
  intro volume s n w u X initial L base E hs path log past m resident j g z selector occurrence bits tail labels buffers point
  let roomH := (le_max_left N M).trans hs
  let roomK := (le_max_right N M).trans hs
  let keys (h : HiddenAt z) := (hiddenRows z h).map (fun e => wordBits (e.1 : Word w))
  let fields (h : HiddenAt z) := (hiddenRows z h).map Prod.snd
  have decode (ids vs) : hidden (point,bits) = (ids,some (vs,tail)) ↔ ∃ h : HiddenAt z,
      ids = keys h ∧ vs = fields h ∧ bits = ShrinkHiddenGuess.stream (hiddenRows z h) ++ tail :=
    he volume roomH path log resident j z.state z.choice selector occurrence z.owner bits ids vs tail
  have call (h : HiddenAt z) :
      kernel (point,(buffers.1.1.2,buffers.1.2),keys h,fields h) = checked ((assign z h).results number) :=
    ke volume roomK path log resident j (assign z h) selector occurrence
  exact readChoices (fun x : (B.shrinkPassWitnesses f hf i rfl z.state z.choice z.owner z.old z.parent).Choice => x.1)
    (fun h => ShrinkHiddenGuess.stream (hiddenRows z h))
    (fun x => (ShrinkRole.MapWitness.emitted B f hf i z.state z.choice z.owner z.old z.parent x).map (tally ∘ number))
    keys fields hidden kernel point _ bits tail labels decode
    (fun h => (congrArg (· = some labels) (call h)).to_iff.trans (assigned_labels z number f hf h labels))

end
end OAI.Computability.MultitapeWeakETH.NativeGrid
