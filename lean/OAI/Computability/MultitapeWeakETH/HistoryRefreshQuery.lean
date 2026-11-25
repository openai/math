import OAI.Computability.MultitapeWeakETH.RefreshEntry
import OAI.Computability.MultitapeWeakETH.HistoryChildren

/-! # The refresh call's public operands on the retained chronological log -/

namespace OAI.Computability.MultitapeWeakETH.NativeGrid

open IntegerMultiplication Code Carry Staff Strip VPVNP BurstRAM Compression CompressorRecords
open DyadicBudget DescriptorSpace PortRefresh StackInterpreter
open private clocks from OAI.Computability.MultitapeWeakETH.DescriptorProgram
open private encoded_short from OAI.Computability.MultitapeWeakETH.TerminalLayout
open scoped Fin.CommRing
noncomputable section

variable {k : Type} [Field k] {S : BlockSchedule k} (B : S.Templates)

abbrev RefreshQuery := HistorySite × Bits.Word × Bits.Word
private abbrev regime : Regime RefreshQuery := ⟨size,send,Dom.base _⟩

private def headerInput (q : RefreshQuery) : Tally × Tally := (q.1.1.1.1,q.1.1.2)

private def headerBits (q : RefreshQuery) :=
  let t := headerInput q
  let s := index (4*stepSize B) t.1.length
  let w := CursorBounds.wordBits 1 (scale B s)
  let site := Bits.short w q.1.2.length
  let head := historyHeader B t
  let next := historyHeader B (t.1,()::t.2)
  StackInterpreter.pack fun j : Fin 5 => if j=0 then site else if j=2 then next else head

def refreshQuery (q : RefreshQuery) : RefreshOperands.Query LogQuery :=
  let t := headerInput q
  let s := index (4*stepSize B) t.1.length
  ((((tally s,q.1.1.1.2),historyHeader B t),headerBits B q),q.2,tally (scale B s))

attribute [local irreducible] BlockProgram.script BlockProgram.layout source scale entryMemory

set_option maxHeartbeats 1600000 in
theorem refreshQuery_poly : Poly (refreshQuery B) := by
  obtain ⟨ix,fuel,word⟩ := clocks B
  have vol : Poly (fun q : RefreshQuery => q.1.1.1.1) := by fun_prop
  have ip : Poly (fun q : RefreshQuery => q.1.1.2) := by fun_prop
  have hp : Poly headerInput := vol.pair ip
  have head := hp.compose (historyHeader_poly B)
  have next := (vol.pair ((Code.Poly.const ()).pair ip |>.compose Easy.cons.poly)).compose (historyHeader_poly B)
  have w : Realizes regime (fun q => CursorBounds.wordBits 1 (scale B (index (4*stepSize B) q.1.1.1.1.length))) :=
    vol.compose (show Poly (fun q : Tally => tally (CursorBounds.wordBits 1 (scale B (index (4*stepSize B) q.length)))) from word)
  have site : Realizes regime (fun q => q.1.2.length) := by
    change Poly (fun q : RefreshQuery => tally q.1.2.length)
    simpa only [recover_tally] using (show Poly (fun q : RefreshQuery => q.1.2) by fun_prop)
  have num : Poly (fun q : RefreshQuery => Bits.short (CursorBounds.wordBits 1 (scale B (index (4*stepSize B) q.1.1.1.1.length))) q.1.2.length) :=
    (Figure.of_spoken site).write w
  have bank : Poly (headerBits B) := by
    apply pack_poly
    intro j
    by_cases j₀ : j=0
    · simpa only [ite_eq_left j₀,headerInput] using num
    · by_cases j₂ : j=2
      · simpa only [ite_eq_right j₀,ite_eq_left j₂,headerInput] using next
      · simpa only [ite_eq_right j₀,ite_eq_right j₂] using head
  have cap := fuel.minused (Realizes.fix 24)
  change Poly (fun x : Tally => tally ((scale B (index (4*stepSize B) x.length)+24)-24)) at cap
  have cp : Poly (fun x : Tally => tally (scale B (index (4*stepSize B) x.length))) := by
    simpa only [Nat.add_sub_cancel] using cap
  have idx := vol.compose (show Poly (fun q : Tally => tally (index (4*stepSize B) q.length)) from ix)
  exact ((((idx.pair (show Poly (fun q : RefreshQuery => q.1.1.1.2) by fun_prop)).pair head).pair bank).pair
    (Easy.snd.poly.pair (vol.compose cp)))

def refreshContext (L : Layout) (i site : ℕ) {w : ℕ} (m : Memory w) : LevelRecipe.Context w :=
  ⟨fun j => if j=0 then (site : Word w) else if j=2 then (levelStart L (i+1) : ℕ) else (levelStart L i : ℕ),
    (levelStart L i : ℕ),m⟩

set_option maxHeartbeats 1600000 in
theorem refreshQuery_eq (volume : Tally) (i site : ℕ) (old new : Bits.Word) :
    let s := index (4*stepSize B) volume.length
    let n := scale B s
    let w := CursorBounds.wordBits 1 n
    let L := gridLayout B volume
    ∀ (log : CallProgram.Stores w) (m : Memory w),
      refreshQuery B ((((volume,writes log),tally i),tally site),old,new) =
        RefreshOperands.encode (tally s,writes log) (refreshContext L i site m) old new n := by
  intro s n w L log m
  let x : RefreshQuery := ((((volume,writes log),tally i),tally site),old,new)
  have header : historyHeader B (volume,tally i) = wordBits ((levelStart L i : ℕ) : Word w) := by
    unfold historyHeader
    rw [tally_length]
  have bank : headerBits B x = StackInterpreter.pack (wordBits ∘ (refreshContext L i site m).pub) := by
    unfold headerBits
    apply congrArg (StackInterpreter.pack (K:=Fin 5))
    funext j
    by_cases j₀ : j=0
    · simp only [x,headerInput,j₀,ite_true,tally_length,refreshContext,Function.comp_apply]
      exact (encoded_short w site).symm
    · by_cases j₂ : j=2
      · simp only [x,headerInput,refreshContext,ite_eq_right j₀,ite_eq_left j₂,Function.comp_apply,historyHeader,List.length_cons,tally_length]
        rfl
      · simp only [x,headerInput,refreshContext,ite_eq_right j₀,ite_eq_right j₂,Function.comp_apply,historyHeader,tally_length]
        rfl
  exact Prod.ext (Prod.ext (Prod.ext rfl header) bank) rfl

end
end OAI.Computability.MultitapeWeakETH.NativeGrid
