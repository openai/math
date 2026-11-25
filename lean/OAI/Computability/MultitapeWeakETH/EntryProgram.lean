import OAI.Computability.MultitapeWeakETH.HeaderProgram
import OAI.Computability.MultitapeWeakETH.InitialBoundary
import OAI.Computability.MultitapeWeakETH.NativeScale

/-! # Physical initialization of the formula scheduler on a binary address -/

namespace OAI.Computability.MultitapeWeakETH.NativeGrid

open VPVNP Compression CompressorRecords DescriptorSpace BurstRAM CursorBounds DyadicBudget
open IntegerMultiplication Code Carry Staff Strip CNFNetwork.InitialIncidence
open private schedulerMemory from OAI.Computability.MultitapeWeakETH.InitialBoundary
open private chooseEq from OAI.Computability.MultitapeWeakETH.IncidenceProgram
open private source_shape from OAI.Computability.MultitapeWeakETH.NativeScale
open scoped Classical Fin.CommRing
noncomputable section

private def bankNumber (ar : ℕ) : Fin 6 → ℕ := ![9,11+ar,7,8,6,6]

private theorem bank_values (ar w : ℕ) (c : Fin 6) :
    Workspace.bank ar (0 : BurstRAM.Word w) c = CursorRAM.encode w (bankNumber ar c) := by
  fin_cases c <;> simp [Workspace.bank,LiveStageLink.publicData,Schedule.Ports.data,Workspace.ports,bankNumber,
    Fin.snoc] <;> rfl

abbrev MemoryQuery := Tally × Bits.Word
private abbrev memoryRegime : Regime MemoryQuery := ⟨size,send,Dom.base _⟩

variable {k : Type} [Field k] {S : BlockSchedule k} (B : S.Templates)

/-- The grid index is supplied in unary and the random access address in
binary. One uniform polynomial-time tape program returns the exact native
word in the formula scheduler's starting memory. -/
theorem entry_program :
    ∃ read : MemoryQuery → Bits.Word, Poly read ∧ ∀ q,
      let s := q.1.length
      let u := stepSize B*s
      let n := scale B s
      Bits.value (read q) = (entryMemory B (3*u) u n s (wordBits 1 n) (Bits.value q.2)).val := by
  let ρ := memoryRegime
  let s (q : MemoryQuery) := q.1.length
  let u (q : MemoryQuery) := stepSize B*s q
  let g (q : MemoryQuery) := 3*u q
  let n (q : MemoryQuery) := scale B (s q)
  let w (q : MemoryQuery) := wordBits 1 (n q)
  let x (q : MemoryQuery) := Bits.value q.2
  let ar := Schedule.arity (BlockProgram.script B).catalog
  let D := S.degreeExponent 0
  let L (q : MemoryQuery) := BlockProgram.layout B 0 (source B (s q)).positions (s q)
  let nat := fun t => Figure.natural (r:=ρ) t
  have sz : Realizes ρ s := by
    change Poly (fun q : MemoryQuery => tally q.1.length)
    simpa only [recover_tally] using (Easy.fst (X:=Tally) (Y:=Bits.Word)).poly
  have un : Realizes ρ u := (Realizes.fix (stepSize B)).times sz
  have gn : Realizes ρ g := (Realizes.fix 3).times un
  have nn : Figure ρ n := (nat 2).repeated ((Realizes.fix 16).times un)
  let width := ((Realizes.fix 1).times nn.short_log).plus (Realizes.fix 10)
  have wn : Realizes ρ w := by
    convert (((width.times width).times width).times width) using 1
    funext q
    dsimp [w,CursorBounds.wordBits,addressBits,BurstRAM.addressWidth]
    ring
  let modsize := (nat 2).repeated wn
  have addr : Figure ρ x := ⟨Prod.snd,Easy.snd.poly,fun _ => rfl⟩
  have P : Figure ρ (fun q => (source B (s q)).positions) := by
    convert (((nat 8).multiplied (Figure.of_spoken un)).added (nat 4)).multiplied ((nat 2).repeated gn) using 1
    funext q
    exact (source_shape B (s q)).1
  have slots := P.multiplied (nat (slotDegree S))
  have arraySize : Figure ρ (fun q => tableWords (L q)) := slots.multiplied (nat (BlockProgram.fieldCount B))
  have stride : Figure ρ (fun q => levelWords (L q)) :=
    ((nat 66).added ((nat 6).multiplied slots)).added ((nat 6).multiplied arraySize)
  have levels : Figure ρ (fun q => (L q).levels) := (nat 1).added ((nat (S.steps+1)).multiplied (Figure.of_spoken sz))
  have rows : Figure ρ (fun q => directoryRows (L q)) := by
    convert (nat (BlockProgram.initial B).length).added
      ((Figure.of_spoken sz).multiplied (nat (BlockProgram.block B).length)) using 1
    funext q
    exact LevelFields.tight_rows ..
  have head : Figure ρ (fun q => levelStart (L q) 0) := by
    convert (nat (9+(ar+1)+1)).added (rows.multiplied (nat (ar+3))) using 1
    funext q
    simp only [levelStart,Nat.zero_mul,Nat.add_zero]
    rfl
  have start : Figure ρ (fun q => incidenceStart (L q) 0) := head.added (nat 66)
  have arrays : Figure ρ (fun q => arrayBase (L q) 0) := start.added ((nat 6).multiplied slots)
  have arena : Figure ρ (fun q => endAddress (L q)) := by
    convert head.added (levels.multiplied stride) using 1
    funext q
    simp only [endAddress,levelStart,Nat.zero_mul,Nat.add_zero]
  let tag := Schedule.Online.calendarIndex (BlockProgram.script B).size (BlockProgram.script B).size
  let old (q : MemoryQuery) := schedulerMemory ar (directoryRows (L q)) (levelWords (L q)) (LiveStageLink.tagWord (w q) tag)
  have bank := selectField (ρ:=ρ) (f:=fun c _ => bankNumber ar c) (fun q => Fin.ofNat 6 (x q))
    (addr.modded (nat 6)) (fun c => nat _)
  have inherited : Figure ρ (fun q => (old q (x q)).val) := by
    let setup := chooseEq addr (nat 6) (nat tag.val) (chooseEq addr (nat 7) (nat 4)
      (chooseEq addr (nat 8) rows (chooseEq addr (nat (10+ar)) stride (nat 0))))
    convert (bank.variant setup (addr.compare_ (nat 6))).modded modsize using 1
    funext q
    dsimp only [old,schedulerMemory]
    split_ifs <;> first | rw [bank_values]; rfl | rfl
  exact level_program D gn un wn nn addr old inherited head start arena levels (nat 54) arrays arraySize

end
end OAI.Computability.MultitapeWeakETH.NativeGrid
