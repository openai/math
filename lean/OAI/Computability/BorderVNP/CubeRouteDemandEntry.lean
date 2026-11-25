import OAI.Computability.BorderVNP.CubeRouteDataLayouts
import OAI.Computability.BorderVNP.CubeRouteNativePlacement
import OAI.Computability.BorderVNP.PackedDirectoryRowFields

/-! # Reading the raw packed demands and the assigned cell banks at the native data-writer entry -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM Transmission CubeArena Packing.Directory
open DiagonalResidueRAM (word_val)

variable {w R : ℕ} {pub : Arg → Word w} {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ}

private theorem populated_positive (i : Fin (D.directory pp lp).length) : 0 < (D.directory pp lp)[i.val].width := by
  obtain ⟨_,_,_,h⟩ := (D.mem_directory_iff pp lp _).mp (List.getElem_mem i.isLt)
  exact h

/-- The selected raw demand's receiving cell is in the physical allocation, including
when its position resulted from splitting a field at a processor boundary. -/
theorem BankPlacement.populated_cell_lt {I : Type*} [Fintype I] {C : ℕ} {cell : I → Fin C}
    {id : I ↪ ℕ} {width : I → ℕ} (place : Packing.Directory.BankPlacement D pp lp I cell id width)
    (bound : D.DestinationBounds) (i : Fin (D.directory pp lp).length) :
    (D.directory pp lp)[i.val].cell < C := by
  let b : D.PopulatedBit pp lp := ⟨i,⟨0,populated_positive i⟩⟩
  let x := D.rawBit pp lp b
  let k := D.destinationKey pp lp bound x
  have col := (D.destinationKey_placement pp lp bound x).1
  change (D.row pp lp x.1).cell = (D.keyPlacement pp lp k.1).1 at col
  rw [place.entry] at col
  rw [D.populatedRow pp lp i]
  exact col ▸ (cell (place.key k.1)).isLt

/-- The word-level data writer decodes a physical pin frame without changing any of its dimensions. -/
theorem dataWriter_pins {L : Pins.Layout} {pub : Arg → ℕ} {m : ℕ → ℕ} (h : Pins.Frame L pub m) :
    (DataWriter.layout pub m).pins = L := by
  rcases L with ⟨t,T,p,l,k,w,I,H,S⟩
  simp only [DataWriter.layout,h.team,h.teams,h.processors,h.literal,h.link,h.width,h.ibase,h.hbase,h.starbase]

private theorem demand_congr (m v : ℕ → ℕ) (a : ℕ) (h : ∀ j < 7, m (a+j)=v (a+j)) :
    DataWriter.demandAt m a = DataWriter.demandAt v a := by
  unfold DataWriter.demandAt
  congr 1 <;> first | exact h 0 (by decide) | exact h 1 (by decide) | exact h 2 (by decide) |
    exact h 3 (by decide) | exact h 4 (by decide) | exact h 5 (by decide) | exact h 6 (by decide)

/-- At the actual post-group memory, reading the previously published seven-word directory
and the two-word cell assignments gives all numeric conditions of the native data writer.
The common arena sentinel and the physical packed-cell bounds cover every generated address. -/
theorem DemandInput.of_publication (ar : CubeArena.Layout) (L : Pins.Layout)
    (slotted entry : Memory w) (base : ℕ) (owner : ℕ → Fin (R+1))
    (pinFrame : Pins.Frame L (readings pub) (readings slotted))
    (pointers : readings slotted ((pub 0).val+8) = base ∧ readings slotted ((pub 0).val+12) = ar.records ∧
      readings slotted ((pub 0).val+72) = ar.hostDirectory)
    (keep : ∀ x < ar.header.header, readings entry x =
      readings (Packing.Directory.ISA.publish slotted (pub 0).val base (D.directory pp lp)) x)
    (host : ∀ c < ar.cells, readings entry (ar.hostDirectory+c*2) = (owner c).val ∧
      readings entry (ar.hostDirectory+c*2+1) = ar.cellBank+c*ar.cellStride)
    (low : (pub 0).val+112 ≤ base) (endRaw : base+(D.directory pp lp).length*7 ≤ ar.header.header)
    (sameTeams : D.teams = L.teams) (fields : 0 < D.fields)
    (tails : D.entries*D.description ≤ D.teams*D.processors*(D.literal/2))
    (rows : (D.directory pp lp).length ≤ ar.maxRows) (room : ar.stop < 2^w)
    (teams : 0 < L.teams) (processors : D.processors = L.processors) (literal : D.literal = L.literal)
    (input : L.processors*L.stride ≤ ar.pairBase) (substitute : L.ibase+L.count ≤ ar.pairBase)
    {I : Type*} [Fintype I] {cell : I → Fin ar.cells} {id : I ↪ ℕ} {width : I → ℕ}
    (place : Packing.Directory.BankPlacement D pp lp I cell id width) (bound : D.DestinationBounds)
    (fitBank : ∀ c, DataSlabs.size cell width c ≤ ar.cellStride) :
    DemandInput ar D pp lp owner pub entry ∧ (DataWriter.layout (readings pub) (readings entry)).pins=L := by
  let items := D.directory pp lp
  let d := DataWriter.layout (readings pub) (readings entry)
  let f := (pub 0).val
  let published := Packing.Directory.ISA.publish slotted f base items
  have frame (j : ℕ) (hj : j < 112) (ne : j ≠ 9) : readings entry (f+j) = readings slotted (f+j) := by
    rw [keep _ (by dsimp only [f]; omega)]
    exact congrArg Fin.val (show published (f+j) = slotted (f+j) by
      dsimp only [published]; rw [Packing.Directory.ISA.publish,Function.update_of_ne (by omega : f+j ≠ f+9),
        Packing.Directory.ISA.putWords_outside _ _ _ _ (Or.inl (by dsimp only [f]; omega))])
  have fld (j : ℕ) (hj : j < 112) (ne : j ≠ 9) : frameField (readings pub) (readings entry) j =
      frameField (readings pub) (readings slotted) j := frame j hj ne
  have pins : d.pins = L := by
    apply dataWriter_pins
    constructor <;> first | exact (fld _ (by decide) (by decide)).trans pinFrame.team |
      exact (fld _ (by decide) (by decide)).trans pinFrame.teams | exact (fld _ (by decide) (by decide)).trans pinFrame.processors |
      exact (fld _ (by decide) (by decide)).trans pinFrame.literal | exact (fld _ (by decide) (by decide)).trans pinFrame.link |
      exact (fld _ (by decide) (by decide)).trans pinFrame.ibase | exact (fld _ (by decide) (by decide)).trans pinFrame.hbase |
      exact (fld _ (by decide) (by decide)).trans pinFrame.width | exact (fld _ (by decide) (by decide)).trans pinFrame.starbase
  obtain ⟨head,lab,gw,own,pair,hostDir,rec,stop⟩ := ar.writer_order
  have len : items.length < 2^w := by change base+items.length*7 ≤ _ at endRaw; omega
  have ct : d.count = items.length := by
    change readings entry (f+9) = items.length
    rw [keep _ (by dsimp only [f]; omega)]
    exact (congrArg Fin.val (Packing.Directory.ISA.publish_read slotted f base items (by dsimp only [f]; omega)).1).trans
      (word_val _ _ len)
  have src : d.input = base := (frame 8 (by decide) (by decide)).trans pointers.1
  have dst : d.output = ar.records := (frame 12 (by decide) (by decide)).trans pointers.2.1
  have ownBase : d.owners = ar.hostDirectory := (frame 72 (by decide) (by decide)).trans pointers.2.2
  have fitted (i : Fin items.length) := D.populated_words_fit_of_slabs pp lp bound fields tails
    (W:=w) (by rw [sameTeams,← pinFrame.teams]; exact (slotted _).isLt.le)
    (by rw [processors,← pinFrame.processors]; exact (slotted _).isLt.le)
    (by have := bound.fields; omega)
    (by rw [literal,← pinFrame.literal]; exact (slotted _).isLt)
    (fun k => by rw [place.entry]; have := (cell (place.key k)).isLt; omega)
    (fun k => by
      rw [place.entry,← place.width_eq k]
      have h := (DataSlabs.base_end_le cell id width (place.key k)).trans (fitBank _)
      have pos := Nat.zero_lt_of_lt (cell (place.key k)).isLt
      have scale := Nat.le_mul_of_pos_left ar.cellStride pos
      change ar.cellBank+ar.cells*ar.cellStride < _ at room
      exact h.trans (by omega)) i
  have atRow (i : Fin items.length) : DataWriter.demandAt (readings entry) (d.input+i.val*7) = items[i.val] := by
    rw [src]
    apply (demand_congr (readings entry) (readings published) _ ?_).trans
      (DataWriter.demandAt_published slotted f base items (by dsimp only [f]; omega) i (fitted i))
    intro j hj
    apply keep
    change base+items.length*7 ≤ _ at endRaw
    have := i.isLt; omega
  have ownerRead (i : Fin items.length) := host items[i.val].cell (BankPlacement.populated_cell_lt place bound i)
  have cellFit (i : Fin items.length) : items[i.val].cell < ar.cells := BankPlacement.populated_cell_lt place bound i
  change base+items.length*7 ≤ ar.header.header at endRaw
  have prefit : 0 < L.processors := processors ▸ bound.processors
  have strideFit : L.stride < 2^w :=
    ((Nat.le_mul_of_pos_left _ prefit).trans (input.trans stop)).trans_lt room
  refine ⟨⟨?_,dst,ct.symm,atRow,fun i => ?_⟩,pins⟩
  · constructor
    · omega
    · change 0 < d.pins.teams; rwa [pins]
    · change d.pins.stride < _; rwa [pins]
    · change d.output+d.count*7 < _; rw [dst,ct]; change items.length ≤ _ at rows; omega
    · constructor
      · left; rw [src,ct,dst]; omega
      · intro i hi
        let j : Fin items.length := ⟨i,ct ▸ hi⟩
        change d.owners+(DataWriter.demandAt _ _).cell*2+2 ≤ d.output ∨ _
        rw [atRow j,ownBase,dst]; left; have := cellFit j; omega
    · change ∀ i < d.count, DataWriter.RowFits w d (readings entry) i
      intro i hi
      let j : Fin items.length := ⟨i,ct ▸ hi⟩
      have hr := atRow j
      have positive := populated_positive (D:=D) (pp:=pp) (lp:=lp) j
      have limit := place.deliveredAt_lt bound ar.cellBank ar.cellStride fitBank ⟨j,⟨0,positive⟩⟩
      change ar.cellBank+items[j.val].cell*ar.cellStride+items[j.val].slot+0 < ar.stop at limit
      constructor
      · rw [src]; have := j.isLt; change i < items.length at this; omega
      · rw [hr,ownBase]; have := cellFit j; omega
      · change readings entry (d.owners+(DataWriter.demandAt _ _).cell*2+1)+(DataWriter.demandAt _ _).slot < _
        rw [hr,ownBase,(ownerRead j).2]; omega
      · rw [hr,pins]
        exact (D.source_below pp lp (List.getElem_mem j.isLt) bound.processors positive L processors literal
          ar.pairBase input substitute).trans_le (stop.trans room.le)
  · change readings entry (d.owners+_*2) = _ ∧ readings entry (d.owners+_*2+1) = _
    rw [ownBase]; exact ownerRead i

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
