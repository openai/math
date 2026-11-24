import OAI.Computability.VPVNP.CompressorShrinkResidentLayout
import OAI.Computability.VPVNP.CompressorShrinkTermSelection
import OAI.Computability.VPVNP.PairSimulationMapResidentInputs

/-!
# Reading a shrinking map occurrence and its demand-grid point

The count and ID arrays published in the old level's header at offsets 34
and 35 are indexed by packed site. Each ID has the dense motif ordinal
as its quotient by six and the party as its remainder. The quotient indexes
the term table published at offsets 36 and 37, whose first word selects
the demand-grid point for that occurrence.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace PairSimulation.MapResidentRows

open BurstRAM BurstRAM.PrivateRAM Compression Compression.PackingData CompressorRecords LocalHistory
open MotifGrid MotifBlocks MotifConversion ShrinkMotif
open scoped Classical Fin.CommRing

variable {a g w : ℕ} (X : State a (packingLaneBits a g))

/-- A packed site in the selected shrinking layout. -/
abbrev Site := (X.Base × BitWord (Shrink.J a)) × BitWord g

/-- The site numeral used by the count and ID arrays. -/
abbrev siteIndex (site : Site X) := (ShrinkHistoryRows.packedOrder X).entries.symm site

/-- The restriction of dense motif-and-party order to one packed site. -/
abbrev order (layout : Bool) (site : Site X) :=
  ShrinkHistoryRows.residents (ShrinkHistoryRows.mapOrder X)
    (fun e => X.packingData.shrinkPartySite layout e.1 e.2) site

/-- The motif and party of a position in a packed site’s ordered map row. -/
abbrev entry (layout : Bool) (site : Site X) (r : Fin (order X layout site).length) :=
  ((order X layout site).entries r).val

/-- The term-table ordinal of a shrinking motif. -/
abbrev ordinal (m : X.packingData.Motif) := (shrinkMotifOrder X).entries.symm m

/-- The number of map occurrences at each packed site. -/
abbrev capacity (a : ℕ) := ShrinkResidentLayout.rowCapacity a true

/-- The compressor’s map directory specialized to the selected layout. -/
abbrev Directory (layout : Bool) (p : Fin 6 → Word w) (mem : Memory w) :=
  ShrinkHistoryRows.Directory (ShrinkHistoryRows.mapOrder X) (ShrinkHistoryRows.packedOrder X)
    (fun e => X.packingData.shrinkPartySite layout e.1 e.2) p mem

theorem length_eq (layout : Bool) (site : Site X) : (order X layout site).length = capacity a := by
  change Fintype.card {e : X.packingData.Motif × Fin 6 //
    site = X.packingData.shrinkPartySite layout e.1 e.2} = _
  exact (Fintype.card_congr (Equiv.subtypeEquivRight (fun _ => eq_comm))).trans
    (ShrinkHistoryRows.map_count X layout site)

variable {layout : Bool} {p : Fin 6 → Word w} {mem : Memory w}

theorem count_read (rows : Directory X layout p mem) (site : Site X) :
    (mem ((p 3).val + (siteIndex X site).val)).val = capacity a :=
  (rows.count site).trans (length_eq X layout site)

set_option maxHeartbeats 1200000 in
/-- A site ordinal indexes the ordered fiber. The word stored there is
the global motif-and-party ordinal, even if several parties share the site. -/
theorem id_read (rows : Directory X layout p mem) (rowSize : (p 4).val = capacity a)
    (fit : (ShrinkHistoryRows.mapOrder X).length ≤ 2^w) (site : Site X)
    (r : Fin (order X layout site).length) :
    (mem ((p 5).val + (siteIndex X site).val * capacity a + r.val)).val =
      (ordinal X (entry X layout site r).1).val * 6 + (entry X layout site r).2.val := by
  let e := entry X layout site r
  let i := (ShrinkHistoryRows.mapOrder X).entries.symm e
  have h := congrArg Fin.val (rows.idAt site r)
  rw [rowSize] at h
  exact h.trans ((Nat.mod_eq_of_lt (i.isLt.trans_le fit)).trans
    (ShrinkResidentLayout.map_id X e.1 e.2))

theorem id_digits (rows : Directory X layout p mem) (rowSize : (p 4).val = capacity a)
    (fit : (ShrinkHistoryRows.mapOrder X).length ≤ 2^w) (site : Site X)
    (r : Fin (order X layout site).length) :
    let id := mem ((p 5).val + (siteIndex X site).val * capacity a + r.val)
    id.val / 6 = (ordinal X (entry X layout site r).1).val ∧
      id.val % 6 = (entry X layout site r).2.val := by
  dsimp only
  rw [id_read X rows rowSize fit site r]
  have := (entry X layout site r).2.isLt
  omega

/-- The physical arena bounds the count address and even the exclusive
end of the last packed site's map row. -/
theorem directory_fit (first : ℕ) (site : Site X)
    (fit : (ShrinkResidentLayout.layout X first).endAddr < 2^w) :
    let p := (ShrinkResidentLayout.layout X first).params a true w
    (p 3).val + (siteIndex X site).val < 2^w ∧
      (p 5).val + (siteIndex X site).val * capacity a + capacity a < 2^w := by
  let L := ShrinkResidentLayout.layout X first
  have hi : (siteIndex X site).val < L.sites := (siteIndex X site).isLt
  have size : L.size true = L.sites * capacity a := ShrinkResidentLayout.size_eq_rows X first true
  obtain ⟨_,_,_,_,hc,_,hr⟩ := ShrinkResidentLayout.frame X first true fit
  have cend := (L.ranges true).2.2.1
  have rend := (L.ranges true).2.2.2
  have bound := Nat.mul_le_mul_right (capacity a) hi
  rw [Nat.succ_mul] at bound
  change L.endAddr < 2^w at fit
  change (L.params a true w 3).val + (siteIndex X site).val < 2^w ∧
    (L.params a true w 5).val + (siteIndex X site).val * capacity a + capacity a < 2^w
  rw [hc, hr]
  change L.counts true + (siteIndex X site).val < 2^w ∧
    L.rows true + (siteIndex X site).val * capacity a + capacity a < 2^w
  rw [size] at rend
  constructor
  · exact (Nat.add_lt_add_left hi _).trans_le (cend.le.trans
      ((Nat.le_add_right ..).trans (rend.trans fit.le)))
  · rw [Nat.add_assoc]
    exact (Nat.add_le_add_left bound _).trans_lt (rend.trans_lt fit)

set_option maxHeartbeats 900000 in
/-- Read the dense ID from the actual allocated map bank. -/
theorem allocated_id (first : ℕ) (fit : (ShrinkResidentLayout.layout X first).endAddr < 2^w)
    (rows : Directory X layout ((ShrinkResidentLayout.layout X first).params a true w) mem)
    (site : Site X) (r : Fin (order X layout site).length) :
    let p := (ShrinkResidentLayout.layout X first).params a true w
    (mem ((p 5).val + (siteIndex X site).val * capacity a + r.val)).val =
      (ordinal X (entry X layout site r).1).val * 6 + (entry X layout site r).2.val := by
  let L := ShrinkResidentLayout.layout X first
  let p := L.params a true w
  obtain ⟨_,ho,_,_,_,hc,_⟩ := ShrinkResidentLayout.frame X first true fit
  have oldFits : L.size true ≤ 2^w := ho.symm.le.trans (p 0).isLt.le
  exact id_read X (layout := layout) (p := p) (mem := mem) rows hc oldFits site r

end PairSimulation.MapResidentRows

namespace PairSimulation.MapResidentInputs

open BurstRAM BurstRAM.PrivateRAM Compression CompressorRecords MapResidentRows
open MotifGrid MotifBlocks MotifConversion ShrinkMotif
open scoped Classical Fin.CommRing

variable {a g w : ℕ} (X : State a (packingLaneBits a g))
variable {layout : Bool} {mem : Memory w} {pcs regs : ℕ} {reg : Fin 11 ↪ Fin regs}
  {done : Fin pcs} {c d : Config w pcs regs}

/-- The output cursor and stop registers delimit exactly this site's ordered
map row. Registers four and five recover the term head and ten-word stride. -/
theorem HeaderResult.directory (h : HeaderResult reg done mem c d)
    (first : ℕ) (fit : (ShrinkResidentLayout.layout X first).endAddr < 2^w)
    (rows : Directory X layout ((ShrinkResidentLayout.layout X first).params a true w) mem)
    (site : Site X) (siteReg : (c.reg (reg 1)).val = (siteIndex X site).val)
    (term : Word w)
    (pub : Published mem (c.reg (reg 0)) ((ShrinkResidentLayout.layout X first).params a true w 3)
      ((ShrinkResidentLayout.layout X first).params a true w 5) term 10)
    (headerFit : (c.reg (reg 0)).val + 37 < 2^w) :
    let p := (ShrinkResidentLayout.layout X first).params a true w
    let start := (p 5).val + (siteIndex X site).val * capacity a
    d.reg (reg 2) = (start : Word w) ∧ d.reg (reg 3) = ((start+(order X layout site).length : ℕ) : Word w) ∧
      d.reg (reg 4) = term ∧ d.reg (reg 5) = 10 := by
  let p := (ShrinkResidentLayout.layout X first).params a true w
  have cf := (directory_fit X first site fit).1
  have cnt := count_read X rows site
  rw [← siteReg] at cf cnt
  have hr := h.readback (p 3) (p 5) term 10 (capacity a) pub headerFit cf cnt
  simpa only [siteReg, length_eq, Nat.cast_ofNat] using hr

variable {k : Type*} [_root_.Field k] {factor : ℝ}
variable (F : FixedBlock k demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31/16) factor)
variable {dense term : Word w} {cap : ℕ} {s : X.ShrinkSelection F}
  {before : Memory w} {rs : List (Report w)}

private theorem grid_at (terms : ShrinkTermSelection.Written F X dense term 10 cap s before rs)
    (m : X.packingData.Motif) (room : term.val + (ordinal X m).val * 10 < 2^w)
    (retained : mem (term.val + (ordinal X m).val * 10) =
      after before (eventLog rs) (term.val + (ordinal X m).val * 10)) :
    F.grid.demands.toList[(mem (term.val + (ordinal X m).val * 10)).val]? =
      some (demandGrid F demandMass_pos
        (X.packingData.shrinkDemandWidths X.shrinkNumber X.packingWidth m)).val := by
  have hb : (ShrinkTermSelection.rowBase X term 10 m).val =
    term.val + (ordinal X m).val * 10 := Nat.mod_eq_of_lt room
  rw [retained, ← hb]
  exact (terms.fields m).1

private theorem fits_ten {base i n bound : ℕ} (hi : i < n) (fit : base + n*10 ≤ bound) :
    6 < bound ∧ base + i*10 < bound := by omega

private theorem ItemResult.term_selected (h : ItemResult reg done mem c d)
    (m : X.packingData.Motif) (j : Fin 6)
    (ident : (mem (c.reg (reg 2)).val).val = (ordinal X m).val * 6 + j.val)
    (headReg : c.reg (reg 4) = term) (strideReg : c.reg (reg 5) = 10)
    (terms : ShrinkTermSelection.Written F X dense term 10 cap s before rs)
    (termFit : term.val + (LocalHistory.shrinkMotifOrder X).length * 10 ≤ 2^w)
    (retained : mem (term.val + (ordinal X m).val * 10) =
      after before (eventLog rs) (term.val + (ordinal X m).val * 10)) :
    (d.reg (reg 6)).val = (ordinal X m).val ∧ (d.reg (reg 7)).val = j.val ∧
      (d.reg (reg 8)).val = term.val + (ordinal X m).val * 10 ∧
      F.grid.demands.toList[(d.reg (reg 9)).val]? = some (demandGrid F demandMass_pos
        (X.packingData.shrinkDemandWidths X.shrinkNumber X.packingWidth m)).val := by
  obtain ⟨h6,room⟩ := fits_ten (ordinal X m).isLt termFit
  have head : c.reg (reg 4) = (term.val : Word w) :=
    headReg.trans (Fin.ext (Nat.mod_eq_of_lt term.isLt)).symm
  have strideCast : c.reg (reg 5) = ((10 : ℕ) : Word w) := by simpa only [Nat.cast_ofNat] using strideReg
  obtain ⟨hm,hj,ha,hz⟩ := h.readback (ordinal X m).val j term.val 10 h6 ident head strideCast room
  exact ⟨hm,hj,ha,(congrArg (fun z : Word w => F.grid.demands.toList[z.val]?) hz).trans
    (grid_at X F terms m room retained)⟩

set_option maxHeartbeats 1500000 in
/-- At a position of this site's ordered map row, the native reader returns
the dense motif ordinal, its six-valued party, and the demand-grid point
written by the term worker for this motif. -/
theorem ItemResult.selected (h : ItemResult reg done mem c d)
    (first : ℕ) (fit : (ShrinkResidentLayout.layout X first).endAddr < 2^w)
    (rows : Directory X layout ((ShrinkResidentLayout.layout X first).params a true w) mem)
    (site : Site X) (r : Fin (order X layout site).length)
    (cursor : (c.reg (reg 2)).val = ((ShrinkResidentLayout.layout X first).params a true w 5).val +
      (siteIndex X site).val * capacity a + r.val)
    (headReg : c.reg (reg 4) = term) (strideReg : c.reg (reg 5) = 10)
    (terms : ShrinkTermSelection.Written F X dense term 10 cap s before rs)
    (termFit : term.val + (LocalHistory.shrinkMotifOrder X).length * 10 ≤ 2^w)
    (retained : ∀ m : X.packingData.Motif, mem (term.val + (ordinal X m).val * 10) =
      after before (eventLog rs) (term.val + (ordinal X m).val * 10)) :
    let e := entry X layout site r
    (d.reg (reg 6)).val = (ordinal X e.1).val ∧ (d.reg (reg 7)).val = e.2.val ∧
      (d.reg (reg 8)).val = term.val + (ordinal X e.1).val * 10 ∧
      F.grid.demands.toList[(d.reg (reg 9)).val]? = some (demandGrid F demandMass_pos
        (X.packingData.shrinkDemandWidths X.shrinkNumber X.packingWidth e.1)).val := by
  intro e
  refine ItemResult.term_selected X F (dense := dense) (term := term) (cap := cap) (s := s)
    (before := before) (rs := rs) h e.1 e.2 ?_ headReg strideReg terms termFit (retained e.1)
  refine (congrArg (fun n : ℕ => (mem n).val) cursor).trans ?_
  exact allocated_id X (layout := layout) (mem := mem) first fit rows site r

end PairSimulation.MapResidentInputs

end

end VPVNP
end Computability
end OAI
