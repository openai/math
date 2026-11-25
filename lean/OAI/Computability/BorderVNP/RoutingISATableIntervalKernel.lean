import OAI.Computability.BorderVNP.RoutingISATableIntervalImage

/-! # The seven-word transmission scan on the physical instruction table -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

private theorem width_increment_fits {w i : ℕ} {l : TableLayout} {row : ℕ → TableRow}
    (fit : l.RowsFit w row) (hi : i < l.count) (hn : (row i).first ≠ (row i).second) :
    l.pairWidth row i (l.pairKey (row i).first (row i).second) + (row i).width < 2^w := by
  have h := (l.pairWidth_le_sum row (i := i+1) hi (l.pairKey (row i).first (row i).second)).trans_lt fit.widths
  simpa [TableLayout.pairWidth, Finset.sum_range_succ, hn] using h

set_option maxHeartbeats 2000000 in
/-- The actual record kernel saves the previous pair width in the ordinal array and
increments the indicated pair. All arithmetic is certified from the allocated intervals
and the global width bound, including the carry check on a nonlocal interval. -/
theorem run_tabulateInterval {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (l : TableLayout) (row : ℕ → TableRow) (al : l.Allocated w) (fit : l.RowsFit w row)
    (before : ℕ → ℕ) (initial : l.recordsMatch row before) (i : ℕ) (hi : i < l.count)
    (s : Bank w) (m : Memory w) (hreg : l.ready (.ofWords s m)) (h13 : (s 13).val = i)
    (image : l.IntervalImage row before i (readings m)) :
    BoundedRun pub macros tabulateInterval s m tabulateInterval.slots (fun z =>
      l.ready z ∧ z.reg 13 = i+1 ∧ z.mem = l.storeRecord (row i) i (readings m)) := by
  let z := NatState.ofWords s m
  have h0 : z.reg 0 = 0 := hreg 0 (by decide)
  have h1 : z.reg 1 = 1 := hreg 1 (by decide)
  have h2 : z.reg 2 = 2 := hreg 2 (by decide)
  have h3 : z.reg 3 = l.teams := hreg 3 (by decide)
  have h6 : z.reg 6 = l.records := hreg 6 (by decide)
  have h8 : z.reg 8 = l.widths := hreg 8 (by decide)
  have h11 : z.reg 11 = l.ordinals := hreg 11 (by decide)
  have h12 : z.reg 12 = 7 := hreg 12 (by decide)
  have h13' : z.reg 13 = i := h13
  have hm := image.recordsMatch al initial i hi
  dsimp only at hm
  obtain ⟨hk,hx,hy,hw⟩ := hm
  change z.mem (7*i+l.records) = (row i).kind at hk
  change z.mem (7*i+l.records+1) = (row i).first at hx
  change z.mem (7*i+l.records+2) = (row i).second at hy
  change z.mem (7*i+l.records+3) = (row i).width at hw
  have hmul : i*7 = 7*i := Nat.mul_comm _ _
  have hr2 : 7*i+l.records+1+1 = 7*i+l.records+2 := by omega
  have hr3 : 7*i+l.records+2+1 = 7*i+l.records+3 := by omega
  obtain ⟨hkind,hfirst,hsecond⟩ := fit.labels i hi
  have headroom := al.address (l.contains_record (q := 3) hi (by decide))
  have ordinalroom := al.address (l.contains_offset (a := .ordinals) hi)
  change l.ordinals+i < 2^w at ordinalroom
  have incroom : i+1 < 2^w := Nat.lt_of_le_of_lt hi al.countFits
  have pairroom := al.address (l.contains_offset (a := .widths) (l.pairKey_lt hfirst hsecond))
  let key := l.pairKey (row i).first (row i).second
  have widthroom (hn : (row i).first ≠ (row i).second) : z.mem (l.widths+key)+(row i).width < 2^w := by
    rw [show z.mem (l.widths+key) = _ from image.widths key (l.pairKey_lt hfirst hsecond)]
    exact width_increment_fits fit hi hn
  have calcIndex : (min (row i).first (row i).second)*l.teams+max (row i).first (row i).second+l.widths =
      l.widths+key := Nat.add_comm _ _
  have safe : tabulateInterval.fixedSafe w (readings pub) z := by
    by_cases eq : (row i).first = (row i).second
    · simp (config := { decide := true }) [tabulateInterval, Code.block, requireLt, Code.fixedSafe,
        Code.fixedEval, Code.safeReadOnly, Code.evalNat, addressOpFits, addressOp,
        h1,h2,h3,h6,h11,h12,h13',hmul,hr2,hr3,hk,hx,hy,hkind,hsecond,eq]
      omega
    · have hwfit := widthroom eq
      by_cases ord : (row i).first < (row i).second
      · have hidx := calcIndex
        simp only [min_eq_left ord.le, max_eq_right ord.le] at hidx
        simp (config := { decide := true }) [tabulateInterval, Code.block, requireLt, orderPair, pairAddress,
          Code.fixedSafe, Code.fixedEval, Code.safeReadOnly, Code.evalNat, addressOpFits, addressOp,
          h1,h2,h3,h6,h8,h11,h12,h13',hmul,hr2,hr3,hk,hx,hy,hw,hkind,hfirst,hsecond,eq,ord,hidx]
        change l.widths+key < 2^w at pairroom
        omega
      · have hidx := calcIndex
        simp only [min_eq_right (le_of_not_gt ord), max_eq_left (le_of_not_gt ord)] at hidx
        simp (config := { decide := true }) [tabulateInterval, Code.block, requireLt, orderPair, pairAddress,
          Code.fixedSafe, Code.fixedEval, Code.safeReadOnly, Code.evalNat, addressOpFits, addressOp,
          h1,h2,h3,h6,h8,h11,h12,h13',hmul,hr2,hr3,hk,hx,hy,hw,hkind,hfirst,hsecond,eq,ord,hidx]
        change l.widths+key < 2^w at pairroom
        omega
  apply (tabulateInterval.runFixed pub macros s m safe).mono le_rfl
  rintro _ rfl
  refine ⟨TableLayout.ready_fixed hreg (c := tabulateInterval) (by decide) _, ?_⟩
  change (tabulateInterval.fixedEval (readings pub) z).reg 13 = i+1 ∧
    (tabulateInterval.fixedEval (readings pub) z).mem = l.storeRecord (row i) i z.mem
  by_cases eq : (row i).first = (row i).second
  · simp (config := { decide := true }) [tabulateInterval, Code.block, requireLt, Code.fixedEval,
      Code.evalNat, addressOp, h0,h1,h2,h3,h6,h11,h12,h13',hmul,hr2,hr3,hk,hx,hy,hkind,hsecond,
      eq, TableLayout.storeRecord]
  · by_cases ord : (row i).first < (row i).second
    · have hidx := calcIndex
      simp only [min_eq_left ord.le, max_eq_right ord.le] at hidx
      simp (config := { decide := true }) [tabulateInterval, Code.block, requireLt, orderPair, pairAddress,
        Code.fixedEval, Code.evalNat, addressOp, h1,h2,h3,h6,h8,h11,h12,h13',hmul,hr2,hr3,hk,hx,hy,hw,
        hkind,hfirst,hsecond,eq,ord,hidx, TableLayout.storeRecord,key]
    · have hidx := calcIndex
      simp only [min_eq_right (le_of_not_gt ord), max_eq_left (le_of_not_gt ord)] at hidx
      simp (config := { decide := true }) [tabulateInterval, Code.block, requireLt, orderPair, pairAddress,
        Code.fixedEval, Code.evalNat, addressOp, h1,h2,h3,h6,h8,h11,h12,h13',hmul,hr2,hr3,hk,hx,hy,hw,
        hkind,hfirst,hsecond,eq,ord,hidx, TableLayout.storeRecord,key]

end RoutingISA

end BorderVNP
end Computability
end OAI
