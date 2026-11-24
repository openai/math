import OAI.Computability.VPVNP.CompressorSlotMateColumns
import OAI.Computability.VPVNP.CompressorSlotFillFootprint
import OAI.Computability.VPVNP.CompressorSlotScanFootprint

/-!
# External addresses of the three mate-table passes

The first pass inverts the base permutation. The other two expand that
matching to all lanes, once in each direction. On the reverse pass the
inverse table determines the index of the displacement read. Its entries
remain bounded by the base-port count after the forward expansion.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkSlots

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM SourceTransport
open Compression IncidenceDirectory SlotLevel SlotFillFootprint

variable {a l w : ℕ}

/-- The lifted incidence pass reads the selected base-mate and displacement
columns. It writes one cell in its output column per actual port. -/
theorem actual_scan_footprint (p : Fin 5 → Word w) (reverse : Bool) (Y : State a l)
    (m : Memory w) (rs : List (Report w))
    (hd : (p 0).val = 2^a) (hl : (p 1).val = 2^l)
    (ht : (p 2).val + Fintype.card Y.Base * 2^a ≤ (p 4).val)
    (hs : (p 3).val + Fintype.card Y.Base * 2^a ≤ (p 4).val)
    (fit : (p 4).val + Fintype.card Y.Base * 2^l * 2^a ≤ 2^w)
    (bounded : ∀ e, (m ((p 2).val + (baseOrder Y e).val)).val < Fintype.card Y.Base * 2^a)
    (run : runSegment ((template (SlotIncidencePass.visit reverse) 0).instantiate w p).program
      28 (some 0) m (List.replicate (Fintype.card Y.Base * 2^l * 2^a) []) = some rs) :
    Reads (fun x ↦ InColumn (p 2).val (Fintype.card Y.Base * 2^a) x ∨
      InColumn (p 3).val (Fintype.card Y.Base * 2^a) x) (eventLog rs) ∧
    Writes (InColumn (p 4).val (Fintype.card Y.Base * 2^l * 2^a)) (eventLog rs) := by
  let I (mem : Memory w) := ∀ e, (mem ((p 2).val + (baseOrder Y e).val)).val < Fintype.card Y.Base * 2^a
  apply SlotEventBounds.scan _ 28 _ (SlotIncidencePass.events p reverse) I _ _
    (SlotIncidencePass.native p reverse) _ m rs bounded run
  intro j hj mem hmem
  obtain ⟨rd,wr⟩ := SlotIncidencePass.row_footprint p reverse Y mem hd hl ht hs fit hmem j hj
  refine ⟨rd, wr, fun e ↦ ?_⟩
  have he := (baseOrder Y e).isLt
  rw [after_outside mem wr (fun hx ↦ by omega)]
  exact hmem e

/-- The three chronological native scans read within the five mate columns
and write only the inverse-base and two actual columns. The bounds include
the data-dependent displacement reads of the reverse scan. -/
theorem mate_footprint (Y : State a l) (s : Shape) (h : Heads) (m : Memory w) (r : MateReports w)
    (base : BaseForward Y (targetsHead s h) (shiftsHead s h) m)
    (hB : Fintype.card Y.Base * 2^a = baseArcs s)
    (hA : Fintype.card Y.Base * 2^l * 2^a = actualCount s)
    (hd : s.newDegree = 2^a) (hl : s.lanes = 2^l) (hdw : 2^a < 2^w) (hlw : 2^l < 2^w)
    (hfit : finish s h < 2^w) (native : r.Native s h m) :
    Reads (fun x ↦ targetsHead s h ≤ x ∧ x < widthHead s h) (eventLog r.all) ∧
    Writes (fun x ↦ inverseBaseHead s h ≤ x ∧ x < widthHead s h) (eventLog r.all) := by
  let p := inverseBank s h w
  let q := actualBank s h false w
  let t := actualBank s h true w
  have h₀ : targetsHead s h + baseArcs s = shiftsHead s h := rfl
  have h₁ : shiftsHead s h + baseArcs s = inverseBaseHead s h := rfl
  have h₂ : inverseBaseHead s h + baseArcs s = outHead s h := rfl
  have h₃ : outHead s h + actualCount s = inHead s h := rfl
  have h₄ : inHead s h + actualCount s = widthHead s h := rfl
  have h₅ : widthHead s h + actualCount s = finish s h := rfl
  have p0 : (p 0).val = targetsHead s h := Nat.mod_eq_of_lt (by omega : targetsHead s h < 2^w)
  have p1 : (p 1).val = inverseBaseHead s h := Nat.mod_eq_of_lt (by omega : inverseBaseHead s h < 2^w)
  have q0 : (q 0).val = 2^a := (Nat.mod_eq_of_lt (hd ▸ hdw)).trans hd
  have q1 : (q 1).val = 2^l := (Nat.mod_eq_of_lt (hl ▸ hlw)).trans hl
  have q2 : (q 2).val = targetsHead s h := p0
  have q3 : (q 3).val = shiftsHead s h := Nat.mod_eq_of_lt (by omega : shiftsHead s h < 2^w)
  have q4 : (q 4).val = outHead s h := Nat.mod_eq_of_lt (by omega : outHead s h < 2^w)
  have t2 : (t 2).val = inverseBaseHead s h := p1
  have t3 : (t 3).val = shiftsHead s h := q3
  have t4 : (t 4).val = inHead s h := Nat.mod_eq_of_lt (by omega : inHead s h < 2^w)
  let m₁ := after m (eventLog r.baseIn)
  let m₂ := after m₁ (eventLog r.actualOut)
  obtain ⟨rb,ro,ri⟩ := native
  rw [← hB] at rb
  rw [← hA] at ro ri
  have reg : SlotScatter.Regions p (Fintype.card Y.Base*2^a) (Fintype.card Y.Base*2^a) :=
    ⟨by rw [p0,hB]; omega, by rw [p1,hB]; omega, Or.inl (by rw [p0,p1,hB]; omega)⟩
  obtain ⟨readB,writeB⟩ := baseInverse Y reg (p0 ▸ base) rb
  obtain ⟨bs,hbr,_,forward,inv,_⟩ := scatterBaseIn Y m p (shiftsHead s h) reg (p0 ▸ base)
    (Or.inl (by rw [p1,hB]; omega))
  obtain rfl := Option.some.inj (rb.symm.trans hbr)
  have outBound (e) : (m₁ ((q 2).val + (baseOrder Y e).val)).val < Fintype.card Y.Base * 2^a := by
    change (after m (eventLog r.baseIn) ((p 0).val + (baseOrder Y e).val)).val < _
    rw [forward.mate e]
    exact (Nat.mod_le ..).trans_lt (baseOrder Y (Y.slots.base.target e)).isLt
  obtain ⟨readO,writeO⟩ := actual_scan_footprint q false Y m₁ r.actualOut q0 q1
    (by rw [q2,q4,hB]; omega) (by rw [q3,q4,hB]; omega) (by rw [q4,hA]; omega) outBound ro
  have inBound (e) : (m₂ ((t 2).val + (baseOrder Y e).val)).val < Fintype.card Y.Base * 2^a := by
    have he : (baseOrder Y e).val < baseArcs s := (baseOrder Y e).isLt.trans_le hB.le
    have away : ¬ InColumn (q 4).val (Fintype.card Y.Base * 2^l * 2^a) ((p 1).val + (baseOrder Y e).val) := by
      rw [InColumn,q4,p1]; omega
    change (after m₁ (eventLog r.actualOut) ((p 1).val + (baseOrder Y e).val)).val < _
    rw [after_outside m₁ writeO away, show m₁ ((p 1).val + (baseOrder Y e).val) = _ from inv e]
    exact (Nat.mod_le ..).trans_lt (baseOrder Y (Y.slots.base.target.symm e)).isLt
  obtain ⟨readI,writeI⟩ := actual_scan_footprint t true Y m₂ r.actualIn q0 q1
    (by rw [t2,t4,hB]; omega) (by rw [t3,t4,hB]; omega) (by rw [t4,hA]; omega) inBound ri
  constructor <;> intro addr val member <;>
    simp only [MateReports.all,eventLog,List.flatMap_append,List.mem_append] at member
  · rcases member with (hb | ho) | hi
    · have hr := readB addr val hb
      rw [InColumn,p0,hB] at hr
      omega
    · have hr := readO addr val ho
      simp only [InColumn,q2,q3,hB] at hr
      omega
    · have hr := readI addr val hi
      simp only [InColumn,t2,t3,hB] at hr
      omega
  · rcases member with (hb | ho) | hi
    · have hw := writeB addr val hb
      rw [InColumn,p1,hB] at hw
      omega
    · have hw := writeO addr val ho
      rw [InColumn,q4,hA] at hw
      omega
    · have hw := writeI addr val hi
      rw [InColumn,t4,hA] at hw
      omega

end CompressorRecords.ShrinkSlots

end VPVNP
end Computability
end OAI
