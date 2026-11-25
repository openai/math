import OAI.Computability.BorderVNP.RoutingISATableIntervalImage
import OAI.Computability.BorderVNP.TransmissionLegTable
import OAI.Computability.BorderVNP.TransmissionSafe

/-! # The scheduled transmission ranges read from the native table image -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Transmission

open VPVNP.BurstRAM

/-- The stored pair widths, indexed by team numbers in the physical frame. -/
def tableWidth (l : TableLayout) (row : ℕ → TableRow) {R : ℕ} (teams : R = l.teams)
    (u v : Fin R) : ℕ :=
  l.widthMatrix row (u.cast teams) (v.cast teams)

/-- The actual row popped at the two word cursors, before any payload writes. -/
def tableRange {w : ℕ} (l : TableLayout) (m : Memory w) (i : ℕ) : Range w :=
  rangeAt m (cursorAt (Fin.ofNat _ l.records) 7 i) (cursorAt (Fin.ofNat _ l.ordinals) 1 i)

/-- The checked offset table, physical frame and the two-direction capacity of
each block supply the complete native transmission schedule. -/
theorem Schedule.of_table {l : TableLayout} {row : ℕ → TableRow} {w : ℕ}
    {before : ℕ → ℕ} {m : Memory w} (image : l.Image row before (readings m)) (al : l.Allocated w)
    (pub : Arg → Word w) (hf : (pub 0).val = l.frame) (loaded : l.frameFields before)
    (f : BroadcastFrame) (im : f.At (readings pub) (readings m)) (fit : f.Fits w (pub 0).val)
    (teams : f.teams = l.teams)
    (capacity : ∀ u v, f.header + Routing.legLoad al.teamCount (l.widthMatrix row) u v +
      Routing.legLoad al.teamCount (l.widthMatrix row) v u ≤ f.capacity) :
    Schedule f (tableWidth l row teams) pub m := by
  obtain ⟨tripleFit,pairFit⟩ := image.directoryFits al (readings pub) hf loaded
  rcases f with ⟨team,R,processors,literal,link,header,dst⟩
  change R = l.teams at teams
  subst R
  exact ⟨im,fit,image.addressTables al (readings pub) hf loaded,tripleFit,pairFit,
    fun v _ => capacity ⟨team,fit.own⟩ v⟩

private theorem addFieldVal {w : ℕ} (base : Word w) (k : ℕ) (h : base.val+k < 2^w) :
    (base + Fin.ofNat _ k).val = base.val+k := by
  rw [Fin.val_add, Fin.val_ofNat, Nat.mod_eq_of_lt (by omega : k < 2^w), Nat.mod_eq_of_lt h]

private theorem cursorVal {w : ℕ} (base stride i : ℕ) (h : base + i*stride < 2^w) :
    (cursorAt (Fin.ofNat _ base : Word w) (Fin.ofNat _ stride) i).val = base + i*stride := by
  induction i with
  | zero =>
    simp only [cursorAt, zero_nsmul, add_zero, Nat.zero_mul] at h ⊢
    exact Nat.mod_eq_of_lt (by omega)
  | succ i ih =>
    rw [Nat.succ_mul] at h ⊢
    have prior := ih (by omega)
    rw [cursorAt, succ_nsmul, ← add_assoc]
    change (cursorAt (Fin.ofNat _ base : Word w) (Fin.ofNat _ stride) i + Fin.ofNat _ stride).val = _
    rw [addFieldVal _ _ (by omega), prior, Nat.add_assoc]

/-- After scheduling, the actual two-cursor load returns the kind, original
endpoint numbers, recorded bit length, and the newly computed ordinal for this row. -/
theorem tableRange_fields {l : TableLayout} {row : ℕ → TableRow} {w : ℕ}
    {before : ℕ → ℕ} {m : Memory w} (image : l.Image row before (readings m)) (al : l.Allocated w)
    (initial : l.recordsMatch row before) {i : ℕ} (hi : i < l.count) :
    let r := tableRange l m i
    r.kind.val = (row i).kind ∧ r.teamA.val = (row i).first ∧ r.teamB.val = (row i).second ∧
      r.width.val = (row i).width ∧ r.ordinal.val = l.ordinal row i := by
  let base : Word w := cursorAt (Fin.ofNat _ l.records) 7 i
  let ord : Word w := cursorAt (Fin.ofNat _ l.ordinals) 1 i
  have hf : 7*i+l.records+3 < 2^w := al.address (l.contains_record hi (by decide : 3 < 7))
  have hb : base.val = 7*i+l.records := by
    have hfit : l.records + i*7 < 2^w := by omega
    calc
      base.val = l.records+i*7 := cursorVal l.records 7 i hfit
      _ = 7*i+l.records := by omega
  have ho : ord.val = l.ordinals+i := by
    have hfit : l.ordinals + i < 2^w := al.address (l.contains_offset (a := .ordinals) hi)
    calc
      ord.val = l.ordinals+i*1 := cursorVal l.ordinals 1 i (by simpa only [Nat.mul_one] using hfit)
      _ = l.ordinals+i := by rw [Nat.mul_one]
  have addr (k : ℕ) (hk : k ≤ 3) : (base + Fin.ofNat _ k).val = 7*i+l.records+k :=
    (addFieldVal base k (by omega)).trans (congrArg (· + k) hb)
  have record (k : ℕ) (hk : k ≤ 3) : readings m (7*i+l.records+k) = before (7*i+l.records+k) := by
    have h := l.contains_record hi (by omega : k < 7)
    exact image.outside _ (al.separate .records .widths _ (by decide) h)
      (al.separate .records .ordinals _ (by decide) h) (al.separate .records .offsets _ (by decide) h)
      (al.separate .records .used _ (by decide) h)
  change readings m base.val = _ ∧ readings m (base+Fin.ofNat _ 1).val = _ ∧ readings m (base+Fin.ofNat _ 2).val = _ ∧
    readings m (base+Fin.ofNat _ 3).val = _ ∧ readings m ord.val = _
  rw [addr 1 (by decide), addr 2 (by decide), addr 3 (by decide), ho,
    record 1 (by decide), record 2 (by decide), record 3 (by decide), image.ordinals i hi, hb]
  have keep := record 0 (by decide)
  simp only [Nat.add_zero] at keep
  exact ⟨keep.trans (initial i hi).1,(initial i hi).2.1,(initial i hi).2.2.1,(initial i hi).2.2.2,rfl⟩

/-- The kind actually loaded by the evaluator is one of the two legal word tags. -/
theorem tableRange_valid_kind {l : TableLayout} {row : ℕ → TableRow} {w : ℕ}
    {before : ℕ → ℕ} {m : Memory w} (image : l.Image row before (readings m)) (al : l.Allocated w)
    (rowsFit : l.RowsFit w row) (initial : l.recordsMatch row before) {i : ℕ} (hi : i < l.count) :
    (tableRange l m i).kind = 0 ∨ (tableRange l m i).kind = 1 := by
  have kind := (tableRange_fields image al initial hi).1
  have bound := (rowsFit.labels i hi).1
  have oneFits : 1 < 2^w := by have := al.teamCount; have := al.teamsFit; omega
  rcases Nat.lt_or_ge (row i).kind 1 with h | h
  · exact Or.inl (Fin.ext (kind.trans (by omega : (row i).kind = 0)))
  · apply Or.inr
    apply Fin.ext
    rw [kind, Fin.val_one', Nat.mod_eq_of_lt oneFits]
    omega

/-- Each concrete two-cursor range in the physical scheduler output satisfies the
pair demand and word-space bounds used by every bit of the transmission scan. -/
theorem ScheduledRange.of_table {l : TableLayout} {row : ℕ → TableRow} {w : ℕ}
    {before : ℕ → ℕ} {m : Memory w} (image : l.Image row before (readings m)) (al : l.Allocated w)
    (rowsFit : l.RowsFit w row) (initial : l.recordsMatch row before)
    (f : BroadcastFrame) (teams : f.teams = l.teams) {i : ℕ} (hi : i < l.count) :
    ScheduledRange f (tableWidth l row teams) (tableRange l m i) := by
  rcases f with ⟨team,R,processors,literal,link,header,dst⟩
  change R = l.teams at teams
  subst R
  let r := tableRange l m i
  obtain ⟨_,ha,hb,hw,ho⟩ := tableRange_fields image al initial hi
  have first : r.teamA.val < l.teams := ha ▸ (rowsFit.labels i hi).2.1
  have second : r.teamB.val < l.teams := hb ▸ (rowsFit.labels i hi).2.2
  let u : Fin l.teams := ⟨r.teamA.val,first⟩
  let v : Fin l.teams := ⟨r.teamB.val,second⟩
  have ne (h : r.teamA ≠ r.teamB) : (row i).first ≠ (row i).second :=
    fun e => h (Fin.ext (ha.trans (e.trans hb.symm)))
  have bound (h : r.teamA ≠ r.teamB) : r.ordinal.val + r.width.val ≤
      l.pairWidth row l.count (l.pairKey (row i).first (row i).second) := by
    rw [show r.ordinal.val = _ from ho, show r.width.val = _ from hw]
    exact l.ordinal_add_width_le row hi (ne h)
  refine ⟨first,second,?_,fun h => (bound h).trans
    ((l.pairWidth_le_sum row le_rfl _).trans rowsFit.widths.le)⟩
  intro h
  have huv : u ≠ v := fun e => h (Fin.ext (show u.val = v.val from congrArg Fin.val e))
  change _ ≤ Routing.demand (l.widthMatrix row) u v
  rw [Routing.demand, ite_eq_right huv]
  have mono : Monotone (@Fin.val l.teams) := fun _ _ e => e
  simpa only [TableLayout.widthMatrix, TableLayout.pairKey, mono.map_min, mono.map_max,
    show u.val = (row i).first from ha, show v.val = (row i).second from hb] using bound h

end RoutingISA.Transmission

end BorderVNP
end Computability
end OAI
