import OAI.Hierarchy.ProtocolRAMPurchaseTape
import OAI.Hierarchy.ProtocolRAMPurchaseMarks
import OAI.Hierarchy.ProtocolRAMPurchaseOwnersCheap

namespace OAI
/-! # Live sign and path inputs for the native purchase interpreter

The inverse-socket and path passes leave the signed stock registers untouched.
The final marking scan consumes exactly those stock words, preserves the tile
rows and the gate ROM, and includes the extra permanently unavailable tile.
-/

namespace Hierarchy.ProtocolRAM.PurchaseTape
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing Classical
noncomputable section
variable {w n m groups D h k : ℕ} {G : Type*}

structure Signed (k : ℕ) where
  stock : Fin (2*k) → Bank
  threshold : Bank
  marks : Bank

structure SignedFits (s : Plan D) (b : Signed k) (w n : ℕ) : Prop where
  directions : 2*k<2^w
  table : b.threshold.Fits w b.marks.base
  stock : ∀ j, (b.stock j).Fits w b.marks.base
  capacity : n+1≤b.marks.size
  marks : b.marks.Fits w s.columns.owner.base
  static : s.gates.base+6*s.gates.stride≤b.marks.base ∨ b.marks.base+b.marks.size ≤ s.gates.base

abbrev signedPrefix (s : Plan D) (b : Signed k) (j : Fin (2*k)) (w n groups m h : ℕ) :=
  (prefixCode s w n groups m h).seq
    (scan w b.marks.base (n+1) (PurchaseMarks.markExpr n b.threshold b.stock j))

abbrev signedOut (s : Plan D) (b : Signed k) (j : Fin (2*k)) (p : Tiles (Fin n) G m)
    (enc : G ↪ Fin groups) (h : ℕ) (mem : Memory w) :=
  image b.marks.base (n+1) (PurchaseMarks.markExpr n b.threshold b.stock j) (prefixOut s p enc h mem)

abbrev signedTicks (s : Plan D) (n groups m h k : ℕ) :=
  prefixTicks s n groups m h + (4+(n+1)*(2*(10+15*(2*k))+4))

theorem mark_fits (s : Plan D) (b : Signed k) (j : Fin (2*k)) (hw : SignedFits s b w n) :
    (PurchaseMarks.markExpr n b.threshold b.stock j).Fits w b.marks.base := by
  have tags (js : List (Fin (2*k))) : (PurchaseMarks.tagExpr b.threshold b.stock js).Fits w b.marks.base := by
    induction js with
    | nil => trivial
    | cons j js ih => exact ⟨⟨hw.table,hw.stock j,trivial⟩,trivial,trivial,ih⟩
  exact ⟨trivial,trivial,⟨tags _,trivial,trivial,trivial⟩,trivial⟩

attribute [local irreducible] Procedure.Exec

/-- The mark and the path rows refer to the same live permutation and the price
quoted before any of these native scans began. -/
theorem signed_columns_run (s : Plan D) (b : Signed k) (phase : PhasePrice) (T : ℝ) (kind : ℕ)
    (j : Fin (2*k)) (p : Tiles (Fin n) G m) (enc : G ↪ Fin groups)
    (sampler : Fin m → Fin D → Option (Fin m)) (h : ℕ) (mem : Memory w)
    (size : Fits s w n groups m h) (bounds : SignedFits s b w n) (input : Loaded s p enc sampler h mem)
    (table : PurchaseMarks.Table phase T k kind b.threshold mem) :
    let rows := PurchaseColumns.rowTile (h:=h) (ProtocolRAMPurchaseOwners.successor p enc sampler)
    let out := signedOut s b j p enc h mem
    let marked := (PurchaseMarks.stratum (n:=n) phase T kind b.threshold b.stock mem j).map Fin.castSuccEmb
    (signedPrefix s b j w n groups m h).Exec mem out (signedTicks s n groups m h k) ∧
    ProtocolRAMPurchaseGateColumns.TileRows s.source rows out ∧
    GateColumns.Mounted s.gates (ProtocolRAMPurchaseGateColumns.spec (R:=count n D h) (H:=h+1) (n+1) s.work s.first) out ∧
    Native.Resident b.marks out (fun i : Fin (n+1) => (decide (i∈marked)).toNat) := by
  let core := prefixOut s p enc h mem
  let out := signedOut s b j p enc h mem
  obtain ⟨run,rows,rom,early⟩ := columns_run s p enc sampler h mem size input
  have read (bank : Bank) (before : bank.Fits w b.marks.base) (r : Word w) : bank.read core r=bank.read mem r :=
    early _ (by have rr := Nat.mod_lt r.val before.1; have lo := before.2.2; have endMark := bounds.marks.2.2
                change bank.base+r.val%bank.size<s.columns.owner.base; omega)
  have tbl : PurchaseMarks.Table phase T k kind b.threshold core := fun r => (read _ bounds.table r).trans (table r)
  have fixed (r : Word w) : PurchaseMarks.tested phase T kind b.threshold b.stock core r =
      PurchaseMarks.tested phase T kind b.threshold b.stock mem r := by
    funext i; simp only [PurchaseMarks.tested,read (b.stock i) (bounds.stock i)]
  have same : PurchaseMarks.stratum (n:=n) phase T kind b.threshold b.stock core j =
      PurchaseMarks.stratum phase T kind b.threshold b.stock mem j := by simp only [PurchaseMarks.stratum,fixed]
  have endMark := bounds.marks.2.2
  have cap := bounds.capacity
  have ownerRoom := size.owners.owner.2.2
  have finalRoom := size.owners.room
  obtain ⟨mark,stored⟩ := PurchaseMarks.emit phase T kind b.marks.base b.threshold b.stock core j
    size.wide bounds.directions tbl (mark_fits s b j bounds) (by omega)
  have frame (a : ℕ) (away : a<b.marks.base ∨ b.marks.base+(n+1)≤a) : out a=core a :=
    ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ away
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [signedPrefix,signedOut,signedTicks,PurchaseMarks.markExpr_work] using run.then mark
  · intro i t
    exact (frame _ (.inr (by have src := size.sourceAfter; omega))).trans (rows i t)
  · apply GateColumns.mounted_of_frame _ _ rom
    intro a low high
    exact frame a (by rcases bounds.static with low' | high' <;> omega)
  · apply Native.Resident.of_cells _ _ _ cap (by omega)
    intro i
    simpa only [same] using stored i

theorem cheap_prefix (s : Plan D) (w n groups m h : ℕ) : CheapCode (prefixCode s w n groups m h) :=
  cheap_seq (ProtocolRAMPurchaseOwners.cheap w n groups m s.ownerScratch s.columns)
    (program_cheap w (PurchaseColumns.passes s.directory s.source.base n h (edge s)))

theorem cheap (s : Plan D) (w n groups m h : ℕ) : CheapCode (code s w n groups m h) :=
  cheap_seq (cheap_prefix s w n groups m h) (program_cheap w (GateColumns.passes s.source s.gates s.work
    (ProtocolRAMPurchaseGateColumns.gates (count n D h) (h+1)) s.packed))

theorem cheap_signed (s : Plan D) (b : Signed k) (j : Fin (2*k)) (w n groups m h : ℕ) :
    CheapCode (signedPrefix s b j w n groups m h) := cheap_seq (cheap_prefix s w n groups m h)
      (scan_cheap w b.marks.base (n+1) (PurchaseMarks.markExpr n b.threshold b.stock j))

end
end Hierarchy.ProtocolRAM.PurchaseTape

end OAI
