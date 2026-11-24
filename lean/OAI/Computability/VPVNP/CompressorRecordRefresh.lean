import OAI.Computability.VPVNP.BitSlotXor
import OAI.Computability.VPVNP.CompressorRecordRefreshRAM
import OAI.Computability.VPVNP.CompressorRecordSlices
import OAI.Computability.VPVNP.DegreeRefreshActualStep

/-!
# Directly indexed records of the degree-restoring step

A source bundle specifies the old base arc and the remaining lane. Its numbered segments
are in source-port order. At the destination the incoming slot and translated port index
the same segment. We relate the emitted offset and width records to the bit indices of the
actual refresh kernel, including local diagonal checks and the two copies of the off-diagonal
demand. We also give the endpoint and width tables for the external, expander and dummy slots.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh

open Compression Compression.Refresh Compression.DegreeRefresh

variable {V H L : Type} {D dH d₀ : ℕ} [AddCommGroup H] [AddCommGroup L]
variable (G : LiftedSlots V D (H × L)) (port : H ≃ Fin D) (w : (V × Fin D) × (H × L) → ℕ)

/-- Both endpoint identifiers and one interval in the external word. An endpoint consists
of its block, its slot and its old port. Its first two components also locate the external
slot at which this interval is read. -/
structure SegmentRecord (B : Type*) (D : ℕ) where
  /-- The outgoing segment identified by its source bundle and numbered port. -/
  outgoing : Arc B D
  /-- The same segment's incoming bundle and translated port at the destination. -/
  incoming : Arc B D
  /-- Starting bit offset of the segment in the concatenation ordered by source port. -/
  offset : ℕ
  /-- Number of bits contributed by this segment to its external bundle. -/
  width : ℕ

/-- Generate the record of an old actual arc in source-bundle coordinates. -/
def outgoingRecord (a : Arc (V × L) D) : SegmentRecord (V × L) D :=
  ⟨a, (bundleTarget G a.1, bundlePort G port a.1 a.2),
    (numberedField (Equiv.refl _) (bundleWidths port w a.1) a.2).start, groupedWidths port w a⟩

/-- Destination slot lookup inverts the remaining-lane translation and then the port
translation. In particular, it retains the prefix total of the *source* ordering. -/
def incomingRecord (q : Arc (V × L) D) : SegmentRecord (V × L) D :=
  let b := (bundleTarget G).symm q.1
  outgoingRecord G port w (b, (bundlePort G port b).symm q.2)

theorem incomingRecord_matching (q : Arc (V × L) D) :
    incomingRecord G port w q = outgoingRecord G port w ((oldPortMatching G port).symm q) := by
  rcases q with ⟨b,j⟩
  rw [oldPortMatching_symm_apply]
  rfl

theorem incomingRecord_roundtrip (a : Arc (V × L) D) :
    incomingRecord G port w (oldPortMatching G port a) = outgoingRecord G port w a := by
  rw [incomingRecord_matching, Equiv.symm_apply_apply]

/-- Every actual incoming half-slot receives exactly one of the emitted rows. -/
theorem incoming_unique (q : Arc (V × L) D) :
    ∃! a : Arc (V × L) D, (outgoingRecord G port w a).incoming = q :=
  ⟨(oldPortMatching G port).symm q, (oldPortMatching G port).apply_symm_apply q,
    fun _ ha => (oldPortMatching G port).eq_symm_apply.mpr ha⟩

/-- The emitted old endpoint slots are those of the original lifted network. -/
theorem old_slot_endpoints (a : Arc (V × L) D) :
    G.actualTarget ((bundleCoordinates port).symm (outgoingRecord G port w a).outgoing) =
      (bundleCoordinates port).symm (outgoingRecord G port w a).incoming :=
  (bundleCoordinates port).eq_symm_apply.mpr (actualTarget_bundleCoordinates G port a.1 a.2)

/-- The prefix scan of the widths writes the exact record, also when its interval is empty. -/
theorem segment_in_scan (a : Arc (V × L) D) :
    let r := outgoingRecord G port w a
    (⟨a.2.val, r.offset, r.width⟩ : Field) ∈ fieldsFrom 0 0 (List.ofFn (bundleWidths port w a.1)) :=
  orderedField_mem (Equiv.refl _) (bundleWidths port w a.1) a.2

theorem segment_fits (a : Arc (V × L) D) :
    let r := outgoingRecord G port w a
    r.offset + r.width ≤ ∑ k, bundleWidths port w a.1 k := by
  simpa [List.sum_ofFn] using (fieldsFrom_bounds (segment_in_scan G port w a)).2.2.2

/-- For any chosen external payload the record's bit addresses recover the actual outgoing
and incoming segment arguments, as read by the local kernel. -/
theorem port_bit_reads (p : (V × L) × Fin D) (j : Fin D) (z : External (groupedWidths port w)) :
    let t := oldPortMatching G port
    let widths := groupedWidths port w
    let lists := incidentPortSegments t (bundleTarget G) (oldPortMatching_bundle G port) widths p
      (z p) (z ((bundleTarget G).symm p))
    (∀ i : Fin (widths (p,j)), ∃ k : Fin (∑ l, widths (p,l)),
      k.val = (outgoingRecord G port w (p,j)).offset + i.val ∧ lists.1 j i = z p k) ∧
    (∀ i : Fin (widths (t.symm (p,j))), ∃ k : Fin (∑ l, widths ((t.symm (p,j)).1,l)),
      k.val = (incomingRecord G port w (p,j)).offset + i.val ∧ lists.2 j i = z (t.symm (p,j)).1 k) := by
  dsimp only
  rw [incidentPortSegments_external, incomingRecord_matching]
  constructor
  · intro i
    exact ⟨_, segment_offset _ p j i, rfl⟩
  · intro i
    let a := (oldPortMatching G port).symm (p,j)
    exact ⟨_, segment_offset _ a.1 a.2 i, rfl⟩

/-- The same interval addresses work on arbitrary incident half-wires. The incoming and
outgoing external slots are distinct, so the two independently chosen words extend to a
single test assignment without imposing any extra equality. -/
theorem local_bit_reads (p : (V × L) × Fin D) (j : Fin D)
    (outWord : Word (∑ l, groupedWidths port w (p,l)))
    (inWord : Word (∑ l, groupedWidths port w ((bundleTarget G).symm p,l))) :
    let t := oldPortMatching G port
    let widths := groupedWidths port w
    let lists := incidentPortSegments t (bundleTarget G) (oldPortMatching_bundle G port) widths p outWord inWord
    (∀ i : Fin (widths (p,j)), ∃ k : Fin (∑ l, widths (p,l)),
      k.val = (outgoingRecord G port w (p,j)).offset + i.val ∧ lists.1 j i = outWord k) ∧
    (∀ i : Fin (widths (t.symm (p,j))), ∃ k : Fin (∑ l, widths ((bundleTarget G).symm p,l)),
      k.val = (incomingRecord G port w (p,j)).offset + i.val ∧ lists.2 j i = inWord k) := by
  classical
  dsimp only
  let q := (bundleTarget G).symm p
  have hne : p ≠ q := fun he => G.base.ends_ne (p.1.1,p.2)
    (congrArg (fun z : (V × L) × Fin D => z.1.1) ((bundleTarget G).eq_symm_apply.mp he))
  let z : External (groupedWidths port w) := Function.update
    (Function.update (fun _ _ => false) p outWord) q inWord
  have ho : z p = outWord := (Function.update_of_ne hne _ _).trans (Function.update_self ..)
  have hi : z ((bundleTarget G).symm p) = inWord := Function.update_self ..
  have reads := port_bit_reads G port w p j z
  dsimp only at reads
  simp only [ho, hi] at reads
  refine ⟨reads.1, fun i => ?_⟩
  obtain ⟨k,hk,hval⟩ := reads.2 i
  have transport (b : (V × L) × Fin D) (hb : b = q) (r : Fin (∑ l, groupedWidths port w (b,l))) :
      ∃ r' : Fin (∑ l, groupedWidths port w (q,l)), r'.val = r.val ∧ z b r = inWord r' := by
    subst b
    exact ⟨r, rfl, congrFun hi r⟩
  obtain ⟨k',he,hz⟩ := transport _ (congrArg Prod.fst (oldPortMatching_symm_apply G port p j)) k
  exact ⟨k', he.trans hk, hval.trans hz⟩

/-- Off-diagonal motif demand references the old half-slot at `tieSource` and its external
segment at `tieTarget`. The flag in `Tie` selects the outgoing or incoming records. -/
def demandRecord (s : V × L) (e : Tie D) : SegmentRecord (V × L) D :=
  let q := ((s, tieTarget e), tieSource e)
  if e.1 then outgoingRecord G port w q else incomingRecord G port w q

theorem demandRecord_width (s : V × L) (e : Tie D) :
    (demandRecord G port w s e).width = internalWidth (oldPortMatching G port) (groupedWidths port w) s e := by
  unfold demandRecord internalWidth
  split_ifs
  · rfl
  · rw [incomingRecord_matching]; rfl

variable (P : SlotGraph (Fin D) dH) (hD : 1 < D) (hd : dH + 1 ≤ d₀)

/-- Both numbered endpoints of one refreshed arc. Widths may vary across lanes and terms. -/
structure NewSlot (V L : Type*) (D d₀ : ℕ) where
  /-- Source site and outgoing slot number of a refreshed actual arc. -/
  src : ActualArc V L D d₀
  /-- Destination site and incoming slot number of the same refreshed arc. -/
  dst : ActualArc V L D d₀
  /-- Number of bits carried by this refreshed external, expander, or padding arc. -/
  width : ℕ

/-- Append the sole external slot, the expander slots in expander order and the dummy slots
in padding order. The same expander edge table supplies the incoming slot number. -/
def slotRecord (internal : (V × L) → Fin D × Fin dH → ℕ) (p : (V × L) × Fin D) :
    RefreshSlot dH d₀ → NewSlot V L D d₀
  | .inl k => ⟨(promotedSites p, refreshSlots hd (.inl k)),
      (promotedSites (bundleTarget G p), refreshSlots hd (.inl k)), ∑ j, bundleWidths port w p j⟩
  | .inr (.inl k) => ⟨(promotedSites p, refreshSlots hd (.inr (.inl k))),
      (promotedSites (p.1,(P.target (p.2,k)).1), refreshSlots hd (.inr (.inl (P.target (p.2,k)).2))),
      internal p.1 (p.2,k)⟩
  | .inr (.inr k) => ⟨(promotedSites p, refreshSlots hd (.inr (.inr k))),
      (promotedSites (p.1,finRotate D p.2), refreshSlots hd (.inr (.inr k))), 0⟩

omit [AddCommGroup H] in
theorem slotRecord_spec (internal : (V × L) → Fin D × Fin dH → ℕ) (p : (V × L) × Fin D)
    (c : RefreshSlot dH d₀) :
    let r := slotRecord G port w P hd internal p c
    r.src = (promotedSites p, refreshSlots hd c) ∧
      (degreeRefresh G P hD hd).actualGraph.target r.src = r.dst ∧
      actualWidths hd port w internal ((r.src.1.1,r.src.2),r.src.1.2) = r.width := by
  rcases p with ⟨⟨v,l⟩,i⟩
  rcases c with k | k | k
  · cases Subsingleton.elim k 0
    refine ⟨rfl, degreeRefresh_external G P hD hd (v,i) l, ?_⟩
    simp [slotRecord, actualWidths, refreshedCoordinates, promotedSites, newWidths]
  · refine ⟨rfl, degreeRefresh_internal G P hD hd v i l k, ?_⟩
    simp [slotRecord, actualWidths, refreshedCoordinates, promotedSites, newWidths]
  · refine ⟨rfl, degreeRefresh_padding G P hD hd v i l k, ?_⟩
    simp [slotRecord, actualWidths, refreshedCoordinates, promotedSites, newWidths]

/-- A full output slot table at a physical port, generated in slot-number order. -/
def slotTable (internal : (V × L) → Fin D × Fin dH → ℕ) (p : (V × L) × Fin D) :=
  List.ofFn fun k : Fin d₀ => slotRecord G port w P hd internal p ((refreshSlots hd).symm k)

omit [AddCommGroup H] in
@[simp] theorem slotTable_length (internal : (V × L) → Fin D × Fin dH → ℕ) (p : (V × L) × Fin D) :
    (slotTable G port w P hd internal p).length = d₀ := by simp [slotTable]

/-- The number of segment visits and slot records is linear in the number of positions
for the fixed degrees of this substep. -/
theorem visit_counts (B : Type*) [Fintype B] (D d₀ : ℕ) :
    Fintype.card (Arc B D) = Fintype.card (B × Fin D) * D ∧
    Fintype.card ((B × Fin D) × Fin d₀) = Fintype.card (B × Fin D) * d₀ := by
  simp [Refresh.Arc, Fintype.card_prod]

section Numbered

open BurstRAM BurstRAM.PrivateRAM

/-- The source-major index is invertible by quotient and remainder with divisor `D`. -/
def numbered {B : Type*} {n D : ℕ} (order : B × Fin D ≃ Fin n) : Refresh.Arc B D ≃ Fin (n * D) :=
  (order.prodCongr (Equiv.refl (Fin D))).trans finProdFinEquiv

theorem numbered_val {B : Type*} {n D : ℕ} (order : B × Fin D ≃ Fin n) (b : B × Fin D) (j : Fin D) :
    (numbered order (b,j)).val = (order b).val * D + j.val := by
  change j.val + D * (order b).val = _
  rw [Nat.mul_comm, Nat.add_comm]

variable {a n bits : ℕ} (X : LiftedSlots V (2 ^ a) (BitWord a × L))
  (order : (V × L) × Fin (2 ^ a) ≃ Fin n)

/-- The numerical destination of a segment uses the bundle number, degree and translated port. -/
theorem translated_index (degree target shift : BurstRAM.Word bits)
    (b : (V × L) × Fin (2 ^ a)) (j : Fin (2 ^ a)) (i : BurstRAM.Word bits)
    (hi : i.val = (numbered order (b,j)).val) (hd : degree.val = 2 ^ a)
    (ht : target.val = (order (bundleTarget X b)).val)
    (hs : shift.val =
      (bitWordFinEquiv a (X.displacement (b.1.1,b.2)).1).val) (hfit : n * 2 ^ a ≤ 2 ^ bits) :
    (target * degree + BinaryOp.bitXor.eval (BinaryOp.mod.eval i degree) shift).val =
      (numbered order (oldPortMatching X (bitWordFinEquiv a) (b,j))).val := by
  have hport : i.val % degree.val = j.val := by
    rw [hi, hd, numbered_val, Nat.mul_add_mod_of_lt j.isLt]
  have hport' : (BinaryOp.mod.eval i degree).val = j.val := by
    change (i.val % degree.val) % _ = _
    rw [hport, Nat.mod_eq_of_lt (j.isLt.trans (hd ▸ degree.isLt))]
  have hxor : (bundlePort X (bitWordFinEquiv a) b j).val =
      j.val ^^^ (bitWordFinEquiv a (X.displacement (b.1.1,b.2)).1).val := by
    rw [bundlePort_apply, bitWordFinEquiv_add_val, Equiv.apply_symm_apply]
  have hrow : (order (bundleTarget X b)).val * 2 ^ a + (bundlePort X (bitWordFinEquiv a) b j).val < 2 ^ bits :=
    (numbered_val order (bundleTarget X b) (bundlePort X (bitWordFinEquiv a) b j) ▸
      (numbered order (bundleTarget X b, bundlePort X (bitWordFinEquiv a) b j)).isLt).trans_le hfit
  have hb (x y : BurstRAM.Word bits) : (BinaryOp.bitXor.eval x y).val = x.val ^^^ y.val :=
    Nat.mod_eq_of_lt (Nat.xor_lt_two_pow x.isLt y.isLt)
  rw [oldPortMatching_apply, numbered_val, Fin.val_add, Fin.val_mul,
    hb, hport', hs, ht, hd, ← hxor, Nat.mod_add_mod, Nat.mod_eq_of_lt hrow]

/-- With the target and shift supplied by the old slot table, the address computed by
`visit` is the number of the actual translated incoming half-slot. -/
theorem visit_destination (p : Fin 8 → BurstRAM.Word bits) (m : Memory bits)
    (b : (V × L) × Fin (2 ^ a)) (j : Fin (2 ^ a)) (i : BurstRAM.Word bits)
    (hi : i.val = (numbered order (b,j)).val) (hd : (p 0).val = 2 ^ a)
    (ht : (m (p 2 + RefreshRAM.bundle p i).val).val = (order (bundleTarget X b)).val)
    (hs : (m (p 3 + RefreshRAM.bundle p i).val).val =
      (bitWordFinEquiv a (X.displacement (b.1.1,b.2)).1).val) (hfit : n * 2 ^ a ≤ 2 ^ bits) :
    (RefreshRAM.destination p m i).val =
      (numbered order (oldPortMatching X (bitWordFinEquiv a) (b,j))).val :=
  translated_index X order _ _ _ b j i hi hd ht hs hfit

end Numbered

end CompressorRecords.PortRefresh

end VPVNP
end Computability
end OAI
