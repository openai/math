import OAI.Computability.BorderVNP.PackedBankCellStatic
import OAI.Computability.BorderVNP.PackedBankInheritedScalarBounds
import OAI.Computability.BorderVNP.PackedInheritedTieFields
import OAI.Computability.BorderVNP.CellPacketFieldMonotone
import OAI.Computability.BorderVNP.CellReportFieldWidth

/-! # Raw and local numeric bounds for the final sorted physical cell

The ordered private box directory keeps the original gadget identifiers. Only
the field bound on local wire addresses enters the expanded generator clock.
The public rows include each retained site program, its actual relocated box
prefix, and every physical cable/argument tie.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FinalCell

open Crossing Shortening CellSparse CellAddresses InheritedBank BankBoxOrdinal DiagonalTallyCellReports
open scoped Classical
open private off from OAI.Computability.BorderVNP.PackedBankSortedCell
open private load from OAI.Computability.BorderVNP.PackedBankCellStatic

set_option maxHeartbeats 1800000
set_option maxRecDepth 22000

variable {D s n p : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
  (cell : N.Site → ℕ) (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin n)
  (portID : P ↪ Fin p) (owner : Fin s → ℕ) (state : N.Site → Site)

/-- All internally guessed cable bits and the allocated persistent site slabs. -/
noncomputable def privateBits (c : ℕ) := guessedSize N cell c + siteSize N cell c (fun v => (state v).size)

/-- The count block immediately follows all the physical external ports. -/
noncomputable def countBase (c : ℕ) := privateBits N cell state c + suppliedSize N cell c

private theorem count_addresses (b g w : ℕ) {bs : List ℕ} (h : bs ∈ countFields b g w) :
    bs.length = w ∧ ∀ x ∈ bs, x < b+g*w := by
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp h
  refine ⟨List.length_ofFn,?_⟩
  intro x hx
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hx
  have h : (i.val+1)*w ≤ g*w := Nat.mul_le_mul_right _ i.isLt
  rw [Nat.add_mul,Nat.one_mul] at h
  have hj := j.isLt
  omega

private theorem firstBox_le {c : ℕ} {v : N.Site} (hv : v ∈ sites siteID owner c)
    (reports : List (List ℕ)) : firstBox siteID owner state v ≤
    (directory owner N cell siteID edgeID portID state c reports).boxes.length := by
  rw [directory_boxes,table_length,← site_owner siteID owner hv]
  unfold firstBox base
  apply Finset.sum_le_sum
  intro i _
  split_ifs with ha hb hb
  · rfl
  · exact False.elim (hb ha.1)
  all_goals exact Nat.zero_le _

private theorem mem_sum {i : ℕ} {xs : List ℕ} (h : i ∈ xs) : i ≤ xs.sum := by
  induction xs with
  | nil => cases h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl|h
    · exact Nat.le_add_right _ _
    · exact (ih h).trans (Nat.le_add_left _ _)

private theorem factor_count (fs : List Factor) : fs.length ≤ (fs.map Factor.staticMass).sum := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    have h : 1 ≤ f.staticMass := by
      cases f with
      | truth ws rs | sign ws rs | gadget ws rs => exact Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
      | unary => exact le_refl 1
    simpa only [List.length_cons,List.map_cons,List.sum_cons,Nat.add_comm fs.length 1] using Nat.add_le_add h ih

private theorem box_sizes (D : Directory) :
    D.boxes.length ≤ Packet.storedMass D ∧ ∀ fs ∈ D.boxes, fs.length ≤ Packet.storedMass D := by
  refine ⟨Nat.le_add_right ..,fun fs hs => (factor_count fs).trans ?_⟩
  let m := fun xs : List Factor => (xs.map Factor.staticMass).sum
  have hm : m fs ∈ D.boxes.map m := List.mem_map.mpr ⟨fs,hs,rfl⟩
  exact (mem_sum hm).trans (Nat.le_add_left _ D.boxes.length)

/-- The canonical cell subtotal word needs exactly the bits of a binary
integer up to the supplied cap. This bound applies directly to the selected,
merged and physically tied cell directory. -/
theorem directory_report_width (c gadgets cap order r : ℕ) (hr : 1 ≤ r) (hc : cap ≤ order) :
    ∀ bs ∈ (directory owner N cell siteID edgeID portID state c
      (countFields (countBase N cell state c) gadgets (Nat.clog 2 (cap+1)))).reportedCounts,
      bs.length ≤ TeamScales.logWidth r order := by
  intro bs h
  rw [countField_length _ _ _ h,Packet.Emit.Finish.countWidth_eq]
  exact (Nat.size_le_size hc).trans (CellMacro.Generator.size_le_logWidth order r hr)

/-- The actual final merged packet meets both numeric restrictions of the
native compiler. The arbitrary global gadget ID bound occurs only in the
raw packet bound, which the native routine measures by its binary width. -/
theorem compiler_fields (c gadgets digits M E Z high : ℕ)
    (ho : ∀ v, owner (siteID v) = cell v) (hin : ∀ v, (state v).incoming = incoming N v)
    (hschema : ∀ v, (state v).Schema) (hpub : load N cell state c false ≤ M)
    (hexp : load N cell state c true ≤ M) (hg : gadgets ≤ M+1) (hd : digits ≤ M+1)
    (hz : 3*M+Z ≤ 4*(M+E+1)^3)
    (hscalar : ∀ v ∈ sites siteID owner c, (state v).ScalarBound Z)
    (hfactors : ∀ v ∈ sites siteID owner c, ∀ fs ∈ (state v).boxes, ∀ f ∈ fs,
      f.FieldBound (4*(M+E+1)^3) ∧ f.IDBound high) :
    let q := privateBits N cell state c
    let V := 4*(M+E+1)^3
    let dir := directory owner N cell siteID edgeID portID state c
      (countFields (countBase N cell state c) gadgets digits)
    dir.CompactFields q V ∧ Packet.RawFields dir q (max V high) := by
  let q := privateBits N cell state c
  let base := countBase N cell state c
  let rs := countFields base gadgets digits
  let dir := directory owner N cell siteID edgeID portID state c rs
  let V := 4*(M+E+1)^3
  change dir.CompactFields q V ∧ Packet.RawFields dir q (max V high)
  have hbank : base ≤ 3*M := (merged_bank_capacity N state cell c hin).trans (Nat.mul_le_mul_left _ hexp)
  have hq : q ≤ base := Nat.le_add_right ..
  have hW : 1 ≤ M+E+1 := by omega
  have hsquare : (M+1)^2 ≤ (M+E+1)^3 :=
    (Nat.pow_le_pow_left (by omega) 2).trans (Nat.pow_le_pow_right hW (by decide))
  have hM : M+1 ≤ (M+E+1)^3 :=
    (show M+1 ≤ M+E+1 by omega).trans (Nat.le_self_pow (by decide) _)
  have cap : base+gadgets*digits ≤ V := by
    rw [pow_two] at hsquare
    have hgd := (Nat.mul_le_mul hg hd).trans hsquare
    dsimp only [V]; omega
  have hsmall : 3*M+1 ≤ V := by dsimp only [V]; omega
  have hstore := (directory_load owner N cell siteID edgeID portID state c rs ho hschema).2.2.1.trans hpub
  have hvisit := (directory_load owner N cell siteID edgeID portID state c rs ho hschema).2.2.2.trans hexp
  obtain ⟨_,_,hlen,hreports,_⟩ := compiler_static N cell siteID edgeID portID owner state c base gadgets digits M E
    ho hschema hpub hexp hg hd
  have length := box_sizes dir
  have box : ∀ fs ∈ dir.boxes, fs.length ≤ V ∧ ∀ f ∈ fs, f.FieldBound V ∧ f.IDBound high := by
    intro fs hm
    refine ⟨(length.2 fs hm).trans (hstore.trans (by dsimp only [V]; omega)),?_⟩
    change fs ∈ (sites siteID owner c).flatMap (fun v => (state v).boxes) at hm
    obtain ⟨v,hv,hfs⟩ := List.mem_flatMap.mp hm
    exact hfactors v hv fs hfs
  have row : ∀ r ∈ dir.records, Packet.RecordFields r V := by
    intro r hr
    change r ∈ (sites siteID owner c).flatMap (fun v =>
      (state v).placedRows (off N cell siteID state v) (firstBox siteID owner state v) ++
        binding N cell siteID edgeID portID state v) at hr
    obtain ⟨v,hv,hr⟩ := List.mem_flatMap.mp hr
    have he := (ho v).symm.trans (site_owner siteID owner hv)
    rcases List.mem_append.mp hr with hp | ht
    · have hf := siteBase_fits N cell (cell v) siteID (fun i => (state i).size) ⟨v,rfl⟩
      have h0 : off N cell siteID state v ≤ privateBits N cell state (cell v) :=
        (Nat.le_add_right _ _).trans hf
      rw [he] at h0
      have h1 := (firstBox_le N cell siteID edgeID portID owner state hv rs).trans (length.1.trans hstore)
      exact ((state v).placed_recordFields (hscalar v hv) _ _ r hp).mono
        ((Nat.add_le_add_right (max_le (h0.trans (hq.trans hbank)) (by omega : firstBox siteID owner state v ≤ 3*M)) Z).trans hz)
    · have h := Placement.ties_recordFields N cell (cell v) siteID edgeID portID state ⟨v,rfl⟩ (hin v) r ht
      change Packet.RecordFields r (countBase N cell state (cell v)+1) at h
      rw [he] at h
      exact h.mono ((Nat.add_le_add_right hbank 1).trans hsmall)
  have rep : ∀ bs ∈ dir.reportedCounts, bs.length ≤ V ∧ ∀ i ∈ bs, i ≤ V := by
    intro bs hb
    obtain ⟨hl,ha⟩ := count_addresses base gadgets digits hb
    exact ⟨hl.le.trans (hd.trans (by dsimp only [V]; omega)),fun i hi => (ha i hi).le.trans cap⟩
  have hqv := hq.trans (hbank.trans (by omega : 3*M ≤ V))
  refine ⟨dir.compact_of_local hqv (hvisit.trans (by omega)) row (fun fs hf =>
    ⟨(box fs hf).1,fun f h => ((box fs hf).2 f h).1⟩) rep,?_⟩
  have vl : V ≤ max V high := le_max_left ..
  refine ⟨hqv.trans vl,⟨length.1.trans (hstore.trans (by omega)),hlen.trans vl,hreports.trans vl⟩,?_,
    fun r hr => (row r hr).mono vl,fun bs hb => ⟨(rep bs hb).1.trans vl,fun i hi => ((rep bs hb).2 i hi).trans vl⟩⟩
  intro fs hm
  refine ⟨(box fs hm).1.trans vl,fun f hf => ?_⟩
  obtain ⟨hfield,hids⟩ := (box fs hm).2 f hf
  exact ⟨hfield.mono vl,hids.mono (le_max_right ..)⟩

end Packing.Inherited.FinalCell

end BorderVNP
end Computability
end OAI
