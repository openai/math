import OAI.Computability.BorderVNP.CellTeamIncomingCharge
import OAI.Computability.BorderVNP.PackedDirectoryKeys

/-! # Charging source bits to genuinely split physical delivery rows -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.TeamRowClock

open scoped Classical

/-- One bit of a source field or of an emitted interval. -/
abbrev FieldBit {I : Type*} (width : I → ℕ) := (i : I) × Fin (width i)

/-- Source-bit positions inject into real receiving row offsets. A source is
allowed to span multiple rows, including two adjacent processor literals. -/
structure BitDelivery {I A C : Type*} (cell : I → C) (bits : I → ℕ) (recv : A → C) (width : A → ℕ) where
  /-- Actual target row and offset for every source-field bit. -/
  index : FieldBit bits ↪ FieldBit width
  /-- The physical recipient is the cell hosting that original source. -/
  route : ∀ x, recv (index x).1=cell x.1

private theorem bit_sum {I C : Type*} [Fintype I] (cell : I → C) (width : I → ℕ) (owner : C → ℕ) (team : ℕ) :
    assignedSum (fun x : FieldBit width => owner (cell x.1)) team (fun _ => 1) = assignedSum (owner ∘ cell) team width := by
  simp only [assignedSum,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : owner (cell i)=team <;> simp [h]

/-- Charge the team's selected source bits to the true sum of the corresponding
native delivery widths even when the physical rows split a field. -/
theorem BitDelivery.load_le {I A C : Type*} [Fintype I] [Fintype A] {cell : I → C} {bits : I → ℕ}
    {recv : A → C} {width : A → ℕ} (d : BitDelivery cell bits recv width) (owner : C → ℕ) (team : ℕ) :
    assignedSum (owner ∘ cell) team bits ≤ assignedSum (owner ∘ recv) team width := by
  rw [←bit_sum cell bits owner team,←bit_sum recv width owner team]
  exact assignedSum_subitems d.index (fun x : FieldBit bits => cell x.1) (fun x : FieldBit width => recv x.1)
    owner team (fun _ => 1) (fun _ => 1) d.route (fun _ => le_rfl)

/-- Equal-size one-copy entries at each selected cell can be charged bitwise. -/
theorem BitDelivery.ordinal_load {C A : Type*} [Fintype C] [Fintype A] {recv : A → C} {width : A → ℕ}
    (num : C → ℕ) (desc : ℕ) (d : BitDelivery (fun i : (c : C) × Fin (num c) => i.1) (fun _ => desc) recv width)
    (owner : C → ℕ) (team : ℕ) : desc*assignedSum owner team num ≤ assignedSum (owner ∘ recv) team width := by
  apply le_trans _ (d.load_le owner team)
  simp only [assignedSum,Fintype.sum_sigma,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c _
  by_cases h : owner c=team <;> simp [h,Nat.mul_comm]

end Cube.TeamRowClock

namespace Packing.Directory

open Cube.TeamRowClock

/-- A logical delivery row and a physical compact RAM row agree on the two fields
used in the load. The ordinal map allows the surrounding runtime to reserve
additional data rows alongside this source directory. -/
structure RowLocations {A C : Type*} (rows : List Row) (encode : C → ℕ) (recv : A → C) (width : A → ℕ) where
  /-- Where the positive-width rows occur in the installed native array. -/
  ordinal : Fin rows.length ↪ A
  /-- The first projected field is the true receiving cell number. -/
  cell : ∀ i, encode (recv (ordinal i))=(rows.get i).cell
  /-- The native stored width is precisely the compact row width. -/
  span : ∀ i, width (ordinal i)=(rows.get i).width

/-- A real compact row and offset, retaining its full processor/source coordinates. -/
abbrev Layout.RowBit (d : Layout) (pp lp : ℕ → ℕ × ℕ) :=
  FieldBit (fun i : Fin (d.directory pp lp).length => ((d.directory pp lp).get i).width)

private theorem private_source {d : Layout} (pp lp : ℕ → ℕ × ℕ) (tail : 0<d.literal/2) (short : d.description≤d.literal/2)
    (x : FieldBit (fun _ : Fin d.entries => d.description)) :
    ∃ y : d.RowBit pp lp, let r := (d.directory pp lp).get y.1
      r.cell=(pp x.1).1 ∧ (r.team*d.processors+r.processor)*(d.literal/2)+
        (r.offset+y.2.val-(d.literal-d.literal/2)) = x.1.val*d.description+x.2.val := by
  obtain ⟨row,hr,j,hj,recv,_,source⟩ := d.private_delivered pp lp x.1 tail short x.2
  obtain ⟨i,hi,eq⟩ := List.getElem_of_mem hr
  subst row
  exact ⟨⟨⟨i,hi⟩,⟨j,hj⟩⟩,recv,source⟩

/-- The bit-addressed embedding for the actual two-piece private field format.
Distinct source bits have distinct returned row offsets by their original linear
processor-tail addresses. -/
noncomputable def Layout.privateBitDelivery {I A C : Type*} (d : Layout) (pp lp : ℕ → ℕ × ℕ)
    (cell : I → C) (entry : I ↪ Fin d.entries) (encode : C ↪ ℕ) (recv : A → C) (width : A → ℕ)
    (rows : RowLocations (d.directory pp lp) encode recv width)
    (placed : ∀ i, (pp (entry i)).1=encode (cell i)) (tail : 0<d.literal/2) (short : d.description≤d.literal/2) :
    BitDelivery cell (fun _ => d.description) recv width := by
  let get (x : FieldBit (fun _ : I => d.description)) :=
    (private_source pp lp tail short ⟨entry x.1,x.2⟩).choose
  let row (x : FieldBit (fun _ : I => d.description)) := (d.directory pp lp).get (get x).1
  let send (x : FieldBit (fun _ : I => d.description)) : FieldBit width :=
    ⟨rows.ordinal (get x).1,Fin.cast (rows.span (get x).1).symm (get x).2⟩
  have source (x : FieldBit (fun _ : I => d.description)) :
      (row x).cell=(pp (entry x.1)).1 ∧
      ((row x).team*d.processors+(row x).processor)*(d.literal/2)+
        ((row x).offset+(get x).2.val-(d.literal-d.literal/2)) = (entry x.1).val*d.description+x.2.val :=
    (private_source pp lp tail short ⟨entry x.1,x.2⟩).choose_spec
  refine ⟨⟨send,?_⟩,fun x => encode.injective ((rows.cell _).trans ((source x).1.trans (placed x.1)))⟩
  intro x y eq
  have index : (get x).1=(get y).1 := rows.ordinal.injective (congrArg Sigma.fst eq)
  have pos : (get x).2.val=(get y).2.val := congrArg (fun z : FieldBit width => z.2.val) eq
  have same : row x=row y := congrArg (d.directory pp lp).get index
  have key := (source x).2
  rw [same,pos,(source y).2] at key
  have quotient (z : FieldBit (fun _ : I => d.description)) :
      ((entry z.1).val*d.description+z.2.val)/d.description=(entry z.1).val := by
    rw [Nat.mul_comm (entry z.1).val,Nat.mul_add_div (Nat.zero_lt_of_lt z.2.isLt),Nat.div_eq_of_lt z.2.isLt,Nat.add_zero]
  have first := entry.injective (Fin.ext ((quotient y).symm.trans ((congrArg (·/d.description) key).trans (quotient x))))
  apply Sigma.ext first.symm
  apply heq_of_eq
  apply Fin.ext
  rw [first] at key
  omega

end Packing.Directory

end BorderVNP
end Computability
end OAI
