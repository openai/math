import OAI.Hierarchy.DescentRegisteredEntryAddress
import OAI.Hierarchy.DescentFundedIngressTariff

namespace OAI
/-! Buying the actual entry address space from the old archive and the dated width purchase. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentSIMDLookup DescentDatedPriorOperand DescentOrdinaryVenueIngress
open DescentRawCablePanel Filter
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {ι : ℕ→Type*} {P : ∀ h,ι h→Type}
    (v : ∀ h i, PhysicalOrdinary F (P h i)) (prior : ∀ h,ι h→DatePorts)
    (floor : ∀ h,ι h→ℕ)
local notation "W_" => fun h i => (v h i).registeredFrom (prior h i) (floor h i)
local notation "A_" => fun h i => (v h i).registeredEntry (prior h i) (floor h i)
local notation "C_" => fun h i => ((A_) h i).clip
local notation "old_" => fun h i => ((A_) h i).previous

private theorem linear_bounded {x : ∀ h,ι h→ℕ} (a : Linear x) : Bounded x :=
  a.table.of_le (fun _ _ => Nat.lt_two_pow_self.le)

theorem registered_entry_source_bounds
    (hosts : Bounded (fun h i => ((C_) h i).venue.hosts))
    (groups : Bounded (fun h i => ((C_) h i).venue.groups))
    (degree : Bounded (fun h i => ((C_) h i).venue.socket.degree))
    (blocks : Bounded (fun h i => ((C_) h i).venue.socket.blocks))
    (seats : Bounded (fun h i => ((C_) h i).venue.socket.cap))
    (lows : Bounded (fun h i => ((W_) h i).vector.lows))
    (oldBlocks : Bounded (fun h i => ((old_) h i).blocks))
    (oldNodes : Bounded (fun h i => (prior h i).nodes))
    (oldArgs : Bounded (fun h i => (prior h i).argumentsPerNode))
    (oldHosts : Bounded (fun h i => (prior h i).operandHosts))
    (oldGroups : Bounded (fun h i => (prior h i).venue.groups))
    (payload : ∀ h i,(v h i).payload=h)
    (initial : ∀ᶠ h : ℕ in atTop,∀ i,let b:=v h i;let t:=prior h i;let a:=(A_) h i;
      0<t.nodes ∧ 2≤t.operandBits ∧ t.operandBits*t.nodes*t.operandLanes≤h ∧
      0<a.roleBits ∧ a.roleBits*t.nodes*t.roleLanes≤h ∧
      ((W_) h i).reference.oldNodes=t.nodes ∧ 2^b.area.k+1≤b.area.unit) :
    EntryAddressInputs v prior floor := by
  let cst := fun n => Bounded.const (ι:=ι) n
  have bus : Linear (fun h (i:ι h) => (v h i).payload) := ⟨1,Eventually.of_forall (by
    intro h i
    change (v h i).payload ≤ 1*h
    rw [payload,one_mul])⟩
  have panels : Bounded (fun h i => ((C_) h i).panelPitch) := (linear_bounded bus).of_le (fun h i =>
    (Nat.div_le_self _ _ : lanes (v h i).payload _ ≤ _))
  have actors : Bounded (fun h i => ((C_) h i).actorPitch) := (linear_bounded bus).of_le (fun h i =>
    (Nat.div_le_self _ _ : lanes (v h i).payload _ ≤ _))
  have racks := (degree.add (cst 1)).pow 4
  have parts := (cst 1).add (seats.mul (cst 6))
  have rolePitch : Linear (fun h i => (prior h i).roleLanes) := by
    refine ⟨1,initial.mono ?_⟩
    intro h data i
    obtain ⟨nodes,_,_,role,packed,_⟩ := data i
    simpa only [one_mul] using (Nat.le_mul_of_pos_left _ (Nat.mul_pos role nodes)).trans packed
  have prevPitch : Linear (fun h i => ((old_) h i).lanes) := by
    refine ⟨1,initial.mono ?_⟩
    intro h data i
    obtain ⟨nodes,bits,packed,_⟩ := data i
    change (prior h i).operandLanes ≤ 1*h
    simpa only [one_mul] using (Nat.le_mul_of_pos_left _ (Nat.mul_pos (by omega : 0 < (prior h i).operandBits) nodes)).trans packed
  refine ⟨⟨oldBlocks,oldNodes,oldArgs,oldHosts,oldGroups,linear_bounded prevPitch,11,?_⟩,
    ⟨hosts,groups,racks,blocks.mul parts,(racks.mul blocks).mul parts,panels,actors,
      panels.of_le (fun h i => (((C_) h i).working_fields).1),bus⟩,?_,linear_bounded rolePitch,?_,?_,lows,?_⟩
  · filter_upwards [initial] with h data
    intro i l
    obtain ⟨nodes,bits,packed,_⟩ := data i
    have base : (prior h i).operandBits*(prior h i).operandLanes ≤ h :=
      (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ nodes)).trans packed
    constructor
    · change (((prior h i).operandBits-2+2)*(prior h i).nodes)*(prior h i).operandLanes ≤ 11*h
      rw [Nat.sub_add_cancel bits]
      omega
    change 11*((prior h i).operandBits-2+2)*(prior h i).operandLanes ≤ 11*h
    rw [Nat.sub_add_cancel bits,Nat.mul_assoc]
    exact Nat.mul_le_mul_left 11 base
  · filter_upwards [initial] with h data
    intro i c
    obtain ⟨_,_,_,_,_,_,full⟩ := data i
    have within := (v h i).funded_input_width ((v h i).argumentUnitFrom (prior h i) (floor h i)) full
    exact within
  · refine ⟨1,initial.mono ?_⟩
    intro h data i
    obtain ⟨_,_,_,_,roles,same,_⟩ := data i
    change (((A_) h i).roleBits*((W_) h i).reference.oldNodes)*(prior h i).roleLanes ≤ 1*h
    rw [same,one_mul]
    exact roles
  · refine ⟨1,Eventually.of_forall ?_⟩
    intro h i
    have width := ((v h i).registered_width (prior h i) (floor h i)).1 3
    change ((W_) h i).argumentWidths ((A_) h i) 3 * ((C_) h i).working ≤ 1*h
    exact (width.trans (Nat.div_le_self _ _)).trans_eq ((payload h i).trans (one_mul h).symm)
  · refine ⟨1,Eventually.of_forall ?_⟩
    intro h i pop
    have w₀ := ((v h i).registered_width (prior h i) (floor h i)).1 1
    have w₁ := ((v h i).registered_width (prior h i) (floor h i)).1 2
    have limit : (v h i).payload/4 ≤ 1*h :=
      (Nat.div_le_self _ _).trans_eq ((payload h i).trans (one_mul h).symm)
    exact ⟨w₀.trans limit,w₁.trans limit⟩

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
