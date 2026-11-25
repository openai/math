import OAI.Computability.MultitapeWeakETH.InitialHeader
import OAI.Computability.VPVNP.CompressorCompiledResident

/-! # The scheduler's entry memory for a packed formula graph -/

namespace OAI.Computability.MultitapeWeakETH.NativeGrid

open VPVNP Compression CompressorRecords DescriptorSpace BurstRAM
open PairSimulation.LocalHistory PairSimulation.TraversalRoles PairSimulation.TraversalRows
open CNFNetwork.InitialIncidence
open private field_addresses from OAI.Computability.VPVNP.CompressorScriptSnapshot
open scoped Classical Fin.CommRing
noncomputable section

variable {k R : Type} [Field k] [CommRing R] {S : BlockSchedule k} (B : S.Templates)
local notation "A" => BlockProgram.script B
local notation "degree" => S.degreeExponent 0
local notation "X" => CNFNetwork.inputState degree

private def schedulerMemory {w : ℕ} (arity total pitch : ℕ) (tag : Word w) : Memory w := fun x =>
  if x < 6 then Workspace.bank arity 0 (Fin.ofNat 6 x)
  else if x=6 then tag else if x=7 then 4 else if x=8 then total else if x=10+arity then pitch else 0

def entryMemory (g r n blocks w : ℕ) : Memory w :=
  let L := BlockProgram.layout B 0 ((X g r).positions) blocks
  levelMemory L degree g r n (schedulerMemory (Schedule.arity (A).catalog) (directoryRows L) (levelWords L)
    (LiveStageLink.tagWord w (Schedule.Online.calendarIndex (A).size (A).size)))

attribute [local irreducible] BlockProgram.script BlockProgram.layout

theorem entry_boundary {g r n blocks w : ℕ} (f : B.Entry → R) (hf : B.IsSolution f) :
    let L := BlockProgram.layout B 0 (X g r).positions blocks
    let m := entryMemory B g r n blocks w
    let initial : TaggedLayer := ⟨leafLayer (siteOrder (X g r)),.cursor⟩
    let frame := Frame.data (k:=8) (BlockHeaderRun.header w L 0+6) m
    endAddress L < 2^w → n < 2^w →
    ScheduledTrace.Boundary (CompiledResident.resident B f hf 0 (X g r).positions blocks n initial frame)
      (fun _ => 0) (levelWords L) (directoryRows L) (A).initial.length [] (X g r) m := by
  intro L m initial frame fit hn
  let ar := Schedule.arity (A).catalog
  let tag := LiveStageLink.tagWord w (Schedule.Online.calendarIndex (A).size (A).size)
  let old := schedulerMemory ar (directoryRows L) (levelWords L) tag
  have fields : L.shape.scalarFields = 54 := by unfold L BlockProgram.layout; rfl
  have levels : 0 < L.levels := by change 0 < (BlockProgram.layout B 0 _ blocks).levels; unfold BlockProgram.layout; change 0 < 1+_; omega
  have base : L.base=0 := by unfold L BlockProgram.layout; rfl
  have arity : L.shape.arity=ar := BlockProgram.layout_arity ..
  have headRoom : levelStart L 0 < 2^w := ((levelStart_mono L (Nat.zero_le L.levels)).trans_lt fit)
  have gap : 11+ar ≤ levelStart L 0 := by
    simp only [levelStart,levelsBase,directoryBase,plannerTag,frameBase,base,arity,Nat.zero_mul,Nat.add_zero]
    omega
  have work (x : ℕ) (h : x < 11+ar) : m x=old x := below L degree g r n old (h.trans_le gap)
  have cap : 11+ar < 2^w := gap.trans_lt headRoom
  let ports := Workspace.ports ar (0 : Word w)
  obtain ⟨ht,ho,hr,hd,_⟩ := field_addresses ar (0 : Word w) (by simpa using cap)
  change ports.tag.val=6 at ht
  change ports.ordinal.val=7 at ho
  change ports.rows.val=8 at hr
  simp only [Fin.val_zero,Nat.zero_add] at hd
  change ports.directory.val=11+ar at hd
  have stride : (ports.directory-1).val=10+ar := by
    rw [Fin.val_sub_one_of_ne_zero]; omega
    intro e
    have := congrArg Fin.val e
    change ports.directory.val=0 at this
    omega
  have rowRoom : directoryRows L < 2^w := by
    refine lt_of_le_of_lt ?_ headRoom
    have bound := Nat.le_mul_of_pos_right (directoryRows L) (by omega : 0 < L.shape.arity+3)
    unfold levelStart levelsBase
    omega
  have slotDeg : 2^degree ≤ slotDegree S :=
    (Finset.le_sup (f := fun j : Fin (S.steps+1) => 2^S.degreeExponent j) (Finset.mem_univ 0)).trans (le_max_right ..)
  have position : vertices g r*2^g = (X g r).positions := by
    rw [State.positions,Fintype.card_prod,card_base,(Fintype.card_congr (bitWordFinEquiv g)).trans (Fintype.card_fin _)]
  have slots : rows degree g r ≤ slotCapacity L := by
    change vertices g r*2^g*2^degree ≤ _
    rw [position]
    unfold slotCapacity L BlockProgram.layout
    exact Nat.mul_le_mul_left _ slotDeg
  have levelRoom : L.levels < 2^w := by
    have h : 0 < levelWords L := by unfold levelWords levelHeaderWords; omega
    exact (Nat.le_mul_of_pos_right L.levels h).trans_lt (by unfold endAddress levelStart at fit; omega)
  have rowBound : rows degree g r < 2^w := by
    have h := packed_incidence_room L fit ⟨0,levels⟩ slots
    omega
  have scalarFit : Scalars.Fits (.terminal degree) (vertices g r) g w := by
    have v : 0 < vertices g r := by unfold vertices; omega
    have dpos := Nat.two_pow_pos degree
    have lpos := Nat.two_pow_pos g
    change vertices g r*2^g*2^degree < 2^w at rowBound
    have vbound := Nat.le_mul_of_pos_right (vertices g r) lpos
    have lbound := Nat.le_mul_of_pos_left (2^g) v
    have pbound := Nat.le_mul_of_pos_right (vertices g r*2^g) dpos
    have dbound := Nat.le_mul_of_pos_left (2^degree) (Nat.mul_pos v lpos)
    intro j
    fin_cases j <;> simp [Scalars.values,Scalars.Pass.spent,Scalars.Pass.expanderDegree] <;> omega
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · funext j
    change Frame.data (0 : Word w) m j = Workspace.bank ar 0 j
    rw [Frame.data_at _ _ (by simpa using (show 6 ≤ 2^w by omega)),Fin.val_zero,Nat.zero_add,work _ (by have := j.isLt; omega)]
    simp [old,schedulerMemory,j.isLt]
  · change m ports.tag.val=tag
    rw [ht,work _ (by omega)]
    simp [old,schedulerMemory]
  · change (m ports.ordinal.val).val=_
    rw [ho,work _ (by omega),BlockProgram.initial_length]
    change (4 : Word w).val=4
    exact Nat.mod_eq_of_lt (show 4 < 2^w by omega)
  · change (m ports.rows.val).val=_
    rw [hr,work _ (by omega)]
    exact Nat.mod_eq_of_lt rowRoom
  · change m (ports.directory-1).val=_
    rw [stride,work _ (by omega)]
    simp [old,schedulerMemory,show ¬10+ar<6 by omega,show 10+ar≠6 by omega,show 10+ar≠7 by omega,show 10+ar≠8 by omega]
  · refine ⟨CurrentResident.empty ?_ (role L degree g r n old (by omega)) rfl,SelectedPayloadHistory.Past.empty⟩
    exact current L degree g r n old (by omega) levels fit hn levelRoom scalarFit (by
      unfold L BlockProgram.layout; exact position) slots

end
end OAI.Computability.MultitapeWeakETH.NativeGrid
