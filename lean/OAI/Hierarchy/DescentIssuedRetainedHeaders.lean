import OAI.Hierarchy.DescentIssuedRoleChoice
import OAI.Hierarchy.DescentRetainedMovedHeaders
import OAI.Hierarchy.DescentOperandCandidateLookup

namespace OAI
/-! A carried pin or local alias passes through the final candidate lookup unchanged. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu
open DescentSIMDLookup DescentDenseHostOrder DescentResetOperandSetup DescentResetPublicOperandBook
open DescentResetRetainedSetup
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
open private queryDigit_only from OAI.Hierarchy.DescentIssuedRoleChoice
variable {a : PhysicalReset} {z : a.Atlas} {roots : a.RootInputs} (menu : OperandMenu z roots)
local notation "C" => a.successor.setup
local notation "R" => (C).retained
local notation "cfg" => publicOperands z roots menu.payload
variable {U : ℕ} (name : Fin U→Fin a.successor.setup.placement.sparse)
variable (x : (publicOperands z roots menu.payload).Data a.successor.middle.rotorBits) (i : Fin (publicOperands z roots menu.payload).mouths)
local notation "reg" => (cfg).reg x
local notation "loc" => (finProdFinEquiv.symm i : Fin (cfg).args × Fin (cfg).nodes)
local notation "prv" b:arg f:arg => ((cfg).rotor.flatReg z.board (cfg).multiplicity (cfg).grain (cfg).split
  (loc).2.val (loc).1.val f (reg) : Cell b)
local notation "pub" b:arg f:arg => (cfg).column z.board b f i x
variable (hostEq : a.successor.setup.placement.oldHosts=a.successor.setup.retained.hosts) (groupEq : a.successor.setup.placement.groups*a.successor.setup.placement.blocks=a.successor.setup.retained.grouped)
variable (packet : a.successor.setup.seven.Packets) (strips : a.successor.setup.retained.Strips) (which : a.successor.setup.seven.control.Targets)
local notation "Y" => (C).assignedDigits hostEq groupEq which packet strips
variable (block : Fin a.successor.setup.placement.blocks) (arg : Fin a.successor.setup.retained.args) (node : Fin a.successor.setup.retained.nodes)
variable (host : Fin a.successor.setup.placement.newHosts) (g : Fin a.successor.setup.placement.groups)
local notation "o" t:arg f:arg => (R).outputID t f arg node
local notation "ret" t:arg f:arg => ((DescentRetainedTargetPlacement.Chart.compact (C).placement (C).seven.batch
  menu.keep name (Y) (o t f) block host g).val : Cell (C).fieldBits)
variable (row : a.successor.setup.cable.Input) (head : a.successor.setup.cable.header row 0=((DescentRetainedTargetPlacement.Chart.compact a.successor.setup.placement a.successor.setup.seven.batch menu.keep name (a.successor.setup.assignedDigits hostEq groupEq which packet strips) (a.successor.setup.retained.outputID 0 0 arg node) block host g).val : Cell a.successor.setup.fieldBits))
variable (blank : ((publicOperands z roots menu.payload).oldConfig.header ((publicOperands z roots menu.payload).basic x) 0).val=0 → (((publicOperands z roots menu.payload).reg x) 1).val=0)
variable (physical : ∀hv : host.val<U,((publicOperands z roots menu.payload).oldConfig.header ((publicOperands z roots menu.payload).basic x) 0).val≠0 →
    (((publicOperands z roots menu.payload).reg x) 3).val=(a.successor.setup.placement.shape (name ⟨host.val,hv⟩)).val)
local notation "q" => (C).cable.query row
local notation "p" => prv (C).queryBits 0
local notation "s" => pub (C).queryBits none

local notation "charge" f:arg => (C).cable.priceField f row
local notation "rotorValue" f:arg => prv (C).fieldBits (f).succ
local notation "publicValue" f:arg => pub (C).fieldBits (some f)
local notation "posted" f:arg => (((ret 1 f).val+(charge f).val+(rotorValue f).val+(publicValue f).val:ℕ) : Cell (C).fieldBits)

local notation "ordinal" => queryDigit (a:=a) q p s

include blank physical in
theorem retained_noncable (live : host.val<U) (primary : menu.keep ((C).placement.shape (name ⟨host.val,live⟩))=true)
    (other : ((C).cable.header row 0).val≠1) :
    ordinal=0 ∧ ∀f : Fin 7,posted f=ret 1 f:=by
  have no:=(C).cable.absent row other
  have free:=(C).cable.charge_none row no
  obtain ⟨privateQuery,publicQuery⟩:=menu.private_public_off name host x i (C).queryBits none 0 blank physical live primary
  refine ⟨?_,?_⟩
  · exact ((queryDigit_only (a:=a) q p s).1 privateQuery publicQuery).trans ((C).cable.query_none row no)
  intro f
  have chargeZero : charge f=0:=by
    simp only [DescentResetRetainedCableLaw.Shape.priceField,free,ite_self]
  obtain ⟨privateField,publicField⟩:=menu.private_public_off name host x i (C).fieldBits (some f) f.succ blank physical live primary
  rw [chargeZero,privateField,publicField]
  simp only [Fin.val_zero,Nat.add_zero]
  exact Fin.cast_val_eq_self _

open DescentPackedZip ProtocolRAM DescentOperandCandidateLookup
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
local notation "H" => (C).placement.newHosts
local notation "G" => (C).placement.groups
local notation "full" t:arg f:arg => DescentRetainedTargetPlacement.Chart.compact (C).placement (C).seven.batch
  menu.keep name (Y) (o t f) block
variable {w : ℕ} (mem : Memory w) (base : ℕ) (owner : a.successor.setup.Sources)
variable (chunk : Fin (chunks a.successor.setup.placement.groups a.successor.setup.lanes)) (lane : Fin a.successor.setup.lanes)
local notation "rr" => DescentSIMDLookup.row H G (C).lanes (host,chunk)
local notation "readCell" t:arg f:arg => (encode (R).bits (C).lanes).symm
    ((((C).oldField base block (o t f)).eval mem ((rr).val:Word w)).val:Cell ((R).bits*(C).lanes)) lane

private theorem original_lane {mode : Fin 2} {f : Fin 7} (hit : chunk.val*(C).lanes+lane.val=g.val)
    (room : (R).bits*(C).lanes≤w)
    (load : Source ((C).oldField base block (o mode f)) (full mode f) (C).lanes mem) :
    readCell mode f=(full mode f) host g:=by
  have packed:=load (host,chunk)
  have size : (data (full mode f) (host,chunk)).val<2^w:=
    (data (full mode f) (host,chunk)).isLt.trans_le (Nat.pow_le_pow_right (by decide) room)
  have same : (((((C).oldField base block (o mode f)).eval mem ((rr).val:Word w)).val:ℕ):
      Cell ((R).bits*(C).lanes))=data (full mode f) (host,chunk):=by
    apply Fin.ext
    change _%2^((R).bits*(C).lanes)=_
    rw [packed,Fin.val_cast_of_lt size]
    exact Nat.mod_eq_of_lt (data (full mode f) (host,chunk)).isLt
  rw [same]
  let values : Fin H → Fin G → Cell (R).bits := full mode f
  change ((encode (R).bits (C).lanes).symm (data values (host,chunk))) lane = values host g
  have inside : chunk.val*(C).lanes+lane.val<G := hit.trans_lt g.isLt
  have sameGroup : (⟨chunk.val*(C).lanes+lane.val,inside⟩:Fin G)=g := Fin.ext hit
  simp only [data,Equiv.symm_apply_apply,dite_true,inside,sameGroup]

include head blank physical in
theorem retained_header_at (live : host.val<U) (primary : menu.keep ((C).placement.shape (name ⟨host.val,live⟩))=true)
    (primaryBank : owner.primary=menu.keep)
    (signed : Fin (C).strip→Fin (C).placement.oldHosts→Fin (G*(C).placement.blocks)→Cell (C).signedBits)
    (moved : (C).Moved base owner name mem (Y) signed) (hit : chunk.val*(C).lanes+lane.val=g.val)
    (room : (R).bits*(C).lanes≤w) (enough : (R).bits≤(C).fieldBits) (output : (R).bits≤a.successor.receiver.valueBits)
    (other : (readCell (0:Fin 2) (0:Fin 7)).val≠1)
    (expected : Fin 7→ℕ) (stored : ∀f,(readCell (1:Fin 2) f).val=expected f)
    {J : ℕ} (space : J<2^(C).queryBits) (q₀ : Fin H→Fin G→Option (Fin J))
    (decoded : code space (q₀ host g)=ordinal)
    (candidates : Fin 7→Fin J→Fin H→Fin G→Cell a.successor.receiver.valueBits) :
    ∀f : Fin 7,(((posted f).val : Cell a.successor.receiver.valueBits).val+
      (selected q₀ (candidates f) host g).val)=expected f:=by
  have atCell (mode : Fin 2) (f : Fin 7) : readCell mode f=(full mode f) host g:=by
    apply original_lane menu name hostEq groupEq packet strips which block arg node host g mem base chunk lane hit room
    simpa only [DescentResetOperandSetup.Chart.oldField,primaryBank] using moved.retained (o mode f) block
  have fit (t f) : ((full t f) host g).val<2^(C).fieldBits:=
    ((full t f) host g).isLt.trans_le (Nat.pow_le_pow_right (by decide) enough)
  have tag : ((C).cable.header row 0).val≠1:=by
    rw [head,Fin.val_cast_of_lt (fit 0 0),←atCell 0 0]
    exact other
  obtain ⟨zero,old⟩:=menu.retained_noncable name x i hostEq groupEq packet strips which block arg node host g row
    blank physical live primary tag
  have absent : q₀ host g=none:=by
    cases e:q₀ host g with
    | none=>rfl
    | some j=>
      have eq:=congrArg Fin.val ((decoded.trans zero))
      rw [e] at eq
      change j.val+1=0 at eq
      omega
  intro f
  have small:=((full 1 f) host g).isLt.trans_le (Nat.pow_le_pow_right (by decide) output)
  rw [old f,Fin.val_cast_of_lt (fit 1 f),Fin.val_cast_of_lt small]
  simp only [selected,absent,Option.elim_none,Fin.val_zero,Nat.add_zero]
  exact (congrArg Fin.val (atCell 1 f)).symm.trans (stored f)

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu

end OAI
