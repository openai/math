import OAI.Hierarchy.DescentRetainedOriginalHeaders

namespace OAI
/-! # The four actual primary cable fields after the moved original, charged cursor and signed candidate have been added -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu
open DescentSIMDLookup DescentDenseHostOrder DescentResetOperandSetup DescentResetPublicOperandBook
open DescentResetRetainedSetup
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
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
variable (owner : a.successor.setup.Sources) (packet : a.successor.setup.seven.Packets) (strips : a.successor.setup.retained.Strips)
local notation "Y" => (C).assignedDigits hostEq groupEq owner.which packet strips
variable (block : Fin a.successor.setup.placement.blocks) (arg : Fin a.successor.setup.retained.args) (node : Fin a.successor.setup.retained.nodes)
variable (host : Fin a.successor.setup.placement.newHosts) (g : Fin a.successor.setup.placement.groups)
local notation "o" t:arg f:arg => (R).outputID t f arg node
local notation "ret" t:arg f:arg => ((DescentRetainedTargetPlacement.Chart.compact (C).placement (C).seven.batch
  menu.keep name (Y) (o t f) block host g).val : Cell (C).fieldBits)
variable (row : a.successor.setup.cable.Input) (head : a.successor.setup.cable.header row 0=((DescentRetainedTargetPlacement.Chart.compact a.successor.setup.placement a.successor.setup.seven.batch menu.keep name (a.successor.setup.assignedDigits hostEq groupEq owner.which packet strips) (a.successor.setup.retained.outputID 0 0 arg node) block host g).val : Cell a.successor.setup.fieldBits))
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

open DescentPackedZip ProtocolRAM DescentOperandCandidateLookup
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
local notation "H" => (C).placement.newHosts
local notation "G" => (C).placement.groups
local notation "full" t:arg f:arg => DescentRetainedTargetPlacement.Chart.compact (C).placement (C).seven.batch
  menu.keep name (Y) (o t f) block
variable {w : ℕ} (mem : Memory w) (base : ℕ)
variable (chunk : Fin (chunks a.successor.setup.placement.groups a.successor.setup.lanes)) (lane : Fin a.successor.setup.lanes)
local notation "rr" => DescentSIMDLookup.row H G (C).lanes (host,chunk)
local notation "readCell" t:arg f:arg => (encode (R).bits (C).lanes).symm
    ((((C).oldField base block (o t f)).eval mem ((rr).val:Word w)).val:Cell ((R).bits*(C).lanes)) lane


open DescentBundleHistory DescentKernelHistory DescentLocalPrivateNames DescentOperandStateBanks
open DescentRetainedControl DescentRetainedRangeDigits
variable (live : host.val<U)
local notation "shape" => (C).placement.shape (name ⟨host.val,live⟩)
local notation "carrier" => ((C).placement.previous (name ⟨host.val,live⟩)).cast hostEq
local notation "coarse" => (finProdFinEquiv (g,block)).cast groupEq
local notation "accept" => ownerAt C owner.which packet shape carrier coarse
local notation "prior" => priorAt C packet carrier coarse
local notation "before" => (R).site strips carrier coarse
local notation "restored" => (R).routedWord accept prior before
variable (primary : menu.keep (a.successor.setup.placement.shape (name ⟨host.val,live⟩))=true) (primaryBank : owner.primary=menu.keep)
  (signed : Fin a.successor.setup.strip→Fin a.successor.setup.placement.oldHosts→Fin (a.successor.setup.placement.groups*a.successor.setup.placement.blocks)→Cell a.successor.setup.signedBits)
  (moved : a.successor.setup.Moved base owner name mem (a.successor.setup.assignedDigits hostEq groupEq owner.which packet strips) signed)
  (hit : chunk.val*a.successor.setup.lanes+lane.val=g.val) (room : a.successor.setup.retained.bits*a.successor.setup.lanes≤w)
  (enough : a.successor.setup.retained.bits≤a.successor.setup.fieldBits) (output : a.successor.setup.retained.bits≤a.successor.receiver.valueBits)
  (order : Fin a.successor.setup.retained.donors≃Fin a.successor.setup.retained.donors) (rank : ∀d,neighbors (priorAt a.successor.setup packet ((a.successor.setup.placement.previous (name ⟨host.val,live⟩)).cast hostEq) ((finProdFinEquiv (g,block)).cast groupEq)) d=(order d).val)
  (d : Fin a.successor.setup.retained.donors) (oldNode : Fin a.successor.setup.retained.previousNodes) (oldArg : Fin a.successor.setup.retained.previousArgs)
  (take : (ownerAt a.successor.setup owner.which packet (a.successor.setup.placement.shape (name ⟨host.val,live⟩)) ((a.successor.setup.placement.previous (name ⟨host.val,live⟩)).cast hostEq) ((finProdFinEquiv (g,block)).cast groupEq)) d=true) (exists_ : oldNode.val<a.successor.setup.retained.originalCount (a.successor.setup.retained.site strips ((a.successor.setup.placement.previous (name ⟨host.val,live⟩)).cast hostEq) ((finProdFinEquiv (g,block)).cast groupEq)) d)
  (le : oldArg.val<(a.successor.setup.retained.entry (a.successor.setup.retained.site strips ((a.successor.setup.placement.previous (name ⟨host.val,live⟩)).cast hostEq) ((finProdFinEquiv (g,block)).cast groupEq)) d oldNode a.successor.setup.retained.arityField).val)
  (position : node.val=a.successor.setup.retained.offset (a.successor.setup.retained.routedWord (ownerAt a.successor.setup owner.which packet (a.successor.setup.placement.shape (name ⟨host.val,live⟩)) ((a.successor.setup.placement.previous (name ⟨host.val,live⟩)).cast hostEq) ((finProdFinEquiv (g,block)).cast groupEq)) (priorAt a.successor.setup packet ((a.successor.setup.placement.previous (name ⟨host.val,live⟩)).cast hostEq) ((finProdFinEquiv (g,block)).cast groupEq)) (a.successor.setup.retained.site strips ((a.successor.setup.placement.previous (name ⟨host.val,live⟩)).cast hostEq) ((finProdFinEquiv (g,block)).cast groupEq))) (order d)+oldNode.val) (argument : arg.val=oldArg.val)
local notation "priorField" f:arg => (R).entry before d oldNode ((R).operandField f oldArg)
variable {J : ℕ} (space : J<2^a.successor.setup.queryBits) (q₀ : Fin a.successor.setup.placement.newHosts→Fin a.successor.setup.placement.groups→Option (Fin J))
  (decoded : code space (q₀ host g)=queryDigit (a:=a) (a.successor.setup.cable.query row) ((publicOperands z roots menu.payload).rotor.flatReg z.board (publicOperands z roots menu.payload).multiplicity (publicOperands z roots menu.payload).grain (publicOperands z roots menu.payload).split ((finProdFinEquiv.symm i : Fin (publicOperands z roots menu.payload).args × Fin (publicOperands z roots menu.payload).nodes).2.val) ((finProdFinEquiv.symm i : Fin (publicOperands z roots menu.payload).args × Fin (publicOperands z roots menu.payload).nodes).1.val) 0 ((publicOperands z roots menu.payload).reg x) : Cell a.successor.setup.queryBits) ((publicOperands z roots menu.payload).column z.board a.successor.setup.queryBits none i x))
  (candidates : Fin 7→Fin J→Fin a.successor.setup.placement.newHosts→Fin a.successor.setup.placement.groups→Cell a.successor.receiver.valueBits)
local notation "f₇" f:arg => (f:Fin 4).castLE (by decide:4≤7)
local notation "actual" f:arg => (((posted (f₇ f)).val:Cell a.successor.receiver.valueBits).val+
  (selected q₀ (candidates (f₇ f)) host g).val)

open private queryDigit_only from OAI.Hierarchy.DescentIssuedRoleChoice
open private original_lane from OAI.Hierarchy.DescentIssuedRetainedHeaders
local notation "source" f:arg => (((priorField f).val:ℕ):Cell (C).fieldBits)
local notation "carriedPrice" f:arg => (C).cable.priceField (f₇ f) row

include blank physical primary primaryBank moved hit room rank take exists_ le position argument enough decoded in
/-- A cable in the real donor's previous node selects exactly its carried candidate.
Each masked moved field vanishes, so the emitted header consists of the registered
cursor correction and this same signed candidate. -/
theorem retained_archived_cable {b : ℕ} (alias_ : Cell b) (oldTag : (priorField 0).val=1) :
    code space (q₀ host g)=q ∧ ∀f:Fin 4,
      actual f=(((DescentResetRetainedPages.kept (f₇ f) (source 0) (source (f₇ f)) alias_).val+
        (carriedPrice f).val:ℕ):Cell a.successor.receiver.valueBits).val+
        (selected q₀ (candidates (f₇ f)) host g).val:=by
  obtain ⟨rq,pq⟩:=menu.private_public_off name host x i (C).queryBits none 0 blank physical live primary
  constructor
  · exact decoded.trans ((queryDigit_only (a:=a) q p s).1 rq pq)
  intro f
  let k:=f₇ f
  have localRead : readCell (1:Fin 2) k=(full 1 k) host g:=by
    apply original_lane menu name hostEq groupEq packet strips owner.which block arg node host g mem base chunk lane hit room
    simpa only [DescentResetOperandSetup.Chart.oldField,primaryBank] using moved.retained (o 1 k) block
  have payload:=moved_header_word C packet strips base owner name mem hostEq groupEq signed moved
    block host g live (1:Fin 2) (by rw [primaryBank];exact primary) order rank d oldNode oldArg take exists_ le
    node position arg argument k chunk lane hit room
  have readZero : readCell (1:Fin 2) k=(0:Cell (R).bits):=by
    simpa only [Fin.val_one,one_ne_zero,k,Fin.val_castLE,show ¬4≤f.val from Nat.not_le.mpr f.isLt,
      oldTag,show (1:ℕ)≠2 by decide,false_or,ite_false,and_false] using payload
  have unkept : (full 1 k) host g=0:=localRead.symm.trans readZero
  have zero : ret 1 k=0:=by simp only [unkept,Fin.val_zero,Nat.cast_zero]
  have tag : (source 0).val=1:=(Fin.val_cast_of_lt ((priorField 0).isLt.trans_le
    (Nat.pow_le_pow_right (by decide) enough))).trans oldTag
  have keep : DescentResetRetainedPages.kept k (source 0) (source k) alias_=0:=by
    simp [DescentResetRetainedPages.kept,DescentResetRetainedPages.aliasPart,tag,k,
      Nat.not_le.mpr f.isLt]
  obtain ⟨rp,pp⟩:=menu.private_public_off name host x i (C).fieldBits (some k) k.succ blank physical live primary
  have corrected : posted k = charge k := by
    rw [rp,pp,zero]
    simp only [Fin.val_zero,Nat.zero_add,Nat.add_zero]
    exact Fin.cast_val_eq_self _
  rw [corrected,keep]
  simp [k]

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu

end OAI
