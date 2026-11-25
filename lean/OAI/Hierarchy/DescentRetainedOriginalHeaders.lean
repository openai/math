import OAI.Hierarchy.DescentIssuedRetainedHeaders
import OAI.Hierarchy.DescentReachedArgumentPointer

namespace OAI
/-! Four archived source fields on an actual retained operand and their transported values. -/
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

private def priorSpan {valueBits : ℕ} (sourceFields : Fin 7→Cell valueBits) : Span :=
  ⟨(sourceFields 4).val,(sourceFields 5).val,(sourceFields 6).val⟩

private theorem prior_fields {valueBits : ℕ} (sourceFields : Fin 7→Cell valueBits) (pointer : Pointer)
    (known : ∀f:Fin 4,(sourceFields (f₇ f)).val=pointer.header f) (f : Fin 7) :
    (sourceFields f).val=pointer.fields (priorSpan sourceFields) f:=by
  by_cases within : f.val<4
  · let k : Fin 4:=⟨f.val,within⟩
    have widen : f₇ k=f := Fin.ext rfl
    calc
      (sourceFields f).val=(sourceFields (f₇ k)).val:=congrArg (fun j=>(sourceFields j).val) widen.symm
      _ = pointer.header k:=known k
      _ = pointer.fields (priorSpan sourceFields) f:=by simp [Pointer.fields,within,k]
  · fin_cases f <;> first | rfl | exact False.elim (within (by decide))

private theorem four_fields (pointer : Pointer) (span : Span) (f : Fin 4) :
    pointer.fields span (f₇ f)=pointer.header f:=by
  simp [Pointer.fields,f.isLt]

include moved primaryBank primary rank take exists_ le position argument hit room in
private theorem original_tag : (readCell (0:Fin 2) (0:Fin 7)).val=(priorField 0).val:=by
  have old:=moved_header_word C packet strips base owner name mem hostEq groupEq signed moved
    block host g live (0:Fin 2) (by rw [primaryBank];exact primary) order rank d oldNode oldArg take exists_ le
    node position arg argument 0 chunk lane hit room
  simpa only [Fin.val_zero,true_or,ite_true] using congrArg Fin.val old

include moved head blank physical primary primaryBank rank take exists_ le position argument hit room
  enough output decoded in
/-- A true old pin is copied under its original label and chunk in every header field. -/
theorem retained_archived_pin (copy fine : ℕ)
    (old : ∀f:Fin 4,(priorField (f₇ f)).val=(Pointer.pin copy fine).header f) :
    ∀f:Fin 4,actual f=(Pointer.pin copy fine).header f:=by
  let span:=priorSpan (fun f=>priorField f)
  have sourceFields:=prior_fields (fun f=>priorField f) (Pointer.pin copy fine) old
  have tag:=original_tag (menu:=menu) (owner:=owner) (name:=name) (mem:=mem) (base:=base)
    (hostEq:=hostEq) (groupEq:=groupEq) (packet:=packet) (strips:=strips)
    (block:=block) (arg:=arg) (node:=node) (host:=host) (g:=g) (live:=live)
    (primary:=primary) (primaryBank:=primaryBank) (signed:=signed) (moved:=moved)
    (rank:=rank) (take:=take) (exists_:=exists_) (le:=le) (position:=position) (argument:=argument)
    (hit:=hit) (room:=room)
  have no : (readCell (0:Fin 2) (0:Fin 7)).val≠1:=by
    have value : (readCell (0:Fin 2) (0:Fin 7)).val=(Pointer.pin copy fine).header 0 := tag.trans (old 0)
    exact fun h => (show (2:ℕ) ≠ 1 by decide) (value.symm.trans h)
  have stored (f : Fin 7) := moved_original_pin C packet strips base owner name mem hostEq groupEq signed moved
    block host g live (by rw [primaryBank];exact primary) order rank d oldNode oldArg take exists_ le node position arg argument
    copy fine span sourceFields f chunk lane hit room
  intro f
  exact (retained_header_at (menu:=menu) (name:=name) (x:=x) (i:=i) (hostEq:=hostEq) (groupEq:=groupEq)
    (packet:=packet) (strips:=strips) (which:=owner.which) (block:=block) (arg:=arg) (node:=node)
    (host:=host) (g:=g) (row:=row) (head:=head) (blank:=blank) (physical:=physical)
    (mem:=mem) (base:=base) (owner:=owner) (chunk:=chunk) (lane:=lane) live primary primaryBank
    signed moved hit room enough output no ((Pointer.pin copy fine).fields span) stored
    space q₀ decoded candidates (f₇ f)).trans (four_fields ..)

include moved head blank physical primary primaryBank rank take exists_ le position argument hit room
  enough output decoded in
/-- A true old private reference receives the least occupied address of its
word in the reached primary recipe. -/
theorem retained_archived_private {Tag Out : Type} (r : Recipe Tag Out)
    (positions : Slot r↪Fin ((R).nodes*(R).args)) (key : r.UsedWord↪(Fin (R).donors×Cell (R).bits))
    (word : r.UsedWord) (oldName : ℕ)
    (old : ∀f:Fin 4,(priorField (f₇ f)).val=(Pointer.privateWord oldName).header f)
    (realKeys : ∀u,(R).keyIndex restored (positions u)=(read r u).map key)
    (padding : ∀i,(∀u,positions u≠i)→(R).keyIndex restored i=none)
    (keyUsed : key word=(order d,priorField 2)) (width : (firstAlias r positions word).val<2^(R).bits) :
    ∀f:Fin 4,actual f=(Pointer.privateWord (firstAlias r positions word).val).header f:=by
  let span:=priorSpan (fun f=>priorField f)
  have sourceFields:=prior_fields (fun f=>priorField f) (Pointer.privateWord oldName) old
  have tag:=original_tag (menu:=menu) (owner:=owner) (name:=name) (mem:=mem) (base:=base)
    (hostEq:=hostEq) (groupEq:=groupEq) (packet:=packet) (strips:=strips)
    (block:=block) (arg:=arg) (node:=node) (host:=host) (g:=g) (live:=live)
    (primary:=primary) (primaryBank:=primaryBank) (signed:=signed) (moved:=moved)
    (rank:=rank) (take:=take) (exists_:=exists_) (le:=le) (position:=position) (argument:=argument)
    (hit:=hit) (room:=room)
  have no : (readCell (0:Fin 2) (0:Fin 7)).val≠1:=by
    have value : (readCell (0:Fin 2) (0:Fin 7)).val=(Pointer.privateWord oldName).header 0 := tag.trans (old 0)
    exact fun h => (show (0:ℕ) ≠ 1 by decide) (value.symm.trans h)
  have stored (f : Fin 7) := moved_original_private C packet strips base owner name mem hostEq groupEq signed moved
    block host g live (by rw [primaryBank];exact primary) order rank d oldNode oldArg take exists_ le node position arg argument
    r positions key word oldName span sourceFields realKeys padding keyUsed width f chunk lane hit room
  intro f
  exact (retained_header_at (menu:=menu) (name:=name) (x:=x) (i:=i) (hostEq:=hostEq) (groupEq:=groupEq)
    (packet:=packet) (strips:=strips) (which:=owner.which) (block:=block) (arg:=arg) (node:=node)
    (host:=host) (g:=g) (row:=row) (head:=head) (blank:=blank) (physical:=physical)
    (mem:=mem) (base:=base) (owner:=owner) (chunk:=chunk) (lane:=lane) live primary primaryBank
    signed moved hit room enough output no ((Pointer.privateWord (firstAlias r positions word).val).fields span)
    stored space q₀ decoded candidates (f₇ f)).trans (four_fields ..)

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu

end OAI
