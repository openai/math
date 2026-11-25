import OAI.Hierarchy.DescentOrdinaryRawOperandOrigin
import OAI.Hierarchy.DescentPrivateRawLabels
import OAI.Hierarchy.DescentDatedCableJobCatalog
import OAI.Hierarchy.DescentOrdinaryBornRoleNumerals

namespace OAI
/-! The original matched cable and typed selector of a newborn party's physical operand. -/
namespace Hierarchy.DescentOrdinaryBorn
open Computability.BorderVNP.Crossing DescentSixParty DescentKernelHistory GadgetNetwork DescentBundleHistory
open DescentOperandPhysicalInput DescentCableDonorNames
noncomputable section
set_option quotPrecheck false
variable {E I : Type}

def edgeOf (pick:I×Fin 2↪E) (i:I) : Role→Raw E I
  | .original s=>.inl (pick (i,s))
  | .arm s=>.inr (.inl (i,s))
  | .supply s=>.inr (.inr (i,s))

theorem mouth_address (pick:I×Fin 2↪E) (i:I) (m:Mouth) :
    anchor pick (edgeOf pick i m.origin)=pick (i,m.anchor) ∧
    (DescentCableDonorNames.role (edgeOf pick i m.origin)).val=m.rawRole :=by
  rcases m with ⟨side,target,chunk⟩
  cases side <;> exact ⟨rfl,rfl⟩

variable {F P : Type} [Field F] [Fintype I] {d p : ℕ} {bits:P→ℕ}
    (W:MarkedWorld F d P bits) (G:PoweredGadget F) (pick:I×Fin 2↪W.graph.Edge)
    (z:I→ℕ) (pr:I→Profile G.C)
local notation "raw" => physical W.graph pick (branchWidth G z pr)
def cableAt {Y:Type} (v:(raw).Site) : BlockRef p (boundaryWidth (raw) v)⊕Y→Option ((raw).Edge×ℕ)
  | .inl ⟨.inl e,k,_⟩=>some (e.val,k)
  | _=>none

private def portCable {v : (raw).Site} (port : Boundary (raw) v) (piece : ℕ) : Option ((raw).Edge×ℕ) :=
  match port with
  | .inl e => some (e.val,piece)
  | .inr _ => none

private theorem cableAt_input {Y : Type} (v : (raw).Site) (b : BlockRef p (boundaryWidth (raw) v)) :
    cableAt W G pick z pr (Y:=Y) v (.inl b) = portCable W G pick z pr b.port b.block := by
  rcases b with ⟨edge|pin,offset,width⟩ <;> rfl

private theorem socket_edge (i:I) (party:Fin 6) (t:RolePort party) (lane:ℕ) :
    portCable W G pick z pr (nativeRole W.graph pick (branchWidth G z pr) i party t) lane=some (edgeOf pick i (DescentOperandPhysicalInput.role t),lane) :=by
  rcases t with (t|t)|(t|t) <;> rfl

theorem occurrence_address (hp:0<p) {i:I} {party:Fin 6} (o:Occurrence W G pick z pr p i party) (Y:Type) :
    let m:=occurrenceMouth W G pick z pr o
    cableAt W G pick z pr (.inr (i,party)) (Y:=Y) (.inl (occurrenceBlock W G pick z pr hp o))=
      some (edgeOf pick i m.origin,m.chunk) :=by
  rcases o with ⟨a,g⟩
  exact (cableAt_input W G pick z pr (Y:=Y) (.inr (i,party))
    (occurrenceBlock W G pick z pr hp ⟨a,g⟩)).trans
    (socket_edge W G pick z pr i party ((roleIndex party).symm a) g.val)

variable {Z:ℕ} (room:∀i,z i≤Z) (hp:0<p) (B:BitDescription W)
    (old:∀v,Shape p (B.recipe v)) (wires:∀e,p∣W.graph.width e) (pins:∀i,p∣bits i) (unit:∀i,p∣z i)
local notation "shape" => physicalShape W B G pick z room pr hp old wires pins unit
local notation "loc" => NodeOrder.physicalNames B G pick z room pr
local notation:max "source_" root:arg => (loc).symm root

theorem born_address (fit:∀i s,W.graph.width (pick (i,s))=z i*G.b)
    (root:NodeOrder.All B⊕(I×Fin 6)) (i:I) (party:Fin 6) (birth:root=.inr (i,party))
    (arg:Fin (((shape (source_ root).1).recipe hp).arity (source_ root).2))
    (e:(raw).Edge) (piece:ℕ)
    (read:cableAt W G pick z pr (source_ root).1 (((shape (source_ root).1).recipe hp).operand (source_ root).2 arg)=some (e,piece)) :
    ∃o:Occurrence W G pick z pr p i party,
      (occurrences W G pick z pr p i party)[arg.val]?=some o ∧
      let m:=occurrenceMouth W G pick z pr o
      mouth (actual G p) (z i) (DescentPacking.PackedMatch.LayoutSum.profileCode G.C (pr i)).val party arg.val=some m ∧
      e=edgeOf pick i m.origin ∧ piece=m.chunk :=by
  subst root
  obtain ⟨o,selected,live,source,_⟩:=DescentOrdinaryRawOperandOrigin.raw_born_read W B G pick z room pr
    hp old wires pins unit fit i party arg (Fintype.equivFin W.graph.Edge) (Fintype.equivFin I)
  refine ⟨o,selected,live,?_⟩
  let m:=occurrenceMouth W G pick z pr o
  change cableAt W G pick z pr (.inr (i,party)) (((shape (.inr (i,party))).recipe hp).operand () arg)=some (e,piece) at read
  rw [source,occurrence_address] at read
  exact ⟨(congrArg Prod.fst (Option.some.inj read)).symm,(congrArg Prod.snd (Option.some.inj read)).symm⟩


/-- The paid donor pages select the very same role, direction and word as the
original occurrence list. Their three short output cells can now be read
at the registered argument without constructing another operand list. -/
theorem observed_pointer {i:I} {party:Fin 6} (o:Occurrence W G pick z pr p i party)
    (j:ℕ) (found:mouth (actual G p) (z i) (DescentPacking.PackedMatch.LayoutSum.profileCode G.C (pr i)).val party j
      =some (occurrenceMouth W G pick z pr o))
    {«loc» nam width:ℕ} (donor:DescentRawCablePanel.Donor «loc» nam width) (first:donor.first=true)
    (supply:∀s,(donor.supplyUnits s).val=((pr i).val s).val+G.k) (bits:ℕ) (wide:11≤2^bits) :
    let m:=occurrenceMouth W G pick z pr o
    let result:=pointerAt G.b p (z i) donor party j
    result=some m ∧ ∀f,(RolePorts.value bits result f).val=RolePorts.numeral m f :=by
  intro m result
  have offered:∀e,(donor.supplyUnits e).val=
      (profileDigits (actual G p).capacity (DescentPacking.PackedMatch.LayoutSum.profileCode G.C (pr i)).val e).val
        +(actual G p).supplyOffset:=by
    intro e
    simpa only [actual,profile_read] using supply e
  have read:result=some m:=(pointer_first (actual G p) (z i) _ j party donor first offered).trans found
  exact ⟨read,fun f=>by rw [read];exact RolePorts.value_live bits wide m f⟩

end
end Hierarchy.DescentOrdinaryBorn

namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentSixParty DescentStageEdgeReceipt DescentHostDirectory DescentSharedCableNames DescentOrdinaryBorn
noncomputable section
set_option quotPrecheck false
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {d k:ℕ} {bits:P→ℕ} {W:MarkedWorld F d P bits} {G:PoweredGadget F} {q ε:ℝ}
  (A:GroupStage W G q ε J V k) (he:0≤ε)
attribute [local irreducible] DescentKernelHistory.BitDescription.scannedRows DescentPacking.slabPacking
local notation "r" => DescentKernelHistory.BitDescription.scannedRows he A.stage
private def newbornMember (i : (r).pairs) (side : Bool) : DescentSharedCableNames.Stage.Positive A := by
  let chosen := picked A he i.1 i.2 side
  exact ⟨chosen.val,A.quantum_positive chosen.val chosen.property.1⟩

local notation:max "member" i:arg b:arg => newbornMember A he i b

set_option maxHeartbeats 700000 in
theorem newborn_port (i:(r).pairs) (m:Mouth) (raw:DescentRawCablePanel.Live A (r).pick)
    (same:raw.val=edgeOf (r).pick i m.origin) :
    let second:=decide (m.anchor.val=1)
    m.anchor.val=second.toNat ∧ m.rawRole=(DescentCableDonorNames.role raw.val).val ∧
    CablePort A he (member i true) (if second then 2 else 0)
      ⟨DescentCableDonorNames.anchor (r).pick raw.val,raw.property⟩ 0 :=by
  intro second
  have id:=mouth_address (r).pick i m
  rw [←same] at id
  refine ⟨?_,id.2.symm,?_⟩
  · dsimp only [second]
    have h:=m.anchor.isLt
    by_cases bit:m.anchor.val=1 <;> simp [bit]; omega
  · by_cases b:m.anchor.val=1
    · have side:m.anchor=1:=Fin.ext b
      have dest:(⟨DescentCableDonorNames.anchor (r).pick raw.val,raw.property⟩:DescentSharedCableNames.Stage.Positive A)=member i false:=by
        apply Subtype.ext
        exact (id.1.trans (congrArg (fun t=>(r).pick (i,t)) side)).trans (picked_old A he i.1 i.2 false).symm
      rw [dest]
      simpa [second,b,newbornMember] using CablePort.sibling (A:=A) (he:=he) i.1 i.2
    · have side:m.anchor=0:=Fin.ext (by have:=m.anchor.isLt;change m.anchor.val=0;omega)
      have dest:(⟨DescentCableDonorNames.anchor (r).pick raw.val,raw.property⟩:DescentSharedCableNames.Stage.Positive A)=member i true:=by
        apply Subtype.ext
        exact (id.1.trans (congrArg (fun t=>(r).pick (i,t)) side)).trans (picked_old A he i.1 i.2 true).symm
      rw [dest]
      simpa [second,b] using CablePort.source (A:=A) (he:=he) (member i true)

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

namespace Hierarchy.DescentLocalArchiveOrder
open Computability.BorderVNP.Crossing DescentSixParty DescentSixParty.Chronology DescentStageEdgeReceipt
open DescentCompiler DescentKernelHistory DescentBundleHistory DescentHostDirectory DescentHostDegree
open DescentPackedOperand DescentNetworkPartition
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d p R : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
variable {u q ε : ℝ} {S : AtomSchedule} {k i z D z' D' wire hist : ℕ}
    {cap : Reached W G q ε S k i z D wire hist}
    {he : 0≤ε} {T : StageInput W G u ε} {c : (T.result he).Choice}
    {n : Normalize ((T.result he).state c)} {target : Reached n.result G q ε S k (i+1) z' D' wire hist}
    (ticket : OrdinaryLink cap he T c n target) (arch : Archive W)
    (hp : 0<p) (one : 1≤R) (pin : ∀x,p∣bits x) (sh : WorldShape p R arch.bit) (unit : p∣(T).z)
local notation "r" => BitDescription.scannedRows he T
local notation "uni" => fun _ : (r).pairs=>(T).z
local notation "room" => fun _ : (r).pairs=>le_refl (T).z
local notation "whole" => fun _ : (r).pairs=>unit
local notation "prof" => (r).profile c
local notation "after" => afterOrdinary hp one pin ticket arch sh unit
local notation "M" => rawGraph he T c
local notation "baseShape" => physicalShape W arch.bit G (r).pick uni room prof hp sh.sites sh.edges pin whole
local notation "next" => (ticket.advance arch).bit
local notation "names" => NodeOrder.physicalNames arch.bit G (r).pick uni room prof
local notation:max "source" x:arg => (names).symm (roots ticket arch x)

open DescentOrdinaryBorn DescentPackedOperand
attribute [local irreducible] sourceIndex roots BitDescription.scannedRows afterOrdinary
/-- In the original selected catalogue the same occurrence determines the
registered port edge, its flattened number, the short mouth, and the word
offset. This projection applies before both contractions. -/
theorem original_born_cable_source (x:NodeOrder.All next) (j:Fin ((((after).sites x.1).recipe hp).arity x.2))
    (i:(r).pairs) (party:Fin 6) (fresh:roots ticket arch x=.inr (i,party))
    (e:Incident (M) (source x).1) (piece:ℕ) (len:(piece+1)*p≤(M).width e.val)
    (read:((baseShape (source x).1).recipe hp).operand (source x).2
      (sourceIndex ticket arch hp one pin sh unit x j)=.inl ⟨.inl e,piece,len⟩) :
    ∃o:Occurrence W G (r).pick uni prof p i party,
      (occurrences W G (r).pick uni prof p i party)[j.val]?=some o ∧
      let m:=occurrenceMouth W G (r).pick uni prof o
      mouth (actual G p) (T).z (DescentPacking.PackedMatch.LayoutSum.profileCode G.C (prof i)).val party j.val=some m ∧
      e.val=edgeOf (r).pick i m.origin ∧ piece=m.chunk :=by
  let saved:=roots ticket arch x
  let slot:=sourceIndex ticket arch hp one pin sh unit x j
  have physical:cableAt W G (r).pick uni prof (source x).1
      (((baseShape (source x).1).recipe hp).operand (source x).2 slot)=some (e.val,piece):=
    congrArg (cableAt W G (r).pick uni prof (source x).1) read
  have index : slot.val = j.val := sourceIndex_val ticket arch hp one pin sh unit x j
  let claim (num : ℕ) : Prop :=
    ∃o:Occurrence W G (r).pick uni prof p i party,
      (occurrences W G (r).pick uni prof p i party)[num]?=some o ∧
      let m:=occurrenceMouth W G (r).pick uni prof o
      mouth (actual G p) (T).z (DescentPacking.PackedMatch.LayoutSum.profileCode G.C (prof i)).val party num=some m ∧
      e.val=edgeOf (r).pick i m.origin ∧ piece=m.chunk
  have chosen : claim slot.val := born_address W G (r).pick uni prof room hp arch.bit sh.sites sh.edges pin whole
    (r).fit saved i party fresh slot e.val piece physical
  exact Eq.mp (congrArg claim index) chosen

end
end Hierarchy.DescentLocalArchiveOrder

namespace Hierarchy.DescentLocalArchiveOrder
open Computability.BorderVNP.Crossing DescentSixParty DescentSixParty.Chronology DescentStageEdgeReceipt
open DescentCompiler DescentKernelHistory DescentBundleHistory DescentHostDirectory DescentHostDegree
open DescentPackedOperand DescentNetworkPartition
open scoped Classical
noncomputable section
set_option quotPrecheck false
section GenericBirth
open DescentOrdinaryBorn DescentPacking.PackedMatch.Local
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k : ℕ} {bits : P → ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {q ε : ℝ}
    (placement : GroupStage W G q ε J V k) (he : 0 ≤ ε) (c : (placement.stage.result he).Choice)
local notation "rows" => BitDescription.scannedRows he placement.stage
local notation "units" => fun _ : (rows).pairs => placement.stage.z
local notation "profile" => (rows).profile c
variable (p : ℕ) (i : (BitDescription.scannedRows he placement.stage).pairs) (party : Fin 6)
    (index piece : ℕ) (raw : DescentRawCablePanel.Live placement (BitDescription.scannedRows he placement.stage).pick)

private def stageBornRequest : Prop :=
    ∃ o : Occurrence W G (rows).pick units profile p i party,
      (occurrences W G (rows).pick units profile p i party)[index]? = some o ∧
      let m := occurrenceMouth W G (rows).pick units profile o
      let second := decide (m.anchor.val = 1)
      mouth (actual G p) placement.stage.z (DescentPacking.PackedMatch.LayoutSum.profileCode G.C (profile i)).val
        party index = some m ∧
      piece = m.chunk ∧ m.anchor.val = second.toNat ∧ m.rawRole = (DescentCableDonorNames.role raw.val).val ∧
      Stage.CablePort placement he
        (Hierarchy.DescentPacking.PackedMatch.Local.Stage.newbornMember placement he i true)
        (if second then 2 else 0) ⟨DescentCableDonorNames.anchor (rows).pick raw.val,raw.property⟩ 0

private theorem stageBornRequest_of_source
    (sourceRead : ∃ o : Occurrence W G (rows).pick units profile p i party,
      (occurrences W G (rows).pick units profile p i party)[index]? = some o ∧
      let m := occurrenceMouth W G (rows).pick units profile o
      mouth (actual G p) placement.stage.z (DescentPacking.PackedMatch.LayoutSum.profileCode G.C (profile i)).val
        party index = some m ∧ raw.val = edgeOf (rows).pick i m.origin ∧ piece = m.chunk) :
    stageBornRequest placement he c p i party index piece raw := by
  obtain ⟨o,found,live,edge,chunk⟩ := sourceRead
  exact ⟨o,found,live,chunk,Stage.newborn_port placement he i (occurrenceMouth W G (rows).pick units profile o) raw edge⟩
end GenericBirth

section RawWord
variable {F P J V I : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V] [Fintype I]
  {d k i p : ℕ} {bits : P → ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
  {q ε : ℝ}

private def rawLiveFromWord (A : GroupStage W G q ε J V k) (S : AtomSchedule) (ready : A.StateBounds S i)
    (pick : I × Fin 2 ↪ W.graph.Edge) (z : I → ℕ) (hz : ∀ j, 0 < z j)
    (fit : ∀ j side, W.graph.width (pick (j,side)) = z j * G.b) (prof : I → Profile G.C)
    (hp : 0 < p) (w : WireWord (GadgetNetwork.physical W.graph pick (branchWidth G z prof)) p) :
    DescentRawCablePanel.Live A pick :=
  ⟨w.1, DescentPrivateRawLabels.parent_positive A S ready pick z hz fit prof hp w⟩

variable {S : AtomSchedule} {a degree wire hist age : ℕ}
    (cap : Reached W G q ε S k age a degree wire hist) (he : 0 ≤ ε)
    (c : (cap.placement.stage.result he).Choice)

private def reachedRawFromIndex (hp : 0 < p) (e : (rawGraph he cap.placement.stage c).Edge)
    (piece : ℕ) (len : (piece+1)*p ≤ (rawGraph he cap.placement.stage c).width e) :
    DescentRawCablePanel.Live cap.placement (BitDescription.scannedRows he cap.placement.stage).pick :=
  let rows := BitDescription.scannedRows he cap.placement.stage
  rawLiveFromWord cap.placement S cap.valid rows.pick (fun _ => cap.placement.stage.z)
    (fun _ => cap.placement.stage.unitPos) rows.fit (rows.profile c) hp
    ⟨e, piece, (Nat.le_div_iff_mul_le hp).mpr len⟩

end RawWord

set_option quotPrecheck false
set_option backward.isDefEq.lazyProjDelta false
set_option backward.isDefEq.lazyWhnfCore false
variable {F P : Type} [Field F] {d p R : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
variable {u q ε : ℝ} {S : AtomSchedule} {k i z D z' D' wire hist : ℕ}
    {cap : Reached W G q ε S k i z D wire hist}
    {he : 0≤ε} {c : (cap.placement.stage.result he).Choice}
    {n : Normalize ((cap.placement.stage.result he).state c)} {target : Reached n.result G q ε S k (i+1) z' D' wire hist}
    (ticket : OrdinaryLink cap he cap.placement.stage c n target) (arch : Archive W)
    (hp : 0<p) (one : 1≤R) (pin : ∀x,p∣bits x) (sh : WorldShape p R arch.bit) (unit : p∣cap.placement.stage.z)
local notation "T" => cap.placement.stage
local notation "r" => BitDescription.scannedRows he T
local notation "uni" => fun _ : (r).pairs=>(T).z
local notation "room" => fun _ : (r).pairs=>le_refl (T).z
local notation "whole" => fun _ : (r).pairs=>unit
local notation "prof" => (r).profile c
local notation "after" => afterOrdinary hp one pin ticket arch sh unit
local notation "M" => rawGraph he T c
local notation "baseShape" => physicalShape W arch.bit G (r).pick uni room prof hp sh.sites sh.edges pin whole
local notation "next" => (ticket.advance arch).bit
local notation "names" => NodeOrder.physicalNames arch.bit G (r).pick uni room prof
local notation:max "source" x:arg => operandSource ticket arch x


open DescentOrdinaryBorn DescentPackedOperand DescentCableDonorNames DescentPacking.PackedMatch.Local
local notation "A" => cap.placement
attribute [local irreducible] sourceIndex roots BitDescription.scannedRows afterOrdinary GroupStage.stage StageInput.result
/-- The full typed birth request of the actual physical stage. The previous
cable is the first member of the original paid pair. Only the original
second mouth issues the sibling query. -/
theorem original_newborn_port (x:NodeOrder.All next) (j:Fin ((((after).sites x.1).recipe hp).arity x.2))
    (i:(r).pairs) (party:Fin 6) (fresh:roots ticket arch x=.inr (i,party))
    (e:Incident (M) (source x).1) (piece:ℕ) (len:(piece+1)*p≤(M).width e.val)
    (read:((baseShape (source x).1).recipe hp).operand (source x).2
      (sourceIndex ticket arch hp one pin sh unit x j)=.inl ⟨.inl e,piece,len⟩) :
    stageBornRequest cap.placement he c p i party j.val piece (reachedRawFromIndex cap he c hp e.val piece len) := by
  apply stageBornRequest_of_source
  exact original_born_cable_source
    (cap:=cap) (he:=he) («T»:=cap.placement.stage) (c:=c) (n:=n) (target:=target)
    ticket arch hp one pin sh unit x j i party fresh e piece len read

end
end Hierarchy.DescentLocalArchiveOrder

end OAI
