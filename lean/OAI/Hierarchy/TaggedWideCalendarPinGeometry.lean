import OAI.Hierarchy.TaggedWideCalendarRows
import OAI.Hierarchy.TaggedWideCalendarShelf
import OAI.Hierarchy.TaggedWideMountedControlFields
import OAI.Hierarchy.TaggedWideDatedLayout
import OAI.Hierarchy.TaggedWidePassiveGate
import OAI.Hierarchy.TaggedWideChordConsumer
import OAI.Hierarchy.TaggedWideTimeOccupancy

namespace OAI
/-! # Literal operand wires for the real dated role, packet and passive-control pages -/

noncomputable section
namespace Hierarchy.WireTelescope.PassMatrix
open ThreeFlat Routing
open LinearAlgebra.SpectralBooks ChordGraph
open Tagged Tagged.WideControlJoin Tagged.WideStack
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ProtocolRAM.Calendar WideCPU SiteControls
open scoped Classical BigOperators

variable {Ex Sel D : Type} [Fintype Ex] [Fintype Sel] [Fintype D] (G : Gate)
local notation "V" => SitePins Ex Sel D G
variable {T deg width : ℕ} (P : Dated T) (work : ℕ) (j : Fin T) (s : Fin P.sites)
local notation "Pin" => BinaryBarrelTurns.Pin (BinaryBarrelTurns.digits width) (BinaryBarrelTurns.digits width) width

def ballotAddress (f : ℕ) := P.ballotStart work j+1+s.val*(P.ballot j).columns+f
def controlAddress (f : SiteControls.Field deg) :=
  P.controlBase work j+1+s.val*(P.controlColumns j)+(fieldNumber deg f).val

def ballotWord (f bit : ℕ) : V⊕Bool := G.shelfBit (ballotAddress P work j s f,bit)
def controlWord (f : SiteControls.Field deg) (bit : ℕ) : V⊕Bool :=
  G.shelfBit (controlAddress P work j s f,bit)

omit [Fintype Ex] [Fintype Sel] [Fintype D] in
theorem controlWord_read (out : Memory G.W) (ext : Ex→Bool) (sel : Sel→Bool) (data : D→Bool)
    (dense : ∀i : Fin G.u,(G.addr i).val=i.val) (f : SiteControls.Field deg) (bit : ℕ)
    (inside : controlAddress P work j s f<G.u) :
    Sum.elim (Sum.elim ext (Sum.elim sel (Sum.elim data (G.terminal out)))) id
      (controlWord G P work j s f bit)=(out (controlAddress P work j s f)).val.testBit bit :=
  G.shelfBit_read dense out ext sel data _ _ inside

omit [Fintype Ex] [Fintype Sel] [Fintype D] in
theorem ballotWord_read (out : Memory G.W) (ext : Ex→Bool) (sel : Sel→Bool) (data : D→Bool)
    (dense : ∀i : Fin G.u,(G.addr i).val=i.val) (f bit : ℕ) (inside : ballotAddress P work j s f<G.u) :
    Sum.elim (Sum.elim ext (Sum.elim sel (Sum.elim data (G.terminal out)))) id
      (ballotWord G P work j s f bit)=(out (ballotAddress P work j s f)).val.testBit bit :=
  G.shelfBit_read dense out ext sel data _ _ inside

/-- Three physical field words control each pair of passive streams. Its
two data slices are the preceding and successor time words themselves. -/
def passivePins (words : Bool→Fin deg→Fin width→V⊕Bool) (pair : Fin deg×Fin deg) : Pin→V⊕Bool
  | .inl b=>controlWord G P work j s (.inr (pair,0)) b.val
  | .inr (side,.inl b)=>controlWord G P work j s (.inr (pair,if side then 2 else 1)) b.val
  | .inr (side,.inr b)=>words side (if side then pair.2 else pair.1) b

def passiveNet {F : Type} [Field F] (words : Bool→Fin deg→Fin width→V⊕Bool) :=
  PassiveWindow.circuit (F:=F) (passivePins G P work j s words)

theorem passiveNet_cost {F : Type} [Field F] (words : Bool→Fin deg→Fin width→V⊕Bool) :
    let b:=passiveNet (F:=F) G P work j s words
    b.cells+b.internal≤deg*deg*(2308*width*(width.log2+2)) := by
  simpa only [passiveNet,Fintype.card_fin] using
    PassiveWindow.cost (F:=F) (passivePins G P work j s words)

omit [Fintype Ex] [Fintype Sel] [Fintype D] in
/-- The interval source, interval target and size all come from the same
sparse pair in the real control page; there is one wire per native bit. -/
theorem passivePins_read (out : Memory G.W) (ext : Ex→Bool) (sel : Sel→Bool) (data : D→Bool)
    (dense : ∀i : Fin G.u,(G.addr i).val=i.val)
    (inside : ∀f : SiteControls.Field deg,controlAddress P work j s f<G.u)
    (words : Bool→Fin deg→Fin width→V⊕Bool) (pair : Fin deg×Fin deg) :
    let v:=Sum.elim ext (Sum.elim sel (Sum.elim data (G.terminal out)))
    let value:=(fun f : Fin 3=>(out (controlAddress P work j s (.inr (pair,f)))).val)
    Sum.elim v id ∘ passivePins G P work j s words pair=
      BinaryBarrelTurns.pins (fun b=>(value 0).testBit b.val)
        (fun side b=>(value (if side then 2 else 1)).testBit b.val)
        (fun side b=>Sum.elim v id (words side (if side then pair.2 else pair.1) b)) := by
  intro v value
  funext pin
  rcases pin with b|⟨side,b|b⟩
  · exact controlWord_read G P work j s out ext sel data dense _ _ (inside _)
  · exact controlWord_read G P work j s out ext sel data dense _ _ (inside _)
  · rfl

/-- The gather cut uses a real dated role word on one side and a locally
bound, padded packed word on the other. Before/after are independent gathers. -/
def gatherPins (side : Bool) (words : Fin deg→Fin width→V⊕Bool)
    (pair : Fin deg×Fin deg) : Pin→(V⊕(Fin deg×Fin width))⊕Bool
  | .inl b=>Sum.map Sum.inl id (controlWord G P work j s (.inl (side,.inl (pair.1,pair.2))) b.val)
  | .inr (target,.inl b)=>Sum.map Sum.inl id (controlWord G P work j s (.inl (side,.inr (.inl (pair.1,target)))) b.val)
  | .inr (false,.inr b)=>Sum.map Sum.inl id (words pair.1 b)
  | .inr (true,.inr b)=>.inl (.inr (pair.2,b))

def gatheredSize (side : Bool) (q : Fin deg) (b : Fin (BinaryBarrelTurns.digits width)) : V⊕Bool :=
  controlWord G P work j s (.inl (side,.inr (.inr q))) b.val

end Hierarchy.WireTelescope.PassMatrix

namespace Hierarchy.Tagged.WideStack
open ProtocolRAM.Calendar WireTelescope.CalendarTape
open scoped Classical

/-- A missing local role, or a digit beyond its own physical word, is a
constant. All admissible cells go to the common chronological data plane. -/
def datedRole {R D : Type} [Fintype R] {sites degree : ℕ} (es : List Event) (cap : R→ℕ)
    (slots : R ↪ Fin (sites*degree)) (wire : Fin ((es.length+1)*Fintype.card ((r:R)×Fin (cap r)))→D)
    (j : Fin es.length) (s : Fin sites) (side : Bool) (q : Fin degree) (bit : ℕ) : D⊕Bool :=
  if live : finProdFinEquiv (s,q)∈Set.range slots then
    let r:=Classical.choose live
    if ok:bit<cap r then .inl (wire (timeOrder es (if side then j.succ else j.castSucc,⟨r,bit,ok⟩)))
    else .inr false
  else .inr false

theorem datedRole_at {R D : Type} [Fintype R] {sites degree : ℕ} (es : List Event) (cap : R→ℕ)
    (slots : R ↪ Fin (sites*degree)) (wire : Fin ((es.length+1)*Fintype.card ((r:R)×Fin (cap r)))→D)
    (j : Fin es.length) (s : Fin sites) (side : Bool) (q : Fin degree) (r : R)
    (atSlot : slots r=finProdFinEquiv (s,q)) (bit : Fin (cap r)) :
    datedRole es cap slots wire j s side q bit.val=
      .inl (wire (timeOrder es (if side then j.succ else j.castSucc,⟨r,bit⟩))) := by
  have live : finProdFinEquiv (s,q)∈Set.range slots:=⟨r,atSlot⟩
  have hit : Classical.choose live=r :=slots.injective ((Classical.choose_spec live).trans atSlot.symm)
  subst r
  simp only [datedRole, dite_eq_left live, dite_eq_left bit.isLt]

end Hierarchy.Tagged.WideStack

namespace Hierarchy.WireTelescope.PassMatrix
open ThreeFlat Routing LinearAlgebra.SpectralBooks ChordGraph
open Tagged Tagged.WideControlJoin Tagged.WideStack Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ProtocolRAM.Calendar WideCPU
open scoped Classical BigOperators
variable {F Ex Sel D : Type} [Field F] [Fintype Ex] [Fintype Sel] [Fintype D] (G : Gate)
local notation "V" => SitePins Ex Sel D G
variable {T deg width bits : ℕ} (P : Dated T) (work : ℕ) (j : Fin T) (s : Fin P.sites)
local notation "Pin" => BinaryBarrelTurns.Pin (BinaryBarrelTurns.digits width) (BinaryBarrelTurns.digits width) width
local notation "HS" => Fin deg×Fin width

/-- Actual dynamic chord gather and its zero extension, closing the hidden
packed word around the finite party consumer. -/
def gatherProgram (side : Bool) (words : Fin deg→Fin width→V⊕Bool)
    (bitRoom : bits≤G.W+1)
    (inside : ∀q:Fin deg,controlAddress P work j s (.inl (side,.inr (.inr q)))<G.u)
    (consumer : BitNetwork F (Fintype.card (V⊕HS))) : BitNetwork F (Fintype.card V) :=
  ChordAperture.attach (gatherPins G P work j s side words)
    (fun q b=>.inr (.inr (.inr (⟨_,inside q⟩,b.castLE bitRoom)))) consumer

/-- The finite menu tag is the first word at precisely this dated ballot row. -/
def dateMode {digits : ℕ} (inside : ballotAddress P work j s 0<G.u) (widthOK : digits≤G.W+1)
    (b : Fin digits) : V := .inr (.inr (.inr (⟨_,inside⟩,b.castLE widthOK)))

omit [Fintype Ex] [Fintype Sel] [Fintype D] in
theorem dateMode_read {digits : ℕ} (inside : ballotAddress P work j s 0<G.u) (widthOK : digits≤G.W+1)
    (out : Memory G.W) (ext : Ex→Bool) (sel : Sel→Bool) (data : D→Bool) (b : Fin digits)
    (dense : ∀i : Fin G.u,(G.addr i).val=i.val) :
    Sum.elim ext (Sum.elim sel (Sum.elim data (G.terminal out))) (dateMode G P work j s inside widthOK b)=
      (out (ballotAddress P work j s 0)).val.testBit b.val := by
  change (out (G.addr ⟨ballotAddress P work j s 0,inside⟩).val).val.testBit b.val=_
  rw [dense]

def datedProgram {formats digits : ℕ} (fit : formats+1≤2^digits)
    (words : Bool→Fin deg→Fin width→V⊕Bool) (inside : ballotAddress P work j s 0<G.u)
    (widthOK : digits≤G.W+1) (packet : Fin formats→BitNetwork F (Fintype.card V)) :=
  dated (passiveNet (F:=F) G P work j s words) packet
    (dateMode (Ex:=Ex) (Sel:=Sel) (D:=D) G P work j s inside widthOK) fit

theorem datedProgram_bill {formats digits : ℕ} (fit : formats+1≤2^digits)
    (words : Bool→Fin deg→Fin width→V⊕Bool) (inside : ballotAddress P work j s 0<G.u)
    (widthOK : digits≤G.W+1) (packet : Fin formats→BitNetwork F (Fintype.card V)) :
    let net:=datedProgram G P work j s fit words inside widthOK packet
    net.cells+net.internal≤deg*deg*(2308*width*(width.log2+2))+
      177^digits*∑t : Fin formats,((packet t).cells+(packet t).internal) := by
  intro net
  let carry:=passiveNet (F:=F) G P work j s words
  have fee:=site_fee carry (Fin.cases (idleNet (F:=F) («V»:=V)) packet)
    (dateMode (Ex:=Ex) (Sel:=Sel) (D:=D) G P work j s inside widthOK) (ProtocolRAM.SiteScatter.tag fit)
  have zero : (idleNet (F:=F) («V»:=V)).cells+(idleNet (F:=F) («V»:=V)).internal=0 := by
    rw [idleNet,WideHost.localFamily_size]
    simp
  rw [Fin.sum_univ_succ] at fee
  have first:=passiveNet_cost (F:=F) G P work j s words
  apply fee.trans
  simpa only [Fin.cases_zero,Fin.cases_succ,zero,zero_add] using Nat.add_le_add_right first _


end Hierarchy.WireTelescope.PassMatrix

end
end OAI
