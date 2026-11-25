import OAI.Hierarchy.DescentFallbackOperandRead
import OAI.Hierarchy.DescentFallbackItemSelect
import OAI.Hierarchy.DescentFallbackMeasuredWindow
import OAI.Hierarchy.DescentResetTrunkPalette
import OAI.Hierarchy.DescentMeasuredOperandKey
import OAI.Hierarchy.DescentContactReceiver

namespace OAI
/-! # Mixed receiver and flattened operand selection from the old signed fallback packet -/
namespace Hierarchy.DescentFallbackOperandBranch
open DescentSIMDLookup DescentPacking.PackedMatch.Local DescentFallbackItemSelect DescentFallbackOperandQuery
open DescentDenseHostOrder DescentHostDirectory DescentResetLocalRoster DescentTreePrefixIntervals
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM DescriptorExpr
open scoped Classical Fin.CommRing
noncomputable section

structure Config extends DescentFallbackOperandQuery.Shape where
  oldDegree : ℕ
  oldCap : ℕ
  donors : ℕ
  fineBits : ℕ
  batches : ℕ
  split : ℕ
  nodes : ℕ
  args : ℕ

namespace Config
variable {n h : ℕ} (board : NonlinearExpanders.Graph n h) (C : Config)
def count:=C.donors*(2*C.oldCap)
def inputs (n : ℕ) :=8+12*C.count+DescentFallbackPeriod.inputCount C.oldDegree C.donors C.oldCap n C.residual
def mouths:=C.args*C.nodes
abbrev Data (n : ℕ) := Fin (C.inputs n)→Cell C.fieldBits
local notation "xF" => Cell C.fieldBits
local notation "K" => C.count
local notation "Y" => 2^n

def ports (n : ℕ) :
    (Fin 8⊕(Fin 12×Fin K))⊕DescentFallbackPeriod.Input C.oldDegree C.donors C.oldCap n C.residual ≃ Fin (C.inputs n) :=
  (Equiv.sumCongr ((Equiv.sumCongr (Equiv.refl _) finProdFinEquiv).trans finSumFinEquiv)
    DescentFallbackPeriod.number).trans finSumFinEquiv

def header (x : C.Data n) (i : Fin 8) :=x (C.ports n (.inl (.inl i)))
def digit (x : C.Data n) (j : Fin K) (i : Fin 12) :=x (C.ports n (.inl (.inr (i,j))))
def packet (x : C.Data n) : DescentFallbackPeriod.Packet C.oldDegree C.donors C.oldCap n C.residual C.fieldBits :=
  fun i=>x (C.ports n (.inr i))

/-- Public shape, old item and face are all per-row data. The same installed code
    consequently evaluates different gate depths on different packed hosts. -/
def rowsAt (x : C.Data n) (side : Bool) (root : code C.residual×Option (Fin Y))
    (rootAddr : Fin (DescentFallbackShapeTable.rows C.residual Y)) (total : ℕ) (j : Fin K) : Item :=
  let ij:=finProdFinEquiv.symm j
  let p:=C.packet x
  let z:=DescentPackedLeafSelector.pick C.maxDepth total
    (DescentFallbackPeriod.sourceCell p side root rootAddr ij.1 ij.2)
  let raw:=p (.inr (.inl ij))
  let key:=DescentMeasuredOperandKey.key C.oldDegree C.oldCap C.fineBits side raw (C.header x 3)
    (C.digit x j 0) (C.digit x j 1)
  ⟨z.map Fin.val,key,ij.1.val,ij.2.val,side,0⟩

theorem rowsAt_key (x : C.Data n) (side : Bool) (root : code C.residual×Option (Fin Y))
    (address : Fin (DescentFallbackShapeTable.rows C.residual Y)) (total : ℕ) (j : Fin K) :
    (C.rowsAt x side root address total j).key = DescentMeasuredOperandKey.key C.oldDegree C.oldCap
      C.fineBits side (C.packet x (.inr (.inl (finProdFinEquiv.symm j)))) (C.header x 3)
      (C.digit x j 0) (C.digit x j 1) := rfl

/-- A socket port can aggregate multiple old stems. The second conservative p-word of
    a flat lane may name the next stem. Select its owner in the same old socket. -/
def stemAt (s : Bool) (cap : ℕ) (it : Item) : ℕ :=
  directed (total C.toShape cap) true ((finTwoEquiv.symm s).val*(2^C.residual*(2*cap))+
    it.residual*(2*cap)+it.signed)

def childPath (H : ℕ) (ds : List Bool) (l : ℕ) :=
  ds++[decide ((l/2^(H-(ds.length+1)))%2=1)]

def treeAt {n : ℕ} (s face : Bool) (cap treeHeight d leaf : ℕ)
    (root : code C.residual×Option (Fin (2^n))) :=
  directed (total C.toShape cap) face (stemSlots C.toShape cap+1+contactSlots C.toShape+
    ((finTwoEquiv.symm s).val*(rootSlots C.residual (2^n)*C.privateSlots)+
      (rootId C.residual (2^n) (.inr root)).val*C.privateSlots+
      pathRank treeHeight d (leaf/2^(C.maxDepth-treeHeight))))

def contactAt {n : ℕ} (s : Bool) (cap treeHeight leaf : ℕ)
    (root : code C.residual×Option (Fin (2^n))) :=
  directed (total C.toShape cap) s (stemSlots C.toShape cap+1+
    ((finTwoEquiv.symm s).val*(rootSlots C.residual (2^n)*sockets C.toShape)+
      (rootId C.residual (2^n) (.inr root)).val*sockets C.toShape+
      (2^n+DescentContactReceiver.treeSlot C.maxDepth treeHeight leaf)))

def startWord (items : Fin K→Item) (live : Finset (Fin K)) (j : Fin K) (node : ℕ) :=
  rank items live j*C.batches+node%C.batches

def visibleWords (items : Fin K→Item) (live : Finset (Fin K)) (j : Fin K) (node : ℕ) :=
  min 2 (live.card*C.batches-C.startWord items live j node)

def make (s : Bool) (cap treeHeight : ℕ) (ds : List Bool) (root : code C.residual×Option (Fin Y))
    (items : Fin K→Item) (node arg : ℕ) : Option (ℕ×ℕ×ℕ×Bool) := do
  let cell:=rows C.maxDepth ds items
  let j←select items cell (node/C.batches)
  let l←(items j).leaf
  let inputWord:=C.startWord items cell j node
  let incoming:=C.visibleWords items cell j node
  if arg< incoming then
    if ds.isEmpty then
      let item←select items cell ((inputWord+arg)/C.batches)
      return (C.stemAt s cap (items item),(inputWord+arg)%C.batches,incoming,false)
    else return (C.treeAt s true cap treeHeight (ds.length-1) l root,inputWord+arg,incoming,true)
  else
    let terminal:=ds.length=treeHeight
    let next:=if terminal then cell else rows C.maxDepth (childPath C.maxDepth ds l) items
    let outWord:=C.startWord items next j node
    let outgoing:=C.visibleWords items next j node
    let step:=arg-incoming
    if step≥outgoing then none else
      let target:=if terminal then C.contactAt s cap treeHeight l root
        else C.treeAt s false cap treeHeight ds.length l root
      return (target,outWord+step,outgoing,true)

/-- A relay's retained predecessor grain has the same birth key as the source
of its incoming stem. The owner and the signed face come from the original
packet at this receiver. -/
def relayItems (x : C.Data n) (j : Fin K) : Item :=
  let loc : Fin C.donors×Fin (2*C.oldCap):=finProdFinEquiv.symm j
  let raw:=C.packet x (.inr (.inl loc))
  let key:=DescentMeasuredOperandKey.key C.oldDegree C.oldCap C.fineBits true raw
    (C.header x 3) (C.digit x j 0) (C.digit x j 1)
  ⟨none,key,loc.1.val,loc.2.val,true,0⟩

def relayRows (x : C.Data n) (target : DescentContacts.Endpoint (2^n)) : Finset (Fin K) :=
  Finset.univ.filter fun j=>
    let loc : Fin C.donors×Fin (2*C.oldCap):=finProdFinEquiv.symm j
    DescentFallbackPeriod.localWord (C.packet x) loc.1/2=DescentFallbackShapeTable.cell C.residual target ∧
      ((DescentFallbackPeriod.signed (C.packet x) loc.1 loc.2).map fun ch=>ch.target)=some true

/-- The first row of a relay argument reads the accumulated trunk at its
incoming rank. The second row reads the original stem at its own subword. -/
def relay (x : C.Data n) (target : DescentContacts.Endpoint (2^n)) (node arg : ℕ) :
    Option (ℕ×ℕ×ℕ×Bool) :=
  if arg<2*C.batches then do
    let j←select (C.relayItems x) (C.relayRows x target) node
    let cap:=(C.header x 1).val
    let slots:=stemSlots C.toShape cap
    let all:=total C.toShape cap
    if arg<C.batches then
      return (directed all true slots,node*C.batches+arg,1,target.2.isSome)
    else
      return (directed all false (2^C.residual*(2*cap)+j.val),arg-C.batches,1,false)
  else none

def mixed (node arg : ℕ) (x : C.Data n) : Option (ℕ×ℕ×ℕ×Bool) := do
  if (C.header x 0).val=0 then none else
    let shapeNo:=(C.header x 2).val
    if ok : shapeNo<(roster board C.residual C.maxDepth).card then
      match ((DescentResetTrunkPalette.order board C.residual C.maxDepth).symm ⟨shapeNo,ok⟩).val with
      | .fall s z ds=>
        if legal : z.2.1∈codes C.residual then
          let root:=(⟨z.2.1,legal⟩,z.2.2)
          let id:=DescentFallbackPeriod.rootCell C.residual n root
          if live : id<DescentFallbackShapeTable.rows C.residual Y then
            let v:=(⟨id,live⟩ : Fin (DescentFallbackShapeTable.rows C.residual Y))
            let amount:=DescentFallbackPeriod.score (C.packet x) (v,0,v)
            C.make s (C.header x 1).val (min C.maxDepth (Nat.clog 2 amount)) ds root (C.rowsAt x s root v amount) node arg
          else none
        else none
      | .trunk true (_,target)=>C.relay x target node arg
      | _=>none
    else none

def column (b : ℕ) (field : Option (Fin 7)) (j : Fin C.mouths) (x : C.Data n) : Cell b :=
  let (a,node):=finProdFinEquiv.symm j
  match C.mixed board node.val a.val x with
  | none=>0
  | some (query,word,count,marked)=>match field with
    | none=>(query:ℕ)
    | some f=>(![0,0,if marked then word/C.split else 0,if marked then word%C.split else word,0,1,count] f:ℕ)

def family (b : ℕ) («fields» : Bool) :
    Fin ((if «fields» then 7 else 1)*C.mouths)→C.Data n→Cell b :=fun q=>
  let j:=finProdFinEquiv.symm q
  if h : j.1.val<7 ∧ «fields»=true then C.column board b (some ⟨j.1.val,h.1⟩) j.2
  else C.column board b none j.2

theorem dead (b : ℕ) («fields» : Bool) (j) : C.family board b «fields» j (fun _=>0)=0 := by
  unfold family
  split <;> simp [column,mixed,header]

def program (b : ℕ) («fields» : Bool) (base w : ℕ) :=
  DescentOperandFamilyBook.program (C.family board b «fields») C.lanes base w
def endAddress («fields» : Bool) (base : ℕ) :=
  DescentOperandFamilyBook.endAddress ((if «fields» then 7 else 1)*C.mouths) (C.inputs n) C.fieldBits C.lanes base
def ticks («fields» : Bool) :=
  DescentOperandFamilyBook.ticks ((if «fields» then 7 else 1)*C.mouths) (C.inputs n) C.fieldBits C.lanes
def expr (b : ℕ) («fields» : Bool) (base : ℕ) (j : Fin ((if «fields» then 7 else 1)*C.mouths))
    (src : Fin (C.inputs n)→Expr) := DescentOperandFamilyBook.expr (C.family board b «fields») C.lanes base j src
abbrev any {w : ℕ} (b : ℕ) («fields» : Bool) (base : ℕ) (m : Memory w) (room : C.endAddress (n:=n) «fields» base<2^w) :=
  DescentOperandFamilyBook.any (C.family board b «fields») C.lanes base m room
abbrev issued {H G w : ℕ} (b : ℕ) («fields» : Bool) (base : ℕ) (j : Fin ((if «fields» then 7 else 1)*C.mouths))
    (src : Fin (C.inputs n)→Expr) (m : Memory w) (x : Fin H→Fin G→C.Data n)
    (fits : ∀i,(src i).Fits w base) (reads : ∀i,DescentPackedZip.Source (src i) (fun v g=>x v g i) C.lanes m)
    (room : C.endAddress (n:=n) «fields» base<2^w) :=
  DescentOperandFamilyBook.issued (C.family board b «fields») (C.dead board b «fields») C.lanes base j src m x fits reads room
end Config
end
end Hierarchy.DescentFallbackOperandBranch

end OAI
