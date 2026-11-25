import OAI.Hierarchy.DescentFallbackOperandBranch
import OAI.Hierarchy.DescentRotorPublicOperand
import OAI.Hierarchy.DescentRotorWindowArchive
import OAI.Hierarchy.DescentRotorOperandRanks

namespace OAI
/-! # Joint public-tap and exceptional-tree gate operand lookup -/
namespace Hierarchy.DescentResetPublicOperandBook
open DescentSIMDLookup DescentPacking.PackedMatch.Local DescentFallbackOperandQuery DescentFallbackItemSelect
open DescentFallbackOperandBranch DescentDenseHostOrder DescentResetLocalRoster DescentHostDirectory
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM DescriptorExpr
open scoped Classical Fin.CommRing
noncomputable section

structure Config extends oldConfig : DescentFallbackOperandBranch.Config where
  packetWidth : ℕ
  gain : ℕ
  multiplicity : ℕ
  grain : ℕ

namespace Config
variable {n h : ℕ} (board : NonlinearExpanders.Graph n h) (C : Config)
local notation "F" => C.oldConfig
local notation "Y" => (2^n : ℕ)
local notation "K" => C.oldConfig.count
abbrev Extra := (Fin C.donors×Fin C.donors) ⊕ (Fin C.oldDegree×(Fin C.oldDegree×Fin 6))
def extraCount :=C.donors*C.donors+C.oldDegree*(C.oldDegree*6)
def extraId : C.Extra≃Fin C.extraCount :=
  (Equiv.sumCongr finProdFinEquiv ((Equiv.prodCongr (Equiv.refl _) finProdFinEquiv).trans finProdFinEquiv)).trans finSumFinEquiv
def inputs (n : ℕ) :=(F).inputs n+C.extraCount
abbrev Data (n : ℕ) :=Fin (C.inputs n)→Cell C.fieldBits
def basic (x : C.Data n) : (F).Data n :=fun i=>x (Fin.castAdd _ i)
def extra (x : C.Data n) (e : C.Extra) :=x (Fin.natAdd ((F).inputs n) (C.extraId e))

def rotor : DescentRotorOperandQueryROM.Shape where
  depth:=C.maxDepth
  packet:=C.packetWidth
  gain:=C.gain
  batches:=C.batches
  residual:=C.residual
  addresses:=C.nodes
  fieldBits:=C.fieldBits
  queryBits:=C.queryBits
  lanes:=C.lanes

def oldData (x : C.Data n) : DescentRotorWindowArchive.RowData C.oldDegree C.donors C.oldCap C.fieldBits
  | .inl (.inl i)=>(F).packet (C.basic x) (.inl i)
  | .inl (.inr i)=>(F).packet (C.basic x) (.inr (.inl i))
  | .inr e=>C.extra x e

def reg (x : C.Data n) : Fin 4→Cell C.fieldBits :=
  ![(F).header (C.basic x) 1,(F).header (C.basic x) 4,(F).header (C.basic x) 5,(F).header (C.basic x) 2]

def endpoints (s : Bool) (root : code C.residual) (x : C.Data n) (j : Fin K) :
    Option (Fin Y×Fin Y) :=
  let k:=DescentRotorWindowArchive.pairCode (n:=n) (r:=C.residual) s root.val (C.oldData x) (finProdFinEquiv.symm j)
  if known : ∃p : Fin Y×Fin Y,DescentPackedRotorMatrix.pair p.1 p.2=k then some known.choose else none

theorem endpoints_read (s : Bool) (root : code C.residual) (x : C.Data n) (j : Fin K) (a b : Fin Y)
    (got : DescentRotorWindowArchive.pairCode (n:=n) (r:=C.residual) s root.val (C.oldData x)
      (finProdFinEquiv.symm j)=DescentPackedRotorMatrix.pair a b) :
    C.endpoints s root x j=some (a,b) := by
  have existsPair : ∃p:Fin Y×Fin Y,DescentPackedRotorMatrix.pair p.1 p.2=
      DescentRotorWindowArchive.pairCode (n:=n) (r:=C.residual) s root.val (C.oldData x) (finProdFinEquiv.symm j):=⟨(a,b),got.symm⟩
  have values:=(DescentPackedRotorMatrix.pair_inj _ _ _ _).mp (existsPair.choose_spec.trans got)
  unfold endpoints
  rw [dite_eq_left existsPair]
  exact congrArg some (Prod.ext values.1 values.2)

def oldItem (x : C.Data n) (s : Bool) (j : Fin K) : Item :=
  let basic:=C.basic x
  let loc:=finProdFinEquiv.symm j
  let old:=(F).packet basic
  let raw:=old (.inr (.inl loc))
  let key:=DescentMeasuredOperandKey.key C.oldDegree C.oldCap C.fineBits s raw ((F).header basic 3)
    ((F).digit basic j 0) ((F).digit basic j 1)
  ⟨none,key,loc.1.val,loc.2.val,s,0⟩

theorem oldItem_key (x : C.Data n) (s : Bool) (j : Fin K) :
    (C.oldItem x s j).key=DescentMeasuredOperandKey.key C.oldDegree C.oldCap C.fineBits s
      ((F).packet (C.basic x) (.inr (.inl (finProdFinEquiv.symm j)))) ((F).header (C.basic x) 3)
      ((F).digit (C.basic x) j 0) ((F).digit (C.basic x) j 1) := rfl

def portRows (x : C.Data n) (s : Bool) (root : code C.residual)
    (a : DescentRotorOperandQueryROM.Shape.Mouth n) :=
  DescentRotorOperandRanks.rows (C.endpoints s root x) (fun p=>(if a.pin then p.2 else p.1)=a.vertex)

def traffic (x : C.Data n) (s : Bool) (root : code C.residual) :=
  DescentPackedResetRotorRoles.matrix n (DescentPackedRotorMatrix.bins K)
    (DescentRotorWindowArchive.matrix C.residual n s root.val (C.oldData x))

def accepts (x : C.Data n) (s : Bool) (root : code C.residual)
    (a : DescentRotorOperandQueryROM.Shape.Mouth n) (j : Fin K) : Bool :=
  let ends:=C.endpoints s root x
  (ends j).any fun p=>
    let same:=DescentRotorOperandRanks.rows ends (·=p)
    let slot:=rank (C.oldItem x s) same j
    let levels:=DescentRecordedRotorLayers.layers n C.packetWidth C.gain ((C.reg x) 0).val
    decide (DescentRotorOperandQueryROM.Shape.railMatch C.packetWidth levels (C.traffic x s root) a p.1 p.2 slot)

def carrier (x : C.Data n) (s : Bool) (root : code C.residual)
    (a : DescentRotorOperandQueryROM.Shape.Mouth n) : Option (Fin K) :=
  if hit : ∃j,C.accepts x s root a j=true then some hit.choose else none

def tap (x : C.Data n) (s : Bool) (root : code C.residual)
    (a : DescentRotorOperandQueryROM.Shape.Mouth n) : Option (ℕ×ℕ×ℕ×Bool) := do
    let ids:=C.oldItem x s
    let ports:=C.portRows x s root a
    let j←C.carrier x s root a
    let first:=rank ids ports j*C.batches+a.batch
    let num:=min 2 (ports.card*C.batches-first)
    if a.within≥num then none else
      let word:=first+a.within
      let cap:=((C.reg x) 0).val
      if a.pin then
        let rootIdVal:=(rootId C.residual Y (.inl root)).val
        let pos:=stemSlots (F).toShape cap+1+
          ((finTwoEquiv.symm s).val*(rootSlots C.residual Y*sockets (F).toShape)+rootIdVal*sockets (F).toShape+a.vertex.val)
        return (directed (total (F).toShape cap) s pos,word,num,true)
      else
        let prior←select ids ports (word/C.batches)
        return ((F).stemAt s cap (ids prior),word%C.batches,num,false)

def mixed (node arg : ℕ) (x : C.Data n) : Option (ℕ×ℕ×ℕ×Bool) :=
  if ((F).header (C.basic x) 0).val=0 then none else
  match C.rotor.public_selector board C.multiplicity C.grain node arg (C.reg x) with
  | some (s,root,req)=>C.tap x s root req
  | none=>(F).mixed board node arg (C.basic x)

def column (b : ℕ) (field : Option (Fin 7)) (j : Fin (F).mouths) (x : C.Data n) : Cell b :=
  let p:=finProdFinEquiv.symm j
  match C.mixed board p.2.val p.1.val x with
  | none=>0
  | some (q,word,count,mark)=>match field with
    | none=>(q:ℕ)
    | some i=>(![0,0,if mark then word/C.split else 0,if mark then word%C.split else word,0,1,count] i:ℕ)

def law (b : ℕ) («fields» : Bool) (q : Fin ((if «fields» then 7 else 1)*(F).mouths)) (x : C.Data n) : Cell b :=
  let j:=finProdFinEquiv.symm q
  if ok : «fields»=true ∧ j.1.val<7 then C.column board b (some ⟨j.1.val,ok.2⟩) j.2 x
  else C.column board b none j.2 x
theorem empty (b : ℕ) («fields» : Bool) (j) : C.law board b «fields» j (fun _=>0)=0 := by
  simp [law,column,mixed,DescentFallbackOperandBranch.Config.header,basic]

def program (b : ℕ) («fields» : Bool) (base w : ℕ) :=
  DescentOperandFamilyBook.program (C.law board b «fields») C.lanes base w
def endAddress («fields» : Bool) (base : ℕ) :=
  DescentOperandFamilyBook.endAddress ((if «fields» then 7 else 1)*(F).mouths) (C.inputs n) C.fieldBits C.lanes base
def ticks («fields» : Bool) :=
  DescentOperandFamilyBook.ticks ((if «fields» then 7 else 1)*(F).mouths) (C.inputs n) C.fieldBits C.lanes
def expr (b : ℕ) («fields» : Bool) (base : ℕ) (q : Fin ((if «fields» then 7 else 1)*(F).mouths)) (src : Fin (C.inputs n)→Expr) :=
  DescentOperandFamilyBook.expr (C.law board b «fields») C.lanes base q src
abbrev any {w : ℕ} (b : ℕ) («fields» : Bool) (base : ℕ) (m : Memory w) (room : C.endAddress (n:=n) «fields» base<2^w) :=
  DescentOperandFamilyBook.any (C.law board b «fields») C.lanes base m room
abbrev issued {H G w : ℕ} (b : ℕ) («fields» : Bool) (base : ℕ) (q : Fin ((if «fields» then 7 else 1)*(F).mouths))
    (src : Fin (C.inputs n)→Expr) (m : Memory w) (x : Fin H→Fin G→C.Data n)
    (fits : ∀i,(src i).Fits w base) (reads : ∀i,DescentPackedZip.Source (src i) (fun v g=>x v g i) C.lanes m)
    (room : C.endAddress (n:=n) «fields» base<2^w) :=
  DescentOperandFamilyBook.issued (C.law board b «fields») (C.empty board b «fields») C.lanes base q src m x fits reads room
end Config
end
end Hierarchy.DescentResetPublicOperandBook

end OAI
