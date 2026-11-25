import OAI.Hierarchy.DescentOrdinaryOriginReturn
import OAI.Hierarchy.DescentPackedPorts

namespace OAI
/-! # Read the earlier path, block, node or birth party at a genuine successor job -/
namespace Hierarchy.DescentOrdinaryOriginPorts
open DescentOrdinaryOriginMask DescentPackedActorMask DescentHaloWalkRAM DescentPackedColony DescentPackedZip
open DescentSIMDLookup DescentOrdinaryAtomFieldRAM DescentPacking.PackedMatch.Local
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section

variable (R : Return)
abbrev extent :=nodes (breadth R.degree*2^R.depth) R.oldNodes R.capacity

/-- Field order is tag, prior path, prior block, prior node, outgoing seat, party.
Tags zero, one and two denote padding, a carried node and a birth. -/
def tuple (j : Fin (extent R)) : Fin 6→ℕ :=
  let p:=(bookRoot R.degree R.depth R.oldNodes R.capacity j).val
  let x:=(bookBlock R.degree R.depth R.oldNodes R.capacity j).val
  let z:=bookItem R.degree R.depth R.oldNodes R.capacity j
  match finSumFinEquiv.symm z with
  | .inl n=>![1,p,x,n.val,0,0]
  | .inr a=>
    let a':Fin R.capacity×Fin 6:=finProdFinEquiv.symm a
    ![2,p,x,0,a'.1.val,a'.2.val]

def candidate (path : Fin (breadth R.degree)) (x : Fin (2^R.depth))
    (i : Fin R.oldNodes ⊕ (Fin R.capacity×Fin 6)) : Fin (extent R) :=
  finProdFinEquiv (finProdFinEquiv (path,x),finSumFinEquiv (i.map id finProdFinEquiv))

theorem tuple_old (path : Fin (breadth R.degree)) (x : Fin (2^R.depth)) (i : Fin R.oldNodes) :
    tuple R (candidate R path x (.inl i))=![1,path.val,x.val,i.val,0,0]:=by
  simp [tuple,candidate,bookRoot,bookBlock,bookItem]

theorem tuple_born (path : Fin (breadth R.degree)) (x : Fin (2^R.depth)) (seat : Fin R.capacity) (party : Fin 6) :
    tuple R (candidate R path x (.inr (seat,party)))=![2,path.val,x.val,0,seat.val,party.val]:=by
  simp [tuple,candidate,bookRoot,bookBlock,bookItem]

def readLaw (outBits : ℕ) (node : Fin R.newNodes) (field : Fin 6)
    (word : Cell (R.ordinalBits*R.newNodes)) : Cell outBits :=
  let stamp:=((encode R.ordinalBits R.newNodes).symm word node).val
  if valid : 0<stamp ∧ stamp≤extent R then ((tuple R ⟨stamp-1,by omega⟩ field:ℕ):Cell outBits) else 0

theorem at_stamp (outBits : ℕ) (node : Fin R.newNodes) (field : Fin 6) (word : Cell (R.ordinalBits*R.newNodes))
    (j : Fin (extent R)) (original : ((encode R.ordinalBits R.newNodes).symm word node).val=j.val+1) :
    readLaw R outBits node field word=((tuple R j field:ℕ):Cell outBits):=by
  have valid : 0<j.val+1 ∧ j.val+1≤extent R:=⟨by omega,j.isLt⟩
  simp [readLaw,original,valid]

theorem at_blank (outBits : ℕ) (node : Fin R.newNodes) (field : Fin 6) (word : Cell (R.ordinalBits*R.newNodes))
    (empty_ : ((encode R.ordinalBits R.newNodes).symm word node).val=0) :
    readLaw R outBits node field word=0:=by simp [readLaw,empty_]

def law (outBits : ℕ) (i : Fin (R.newNodes*6)) (x : Fin 1→Cell (R.ordinalBits*R.newNodes)) : Cell outBits :=
  let p:Fin R.newNodes×Fin 6:=finProdFinEquiv.symm i
  readLaw R outBits p.1 p.2 (x 0)

theorem dead (outBits : ℕ) (i : Fin (R.newNodes*6)) : law R outBits i (fun _=>0)=0:=by
  apply at_blank
  have z:encode R.ordinalBits R.newNodes (fun _=>0)=0:=by
    apply Fin.ext
    change (finFunctionFinEquiv (fun _:Fin R.newNodes=>(0:Cell R.ordinalBits))).val=0
    simp
  rw [(show (encode R.ordinalBits R.newNodes).symm 0=fun _=>0 from (encode _ _).symm_apply_eq.mpr z.symm)]
  rfl

def words :=DescentOperandFamilyBook.words (R.newNodes*6) 1 (R.ordinalBits*R.newNodes) R.lanes
def endAddress (base : ℕ):=base+words R
def program (outBits base w : ℕ):=DescentOperandFamilyBook.program (law R outBits) R.lanes base w
def image {w} (outBits base : ℕ) (m : Memory w):=DescentOperandFamilyBook.image (law R outBits) R.lanes base m

def expr (outBits floor base : ℕ) (block : Fin R.blocks) (node : Fin R.newNodes) (field : Fin 6) : Expr :=
  DescentOperandFamilyBook.expr (law R outBits) R.lanes base (finProdFinEquiv (node,field))
    (fun _:Fin 1=>.lookup (R.returned floor block) .row)

theorem issued {w} (outBits floor base : ℕ) (m : Memory w) (block : Fin R.blocks)
    (node : Fin R.newNodes) (field : Fin 6) (x : Fin (R.hosts*R.lows)→Fin R.groups→Cell (R.ordinalBits*R.newNodes))
    (early : (R.returned floor block).Fits w base)
    (rows : (R.hosts*R.lows)*chunks R.groups R.lanes≤(R.returned floor block).size)
    (source : Reads (R.returned floor block) x R.lanes m) (space : endAddress R base<2^w) :
    (expr R outBits floor base block node field).Fits w (endAddress R base) ∧
      Source (expr R outBits floor base block node field) (fun h g=>readLaw R outBits node field (x h g)) R.lanes
        (image R outBits base m):=by
  have run:=DescentOperandFamilyBook.issued (law R outBits) (dead R outBits) R.lanes base
    (finProdFinEquiv (node,field)) (fun _:Fin 1=>.lookup (R.returned floor block) .row) m (fun h g (_:Fin 1)=>x h g)
    (fun _=>⟨early,trivial⟩) (fun _=>source_column _ base early m x rows source) space
  simpa only [law, Equiv.symm_apply_apply, expr, endAddress, words, image,
    DescentOperandFamilyBook.endAddress] using run

theorem price (outBits floor base : ℕ) (block : Fin R.blocks) (node : Fin R.newNodes) (f : Fin 6) :
    (expr R outBits floor base block node f).work≤32:=
  DescentOperandFamilyBook.expr_work _ _ _ _ _ 7 (fun _=>le_rfl)

end
end Hierarchy.DescentOrdinaryOriginPorts

end OAI
