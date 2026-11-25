import OAI.Hierarchy.DescentDonorNumericHeads
import OAI.Hierarchy.DescentDonorParts
import OAI.Hierarchy.DescentDonorEncodedBits

namespace OAI
/-! The six packed donor fields determine every ordinary birth-chip output bit. -/

namespace Hierarchy.DescentSharedCableNames.Stage
open DescentSIMDLookup DescentSignedCableCodec
open scoped Classical
noncomputable section

def atSource {D cap : ℕ} (ticket : Fin cap) : Option (Live D cap)→Bool
  | none=>false
  | some p=>(!p.target) && decide (p.sourceWire=ticket)

def sourceGrains {D cap : ℕ} (panel : Fin (2*cap)→Cell (width D cap)) (ticket : Fin cap) :=
  (Finset.univ.filter (fun j=>atSource ticket (decode D cap (panel j))=true)).card

end
end Hierarchy.DescentSharedCableNames.Stage

namespace Hierarchy.DescentRawCablePanel
open DescentSIMDLookup DescentSixParty DescentPacking.PackedMatch.Local
open scoped Classical Fin.CommRing
noncomputable section

def representative : Fin 3→Fin 6 := ![demandSrc 0,demandDst 0,demandDst 1]

def emptyDonor (s a c : ℕ) : Donor s a c :=
  ⟨false,false,false,false,0,0,fun _=>0,0,0,fun _=>0⟩

/-- The physical rooted walk lookup supplies a short ordinal in the donor's
four-step host roster. A single roster serves every actor read at this donor. -/
structure LocalActor where
  rank : ℕ
  hub : Bool
  node : ℕ
  pack : ℕ

def actorWord (slots a : ℕ) (rows : List LocalActor) (x : LocalActor) : Cell (3+1+a) :=
  endpoint 3 a ((((rows.map LocalActor.rank).idxOf x.rank:ℕ),tag x.hub),(x.node*slots+x.pack:ℕ))

def observations (left right : LocalActor) (anchor : Option (Fin 3→LocalActor)) :=
  [left,right]++(anchor.toList.flatMap fun f=>List.ofFn f)

def observedDonor (slots a c : ℕ) (left right : LocalActor) (anchor : Option (Fin 3→LocalActor))
    (chosen lay : Bool) (old arm : Cell c) (supply : Fin 8→Cell c) : Donor 3 a c :=
  let rows:=observations left right anchor
  {live:=true,picked:=chosen,first:=anchor.isSome,layout:=lay,left:=actorWord slots a rows left,
   right:=actorWord slots a rows right,anchors:=fun t=>(anchor.map (fun f=>actorWord slots a rows (f t))).getD 0,
   oldUnits:=old,armUnits:=arm,supplyUnits:=supply}

/-- This numeric cell contains no global actor or cable identifiers. The old
source seat, its original peer, the marked matcher and the six genuine birth
roles all use the same common roster at the selected prior source. -/
def depot (a c slots b : ℕ) {r D cap d : ℕ} (B profile : ℕ) (panel : Panel r D (2*cap) d)
    (records : Fin (2*cap)→Cell (DescentSignedCableCodec.width D cap))
    (readWalk : Walk→LocalActor) (here : Fin r→Address) (neighbor : Fin D→Fin r→Address)
    (supply : Fin 8→Cell c) (lay : Bool) (x : Fin r) (s : Fin cap) : Donor 3 a c :=
  let n:=DescentSharedCableNames.Stage.sourceGrains records s
  let t:=s.castLE (show cap≤2*cap by omega)
  if n=0 then emptyDonor 3 a c else
    let peer:=(DescentSignedCableCodec.decode D cap (records t)).elim 0 fun v=>v.neighbor.val+1
    let old:=actorHeads B profile panel lay here neighbor x t
    observedDonor slots a c (readWalk (look here neighbor (0,x.val))) (readWalk (look here neighbor (peer,x.val)))
      (old.born.map (fun ws k=>readWalk (ws (representative k)))) (DescentPacking.PackedMatch.Local.Stage.markedChoice B profile panel x s.val)
      lay (n*b:ℕ) b supply

end
end Hierarchy.DescentRawCablePanel

namespace Hierarchy.DescentRawCablePanel.DepotRAM
open DescentSIMDLookup DescentPacking.PackedMatch.Local DescentSharedCableNames DescentHaloWalkRAM
open scoped Classical Fin.CommRing
variable (s : Shape)
noncomputable section

def chip (B profile b slots : ℕ) (f : Parts s) : Cell (outputBits s) :=
  let fields_ : Cell 1×Cell (s.short*fields s.blocks s.degree (2*s.cap)) :=
    finProdFinEquiv.symm (finCongr (pow_add 2 1 _) f.terrain)
  let layout:=decide (fields_.1.val=1)
  let panel:=decodePanel fields_.2
  let signed:=(encode (DescentSignedCableCodec.width s.degree s.cap) (s.blocks*(2*s.cap))).symm f.cables
  let own:=(encode ((Owners.digits s.blocks s.degree s.short*3)*s.blocks) (s.degree+1)).symm f.owners
  let ord:=(encode (Packed.bits (breadth s.degree)) (breadth s.degree)).symm f.chart
  let hub:=(encode (Packed.bits (breadth s.degree)) (breadth s.degree)).symm f.hub
  let born:=(encode s.widths ((s.blocks*s.cap)*8)).symm f.births
  let read (w : Walk) : LocalActor :=
    ⟨(ord (ActorPath.index s.degree w)).val,decide ((hub (ActorPath.index s.degree w)).val=1),w.2.2.1,w.2.2.2⟩
  encode (bundleBits 3 s.names s.widths) (s.blocks*s.cap) (fun j=>
    let z:=finProdFinEquiv.symm j
    packDonor (depot s.names s.widths slots b B profile panel (fun t=>signed (finProdFinEquiv (z.1,t))) read
      (Owners.addressed (own 0)) (fun peer=>Owners.addressed (own peer.succ))
      (fun wire=>born (finProdFinEquiv (j,wire))) layout z.1 z.2))

def output (B profile b slots : ℕ) (v : Cell (totalBits s)) := chip s B profile b slots (separate s v)

end
end Hierarchy.DescentRawCablePanel.DepotRAM

end OAI
