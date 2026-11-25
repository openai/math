import OAI.Hierarchy.DescentDatedOriginMouth
import OAI.Hierarchy.DescentPackedChunkWork

namespace OAI
/-! Full native time and instruction payment for the original chip, all three short fields,
the stable donor gather, and the receiving block transpose. -/
namespace Hierarchy.DescentOrdinaryMouthReturn.Layout
open DescentOrdinaryBorn DescentOrdinaryAtomFieldRAM.ScalarOperand DescentPackedActorMask DescentHaloWalkRAM
open DescentSIMDLookup DescentVectorBookReshape DescentStaticWordColumn DescentSixParty.Chronology ProtocolRAM
noncomputable section
variable (L : Layout)

def fan (src : ℕ) :=termBound (nodes (breadth L.degree*2^L.depth) L.oldNodes L.B.cap) src
def fixedCost (src : ℕ) := 1217+977*L.B.fields+(L.pages*L.lows)*(81+28*L.fan src)
def rowCost (src : ℕ) := 68*L.B.fields+(L.pages*L.lows)*(2*L.fan src+4+284*L.radix)
def romCost :=115*(2*(1+L.B.fields)+L.radix)

theorem resources (floor w h src : ℕ) (old : Bank) (C : Fin L.B.args→Fin L.lows→L.Ref)
    (fit : ∀a l,let t:=C a l;t.want.work+t.addr.work+t.counts.work≤ src)
    (hm : 0<L.lanes) (hr : 0<L.radix) (same : L.B.groups=L.groups*L.radix)
    (pitch : L.B.lanes=L.lanes*L.radix)
    (chip : (L.B.chipBits*1+L.B.chipBits)*L.B.lanes≤h/2)
    (packed : (L.bits*L.radix)*L.lanes≤h/2) :
    let P:=L.phase old floor w C
    P.ticks+7*names P.program≤L.fixedCost src+L.rowCost src*(L.B.hosts*chunks L.groups L.lanes)+L.romCost*2^(h/2) :=by
  intro P
  have first:=RolePorts.resources L.B old floor w
  have second:=DescentGatheredVectorReshape.tariff (L.refs floor C) L.B.hosts L.B.groups L.groups L.radix L.lanes
    L.bits w (L.transpose floor) (L.out floor) src (L.raw floor)
    (fun p l=>fit (finProdFinEquiv.symm p : Fin L.B.args×Fin 3).1 l)
  dsimp only at second
  have chunks_ : chunks L.B.groups (L.lanes*L.radix)=chunks L.groups L.lanes :=
    by rw [same];exact chunks_group L.groups L.lanes L.radix hm hr
  have ca:=Nat.pow_le_pow_right (n:=2) (by decide) chip
  have cb:=Nat.pow_le_pow_right (n:=2) (by decide) packed
  change (RolePorts.ticks L.B old floor+(L.gather floor w C).ticks)+
    7*names ((RolePorts.program L.B old floor w).seq (L.gather floor w C).program)≤_
  rw [names_seq]
  calc
    _ ≤ (L.B.cpu + ((4+(L.pages*L.lows)*(4+(L.B.hosts*chunks L.B.groups (L.lanes*L.radix))*(2*L.fan src+4)))+
          (8+10*dictionaryWords L.radix L.bits L.lanes+74*(L.pages*rows L.B.hosts L.lows L.groups L.radix L.lanes))))+
        7*(L.B.textCost+((15+(L.pages*L.lows)*(11+4*L.fan src))+
          (15*(cells L.pages L.B.hosts L.lows L.groups L.radix L.bits L.lanes+1)+111))) :=
      Nat.add_le_add (Nat.add_le_add first.1 second.1) (Nat.mul_le_mul_left 7 (Nat.add_le_add first.2.1 second.2))
    _ ≤ _ :=by
      simp only [Chart.cpu,Chart.textCost,Chart.bookWords,Chart.rows,cells,rows,dictionaryWords,fixedCost,rowCost,romCost]
      simp only [pitch,chunks_] at ca ⊢
      have table : 2^((L.B.chipBits*1+L.B.chipBits)*(L.lanes*L.radix))≤2^(h/2):=ca
      calc
        _ ≤ ((4+10*((1+L.B.fields)*(2*2^(h/2))))+(4+L.B.fields*(4+(L.B.hosts*chunks L.groups L.lanes)*(2*32+4)))+
          ((4+(L.pages*L.lows)*(4+(L.B.hosts*chunks L.groups L.lanes)*(2*L.fan src+4)))+
            (8+10*(L.radix*2^(h/2))+74*(L.pages*(L.radix*((L.B.hosts*L.lows)*chunks L.groups L.lanes))))))+
          7*((15*((1+L.B.fields)*(2*2^(h/2))+1)+(15+L.B.fields*(11+4*32)))+
            ((15+(L.pages*L.lows)*(11+4*L.fan src))+
              (15*((L.radix*2^(h/2)+2*(L.pages*(L.radix*((L.B.hosts*L.lows)*chunks L.groups L.lanes))))+1)+111))) :=by
              with_reducible
                repeat' first | exact le_rfl | exact table | exact cb | apply Nat.add_le_add | apply Nat.mul_le_mul
        _ = _ :=by ring
end
end Hierarchy.DescentOrdinaryMouthReturn.Layout

namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentOrdinaryMouthReturn DescentSIMDLookup DescentStaticWordColumn
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (extra : ℕ)
set_option hygiene false
set_option quotPrecheck false
local notation "dateₘ" => v.withFundedClip extra
local notation "layoutₘ" => (dateₘ).mouthChart rfl

set_option hygiene true
set_option quotPrecheck true
def mouthPeak :=max (dateₘ).bornBook.chipBits (layoutₘ).bits

theorem funded_mouth (floor w ratio : ℕ) (A : (dateₘ).ArgumentEntry) (matched : A.Match dateₘ floor)
    (same : (dateₘ).bornBook.groups=(dateₘ).vector.groups*(dateₘ).vector.radix)
    (short : v.mouthPeak extra≤extra) (paid : 0<v.venue.paidBits) (input : v.venue.paidBits≤v.area.unit)
    (width : 4*v.fundedMaxUnit extra*2^v.area.k≤v.payload) (bus : w≤ratio*v.payload) :
    let p:=(dateₘ).originPrefixMouth floor w A matched
    (p.ticks+7*names p.program)*w ≤ ratio*((layoutₘ).fixedCost 26*v.payload+
      (layoutₘ).rowCost 26*((dateₘ).bornBook.hosts*v.payload+(dateₘ).bornBook.hosts*v.vector.groups*
        ((v.fundedClip extra).radix*v.fundedWorkingUnit extra))+
      (layoutₘ).romCost*2^(v.payload/2)*v.payload) :=by
  intro p
  have capacity:=v.funded_bounds extra paid input width
  have first:=(v.funded_extra_fit extra (dateₘ).bornBook.chipBits (by exact (Nat.le_max_left ..).trans short)).1
  have second:=(v.funded_extra_fit extra (layoutₘ).bits (by exact (Nat.le_max_right ..).trans short)).2.1
  have bits : ((dateₘ).bornBook.chipBits*1+(dateₘ).bornBook.chipBits)*(dateₘ).bornBook.lanes≤v.payload/2 :=by
    rw [Nat.mul_one,Nat.add_mul]
    change (dateₘ).bornBook.chipBits*(v.fundedClip extra).working+
      (dateₘ).bornBook.chipBits*(v.fundedClip extra).working≤v.payload/2
    omega
  have bill:=(layoutₘ).resources ((dateₘ).originPortEnd floor) w v.payload 26 (A.chipBank dateₘ floor)
    ((dateₘ).mouthRef A matched) ((dateₘ).mouth_sources A matched) capacity.out (Nat.two_pow_pos _) same rfl bits (by
      change (layoutₘ).bits*(v.fundedClip extra).radix*(v.fundedClip extra).postPitch≤v.payload/2
      omega)
  have rows_:=DescentDatedSeedStartup.chunk_work (dateₘ).bornBook.hosts v.vector.groups (v.fundedClip extra).postPitch
    v.payload ((v.fundedClip extra).radix*v.fundedWorkingUnit extra) capacity.fill₂
  calc
    _ ≤ ((layoutₘ).fixedCost 26+(layoutₘ).rowCost 26*((dateₘ).bornBook.hosts*chunks v.vector.groups (v.fundedClip extra).postPitch)+
        (layoutₘ).romCost*2^(v.payload/2))*(ratio*v.payload) := Nat.mul_le_mul bill bus
    _ = ratio*((layoutₘ).fixedCost 26*v.payload+(layoutₘ).rowCost 26*
          (((dateₘ).bornBook.hosts*chunks v.vector.groups (v.fundedClip extra).postPitch)*v.payload)+
          (layoutₘ).romCost*2^(v.payload/2)*v.payload) :=by ring
    _ ≤ _ := by gcongr

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
