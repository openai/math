import OAI.Hierarchy.DescentContactDonorFrontLayout
import OAI.Hierarchy.DescentContactSenderRead

namespace OAI
/-! # One earlier RAM phase for all old sender, reciprocal, and halo operands -/
namespace Hierarchy.DescentContactDonorFront.Shape
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentSixParty.Chronology
open DescentResetSignedHaloMatrix DescentPackedChildNeighbor.SIMD
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable (A : Shape) (base : ℕ) {w : ℕ}
variable (u : DescentContactSenderDate.Prior A.degree A.lows A.cap A.n A.residual)
local notation "sender" => A.sender base
local notation "halo" => A.halo base u.routes.roster
local notation "H" => A.hosts
local notation "G" => A.groups
local notation "M" => A.batch
local notation "D" => A.degree

structure Space (w : ℕ) : Prop where
  «sender» : (A.sender base).PriorFits u w
  roster : u.routes.roster.Fits w base
  rosterLength : H*D≤u.routes.roster.size
  hosts : H<2^w
  degree : D+1<2^w
  extent : A.endAddress base+H*chunks G M<2^w

theorem ordered : base≤A.idBase base ∧ A.idBase base≤A.haloStart base ∧ A.haloStart base≤A.endAddress base := by
  obtain ⟨a,b,c,d,e⟩:=(sender).bounds
  exact ⟨a.trans (b.trans (c.trans (d.trans e))),Nat.le_add_right ..,Nat.le_add_right ..⟩

variable (r : A.Space base u w)
include r in
theorem haloFits : (halo).Fits w := by
  obtain ⟨old,uploaded,finish⟩:=A.ordered base
  have small : A.haloStart base<2^w:=finish.trans_lt ((Nat.le_add_right ..).trans_lt r.extent)
  have countable : (A.oldCount base).base+(A.oldCount base).size≤A.haloStart base:=by
    change A.idBase base+1≤A.idBase base+(1+_)
    exact Nat.add_le_add_left (Nat.le_add_right ..) _
  have directory : (A.owner base).base+(A.owner base).size=A.haloStart base:=Nat.add_assoc ..
  exact arrange_fits ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (countable.trans_lt small),countable⟩
    ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (directory.le.trans_lt small),directory.le⟩
    ⟨r.roster.1,r.roster.2.1,r.roster.2.2.trans (old.trans uploaded)⟩
    r.hosts r.hosts r.degree r.rosterLength (by change (halo).high + H*chunks G M < 2^w; rw [A.halo_end base u.routes.roster];exact r.extent)

def idImage (m : Memory w) := DescentStaticWordColumn.image (A.idBase base) A.identityWord ((sender).image u m) A.idCells
def memory (m : Memory w) := (halo).finalMem (A.idImage base u m)
def program (w : ℕ) := (((sender).program u w).seq
    (DescentStaticWordColumn.program w (A.idBase base) A.identityWord A.idCells)).seq ((halo).cpu w)
def ticks := ((sender).ticks u+(4+10*A.idCells))+(halo).ticks

include r in
theorem any (m : Memory w) :
    (A.program base u w).Exec m (A.memory base u m) (A.ticks base u) ∧ CheapCode (A.program base u w) ∧
    ∀a,a<base ∨ A.endAddress base≤a→A.memory base u m a=m a := by
  obtain ⟨start,ids,past⟩:=A.ordered base
  have end_ : A.endAddress base<2^w:=(Nat.le_add_right ..).trans_lt r.extent
  obtain ⟨run,one,keep⟩:=(sender).any u m r.sender (ids.trans_lt (past.trans_lt end_))
  have mid : (DescentStaticWordColumn.program w (A.idBase base) A.identityWord A.idCells).Exec ((sender).image u m) (A.idImage base u m) (4+10*A.idCells) := DescentStaticWordColumn.mount (A.idBase base) A.idCells A.identityWord ((sender).image u m) (past.trans_lt end_)
  obtain ⟨last,three,frame⟩:=(halo).any (A.haloFits base u r) (A.idImage base u m)
  refine ⟨Procedure.Exec.then (Procedure.Exec.then run mid) last,cheap_seq (cheap_seq one (@DescentStaticWordColumn.cheap _ _ _ _)) three,?_⟩
  intro a e
  have outside : a<(halo).root ∨ (halo).high≤a:=e.imp (fun h=>h.trans_le (start.trans ids))
    (fun h=>(A.halo_end base u.routes.roster).le.trans h)
  exact (frame a outside).trans ((DescentStaticWordColumn.frame _ _ _ _ _ (e.imp
    (fun h=>h.trans_le start) (fun h=>past.trans h))).trans
    (keep a (e.imp id (fun h=>(ids.trans past).trans h))))

def native : NativePhase w := ⟨A.program base u w,A.ticks base u,A.memory base u,(A.any base u r (fun _=>0)).2.1⟩

include r in
theorem sender_frame (m : Memory w) (a : ℕ) (lo : a<A.idBase base) :
    A.memory base u m a=(sender).image u m a := by
  have early:=(A.ordered base).2.1
  have frame:=((halo).any (A.haloFits base u r) (A.idImage base u m)).2.2
  exact (frame a (.inl (lo.trans_le early))).trans (DescentStaticWordColumn.frame _ _ _ _ _ (.inl lo))

def priorSensor (s : Bool) (j : Fin (A.lows*(2*A.cap))) (f : Fin 5) : Expr :=
  let t:=finProdFinEquiv.symm j
  .lookup (![(sender).senderBank s t 0,(sender).returnBank s t 0,(sender).senderBank s t 1,
    (sender).returnBank s t 1,(sender).senderBank s t 2] f) .row

local notation "point" => Fin A.lows×Fin (2*A.cap)
local notation "span" => DescentResetOppositePayload.span A.degree A.cap
local notation "oldN" => DescentOldContactSender.count A.degree A.lows A.cap A.n A.residual
local notation "big" => A.fieldBits*DescentOldContactSender.lanes A.lows A.cap
variable (xs : Fin A.hosts→Fin A.groups→Fin (DescentOldContactSender.count A.degree A.lows A.cap A.n A.residual)→Cell A.fieldBits)
    (next : Fin A.hosts→Fin A.degree→Option (Fin A.hosts)) (raw : Fin A.lows→Fin (2*A.cap)→Fin A.hosts→Fin A.groups→Cell A.fieldBits)

def sensorValue (s : Bool) (j : Fin (A.lows*(2*A.cap))) (f : Fin 5) : Fin A.hosts→Fin A.groups→Cell A.fieldBits :=
  let t:=finProdFinEquiv.symm j
  ![(sender).sentValue xs s t 0,(sender).arrivedValue xs next raw s t 0,(sender).sentValue xs s t 1,
    (sender).arrivedValue xs next raw s t 1,(sender).sentValue xs s t 2] f

include r in
theorem sensor_banks (s : Bool) (t : point) :
    (∀i,((sender).senderBank s t i).Fits w (A.idBase base) ∧ H*chunks G M≤((sender).senderBank s t i).size) ∧
    ∀i,((sender).returnBank s t i).Fits w (A.idBase base) ∧ H*chunks G M≤((sender).returnBank s t i).size := by
  obtain ⟨_,_,_,s0,s1⟩:=(sender).bounds
  have end_ : A.idBase base<2^w:=(A.ordered base).2.1.trans_lt ((A.ordered base).2.2.trans_lt ((Nat.le_add_right ..).trans_lt r.extent))
  constructor
  · intro i
    have f:=(sender).splitShape.output_fits (N:=2) (field:=big) (DescentOldContactSender.lane s (finProdFinEquiv t) i).val
      (Fin.isLt _) ((s0.trans s1).trans_lt end_)
    exact ⟨⟨f.1,f.2.1,f.2.2.trans (s0.trans s1)⟩,(sender).splitShape.rows_fit⟩
  · intro i
    have le_ : ((sender).returnShape s).endAddress span A.fieldBits≤A.idBase base:=by
      cases s
      · exact s1
      · exact le_rfl
    have f:=((sender).returnShape s).output_fits (N:=span) (field:=A.fieldBits)
      (DescentContactSenderDate.Layout.ticket t i).val (by cases s <;> exact (DescentContactSenderDate.Layout.ticket t i).isLt) (le_.trans_lt end_)
    exact ⟨⟨f.1,f.2.1,f.2.2.trans le_⟩,by cases s <;> exact (sender).localShape.rows_fit⟩

include r in
theorem priorSensor_fits (s : Bool) (j : Fin (A.lows*(2*A.cap))) (f : Fin 5) :
    (A.priorSensor base s j f).Fits w (A.endAddress base) := by
  have ⟨at_,far⟩:=A.sensor_banks base u r s (finProdFinEquiv.symm j)
  have early:=(A.ordered base).2.1.trans (A.ordered base).2.2
  apply ProtocolRAMGeneratedWrite.fits_mono _ early
  fin_cases f <;> first | exact ⟨(at_ _).1,trivial⟩ | exact ⟨(far _).1,trivial⟩

include r in
theorem sources (m : Memory w) (packed : (sender).Packed w) (real : (sender).Before u xs next raw m) :
    ∀s j f,Source (A.priorSensor base s j f) (A.sensorValue base xs next raw s j f) M (A.memory base u m) := by
  have end_ : A.idBase base<2^w:=(A.ordered base).2.1.trans_lt ((A.ordered base).2.2.trans_lt ((Nat.le_add_right ..).trans_lt r.extent))
  obtain ⟨here,there⟩:=(sender).sources u xs next raw m r.sender packed end_ real
  intro s j f
  let t:=finProdFinEquiv.symm j
  obtain ⟨localFits,farFits⟩:=A.sensor_banks base u r s t
  have preserve (b : Bank) (v : Fin H→Fin G→Cell A.fieldBits)
      (legal : b.Fits w (A.idBase base) ∧ H*chunks G M≤b.size) (observed : Reads b v M ((sender).image u m)) :
      Source (.lookup b .row) v M (A.memory base u m) := by
    apply source_column b (A.idBase base) legal.1 _ _ legal.2
    intro q
    have visible : b.base+(row H G M q).val<A.idBase base:=
      (Nat.add_lt_add_left ((row H G M q).isLt.trans_le legal.2) _).trans_le legal.1.2.2
    exact (A.sender_frame base u r m _ visible).trans (observed q)
  fin_cases f
  all_goals first | exact preserve _ _ (localFits _) (here s t _) | exact preserve _ _ (farFits _) (there s t _)

include r in
theorem identity_roster (m : Memory w) (p : Fin H→Fin D→Option (Fin H)) (mounted : Mounted u.routes p m G M) :
    (∀addr,addr<base→A.idImage base u m addr=m addr) ∧
    A.idImage base u m (A.oldCount base).base=(H:Word w) ∧
    (∀i : Fin H,A.idImage base u m ((A.owner base).base+i.val)=(i.val:Word w)) ∧
    (∀v j,A.idImage base u m (u.routes.roster.base+(v.val*D+j.val))=(target (p v j):Word w)) := by
  obtain ⟨start,ids,past⟩:=A.ordered base
  have oldPos (a : ℕ) (low : a<base) : A.idImage base u m a=m a := by
    have oldEnd : A.idBase base<2^w:=(ids.trans past).trans_lt ((Nat.le_add_right ..).trans_lt r.extent)
    exact (DescentStaticWordColumn.frame _ _ _ _ _ (.inl (low.trans_le start))).trans
      (((sender).any u m r.sender oldEnd).2.2 _ (.inl low))
  have counted : A.idImage base u m (A.oldCount base).base=(H:Word w) := by
    simpa [idImage,oldCount,identityWord] using
      DescentStaticWordColumn.read (A.idBase base) A.idCells A.identityWord ((sender).image u m)
        (j:=0) (show 0<A.idCells from Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_add_right 1 _))
  have names (i : Fin H) : A.idImage base u m ((A.owner base).base+i.val)=(i.val:Word w) := by
    have small:=i.isLt.trans_le (DescentResetOriginalSlots.rows_le H)
    change i.val < 2^Nat.clog 2 A.hosts at small
    simpa [idImage,owner,identityWord,Nat.add_assoc,Nat.add_comm 1 i.val] using
      DescentStaticWordColumn.read (A.idBase base) A.idCells A.identityWord ((sender).image u m)
        (j:=i.val+1) (by unfold idCells;omega)
  have edges (v : Fin H) (j : Fin D) : A.idImage base u m (u.routes.roster.base+(v.val*D+j.val))=
      (target (p v j):Word w) := by
    have lt_ : v.val*D+j.val<H*D:=(Nat.add_lt_add_left j.isLt _).trans_le
      (by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ v.isLt)
    exact (oldPos _ ((Nat.add_lt_add_left (lt_.trans_le r.rosterLength) _).trans_le r.roster.2.2)).trans (mounted.roster v j)
  exact ⟨oldPos,counted,names,edges⟩

include r in
theorem oldHalo (m : Memory w) (p : Fin H→Fin D→Option (Fin H)) (mounted : Mounted u.routes p m G M)
    (wide : D+2<2^A.cargoBits) (port : Expr) (data_ : Fin H→Fin G→Cell A.fieldBits)
    (fits : port.Fits w base) (read : Source port data_ M m) :
    ((halo).port port).Fits w (A.endAddress base) ∧ Source ((halo).port port)
      (fun h g=>lookup (short (b:=A.cargoBits) p id h)
        (askedField D A.cap A.fieldBits A.queryBits (data_ h g) 0) (List.finRange (D+1))) M (A.memory base u m) := by
  obtain ⟨start,ids,_⟩:=A.ordered base
  obtain ⟨oldPos,counted,names,edges⟩:=A.identity_roster base u r m p mounted
  have at_ : Source port data_ M (A.idImage base u m):=fun j=>
    (eval_below port _ m (A.idImage base u m) fits oldPos).trans (read j)
  have result:=(halo).posted (A.haloFits base u r) (A.idImage base u m) p id le_rfl
    (DescentResetOriginalSlots.rows_le H) wide counted names edges port data_
    (ProtocolRAMGeneratedWrite.fits_mono port (start.trans ids) fits) at_
  refine ⟨?_,result.2.2⟩
  rw [←A.halo_end base u.routes.roster]
  exact result.2.1

end
end Hierarchy.DescentContactDonorFront.Shape

end OAI
