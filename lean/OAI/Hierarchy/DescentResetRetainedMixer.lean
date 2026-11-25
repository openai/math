import OAI.Hierarchy.DescentResetRetainedBasis

namespace OAI
/-! # The remixed original channels at the receiving aperture -/
namespace Hierarchy.DescentResetRetainedSetup.Layout
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentGLPacked.BankImage DescentGLNielsen
open DescentSixParty.Chronology ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
noncomputable section
variable {w : ℕ} (v : Layout)

def mixedBank (base : ℕ) (i : Fin v.channels) : Bank :=
  ⟨slice ((((v.chart base).chosen (v.high+v.low)).bank (schedule (v.high+v.low)).length).base)
    v.hosts (2^v.high) i,Nat.clog 2 (v.hosts*2^v.high)⟩
def hostBank (base : ℕ) (i : Fin v.channels) :=
  Strip.bank (v.mixed base) v.hosts v.grouped v.matrixLanes v.decodedLanes v.stripWord i.val
def receiving (base w : ℕ) :=
  Strip.code (v.mixed base) v.hosts v.grouped v.matrixLanes v.decodedLanes v.stripWord w (v.mixedBank base)
def moved (base w : ℕ) (old : Fin v.sources→Bank) (key : Bank) :=(v.basisProgram base w old key).seq (v.receiving base w).program
def movedTicks (base w : ℕ) (old : Fin v.sources→Bank) (key : Bank) :=v.basisTicks base w old key+(v.receiving base w).ticks
def movedImage (base : ℕ) (old : Fin v.sources→Bank) (key : Bank) (m : Memory w) :=(v.receiving base w).image (v.basisImage base old key m)

theorem mixed_fit (base : ℕ) (i : Fin v.channels) (space : v.mixed base<2^w) : (v.mixedBank base i).Fits w (v.mixed base) :=by
  let C:=v.chart base
  let d:=v.high+v.low
  let n:=(schedule d).length
  let q:=v.hosts*2^v.high
  have data_ : Size C (v.channels*v.hosts) v.high v.low v.bits w :=
    (SignedFields.allocation (v.matrix base) v.channels v.hosts v.high v.low v.bits w space).1
  have all : v.channels*q≤C.page:=by simpa only [q,←Nat.mul_assoc] using data_.rows
  have one : 1≤v.channels:=by have:=i.isLt;omega
  have part : q≤C.page:=(show q≤v.channels*q by simpa only [Nat.one_mul] using Nat.mul_le_mul_right q one).trans all
  have rounded : 2^Nat.clog 2 q≤C.page:=Nat.pow_le_pow_right (by decide) (Nat.clog_le_of_le_pow part)
  have idx : i.val*q≤C.page:=(Nat.mul_le_mul_right q i.isLt.le).trans all
  have gap : C.input.base+C.input.size≤C.start := data_.input.2.2
  have heap : C.start≤C.heap d:=Nat.le_add_right ..
  have earlier : C.input.base≤C.start:=(Nat.le_add_right ..).trans gap
  have span : (v.mixedBank base i).base+(v.mixedBank base i).size≤v.mixed base:=by
    change ((C.chosen d).bank n).base+i.val*v.hosts*2^v.high+2^Nat.clog 2 q≤C.heap d+(n+1)*C.page
    rw [Nat.mul_assoc]
    change ((C.chosen d).bank n).base+i.val*q+2^Nat.clog 2 q≤C.heap d+(n+1)*C.page
    cases eq:n with
    | zero=>
       change C.input.base+i.val*q+2^Nat.clog 2 q≤C.heap d+(0+1)*C.page
       have inputSize : v.channels*q≤C.input.size:=by simpa only [q,←Nat.mul_assoc] using data_.inputSize
       have row:= (Nat.mul_le_mul_right q i.isLt.le).trans inputSize
       simp only [Nat.zero_add,Nat.one_mul];omega
    | succ k=>
       change C.heap d+k*C.page+i.val*q+2^Nat.clog 2 q≤C.heap d+(k+1+1)*C.page
       rw [Nat.succ_mul,Nat.succ_mul];omega
  exact ⟨Nat.two_pow_pos _,(Nat.le_add_left _ _).trans_lt (span.trans_lt space),span⟩

theorem moved_any (base : ℕ) (old : Fin v.sources→Bank) (saved : Bank) (m : Memory w)
    (orig : ∀i,(old i).Fits w base) (key : saved.Fits w base) (room : v.tables base<2^w) :
    (v.moved base w old saved).Exec m (v.movedImage base old saved m) (v.movedTicks base w old saved) ∧
    (∀x,x<base ∨ v.tables base≤x→v.movedImage base old saved m x=m x) ∧ CheapCode (v.moved base w old saved) :=by
  obtain ⟨lo,a,b,c,d,_⟩:=v.order base
  have before :=lo.trans (a.trans (b.trans c))
  obtain ⟨first,f1,cheap⟩:=v.basis_any base old saved m orig key (d.trans_lt room)
  obtain ⟨last_,f2⟩:=Strip.any (v.mixed base) v.hosts v.grouped v.matrixLanes v.decodedLanes v.stripWord
    (v.mixedBank base) (v.basisImage base old saved m) (fun j=>v.mixed_fit base j (d.trans_lt room)) room
  exact ⟨first.then last_,fun x h=>(f2 x (h.imp_left (fun z=>z.trans_le before))).trans
    (f1 x (h.imp_right (fun z=>d.trans z))),cheap_seq cheap (NativePhase.cheap _)⟩

end
end Hierarchy.DescentResetRetainedSetup.Layout

end OAI
