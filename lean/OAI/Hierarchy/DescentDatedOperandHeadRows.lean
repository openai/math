import OAI.Hierarchy.DescentDatedOperandHeadBill
import OAI.Hierarchy.DescentPackedChunkWork

namespace OAI
/-! The five ordinary head readers visit the original signed rows and the acquired resolver
rows. The number of heads and the cost of an original field expression are explicit. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentOrdinaryHeadRetile DescentSIMDLookup DescentDatedAddressBook DescentStaticWordColumn
open Filter
noncomputable section

def headCoefficient (n work : ℕ) :=
  4*4096*(n+1)+109+n*((4+(2*work+4))+7*(11+4*work))

private theorem shape_head_rows (s : Shape) (work h budget : ℕ) (positive : 0<s.hosts)
    (fixed : h≤budget) (old : s.oldRows*h≤budget)
    (next : (s.hosts*chunks s.groups s.after)*h≤budget) :
    (4096*s.role.rowBill+headerFee s.n s.oldRows work)*h≤headCoefficient s.n work*budget :=by
  let p:=Overlap.pieces s.groups s.before s.after
  let newRows:=s.hosts*chunks s.groups s.after
  change newRows*h≤budget at next
  have one : p≤ s.oldRows:=(Nat.min_le_left ..).trans (Nat.le_mul_of_pos_left _ positive)
  have window : p*h≤budget:=(Nat.mul_le_mul_right _ one).trans old
  have span : (s.oldRows+newRows+p+1)*h≤4*budget:=by
    rw [Nat.add_mul,Nat.add_mul,Nat.add_mul,Nat.one_mul]
    omega
  have raw := Nat.mul_le_mul_left (4096*(s.n+1)) span
  have headerPart : ((4+s.oldRows*(2*work+4))+7*(11+4*work))*h≤
      ((4+(2*work+4))+7*(11+4*work))*budget :=by
    calc
      _ = 4*h+(2*work+4)*(s.oldRows*h)+(7*(11+4*work))*h:=by ring
      _ ≤ 4*budget+(2*work+4)*budget+(7*(11+4*work))*budget :=
        Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ fixed) (Nat.mul_le_mul_left _ old))
          (Nat.mul_le_mul_left _ fixed)
      _ = _ :=by ring
  have part := Nat.add_le_add (Nat.mul_le_mul_left 109 fixed) (Nat.mul_le_mul_left s.n headerPart)
  change (4096*((s.n+1)*(s.oldRows+newRows+p+1))+headerFee s.n s.oldRows work)*h≤_
  unfold headerFee headCoefficient
  nlinarith only [raw,part]

variable {F Pin : Type} [Field F] (v : PhysicalOrdinary F Pin)
def headUnit :=headCoefficient v.wideHeads.n v.headLimit+headCoefficient v.narrowHeads.n 512

/-- At the actual signed pitch a full old row pays '4*unit'. The successor density
is the one measured on the same registered resolver through 'registered_row_room'. -/
theorem head_rows_paid (h nextUnit : ℕ) (height : v.payload=h)
    (selected : v.signed=v.signedLayout.format v.payload) (live : 0<v.signed.hosts)
    (wide : 2*v.signedLayout.unit≤h) (density : h≤v.resolver.lanes*nextUnit) :
    v.headRowBill*h ≤ v.headUnit*(v.signed.hosts*h+
      v.signed.hosts*v.signed.groups*(4*v.signedLayout.unit+nextUnit)) :=by
  let H:=v.signed.hosts
  let G:=v.signed.groups
  let U:=v.signedLayout.unit
  let budget:=H*h+H*G*(4*U+nextUnit)
  have pitch : v.signed.lanes=lanes h U:=calc
    _ = (v.signedLayout.format v.payload).lanes:=congrArg SignedExtent.lanes selected
    _ = lanes v.payload U:=rfl
    _ = _:=by rw [height]
  have fixed : h≤budget:=(Nat.le_mul_of_pos_left _ live).trans (Nat.le_add_right ..)
  have old : H*chunks G v.signed.lanes*h≤budget:=by
    rw [pitch]
    apply (volume H G h U v.signedLayout.positive wide).trans
    dsimp only [budget]
    ring_nf
    omega
  have next : H*chunks G v.resolver.lanes*h≤budget:=by
    apply (DescentDatedSeedStartup.chunk_work H G v.resolver.lanes h nextUnit density).trans
    exact Nat.add_le_add_left (Nat.mul_le_mul_left (H*G) (Nat.le_add_left ..)) _
  have a:=shape_head_rows v.wideHeads v.headLimit h budget live fixed old next
  have b:=shape_head_rows v.narrowHeads 512 h budget live fixed old next
  simpa only [headRowBill,headUnit,Nat.add_mul] using Nat.add_le_add a b

theorem head_transfer_paid_all (factor saving : ℕ) :
    ∀ᶠ h : ℕ in atTop,∀(Pin : Type),∀(v : PhysicalOrdinary F Pin)(floor w J original nextUnit : ℕ)(c : v.SignedChart),
    v.payload=h → v.signed=v.signedLayout.format v.payload → 0<v.signed.hosts →
    2*v.signedLayout.unit≤h → 0<v.resolver.lanes → v.resolver.lanes≤h → h≤v.resolver.lanes*nextUnit →
    J≤Nat.log 2 h → 2^h≤original → w+1≤factor*h →
    let code:=v.headTransferPhase floor c w
    (code.ticks+7*names code.program)*(w+1) ≤ 2*(original/(2^J)^saving)+
      factor*v.headUnit*(v.signed.hosts*h+v.signed.hosts*v.signed.groups*(4*v.signedLayout.unit+nextUnit)) :=by
  filter_upwards [head_transfer_bill_all (F:=F) factor saving] with h bill
  intro Pin v floor w J original nextUnit c height selected live wide next nextMax density hj huge bus code
  have fit:=v.head_signed_width selected
  rw [height] at fit
  have pitch : v.signed.lanes=lanes h v.signedLayout.unit:=calc
    _ = (v.signedLayout.format v.payload).lanes:=congrArg SignedExtent.lanes selected
    _ = lanes v.payload v.signedLayout.unit:=rfl
    _ = _:=by rw [height]
  have pos : 0<v.signed.lanes:=by rw [pitch];exact Nat.div_pos wide (by have:=v.signedLayout.positive;omega)
  have limit : v.signed.lanes≤h:=by rw [pitch];exact Nat.div_le_self ..
  apply (bill Pin floor w J original v c hj huge pos next limit nextMax fit.1 fit.2 bus).trans
  apply Nat.add_le_add_left
  simpa only [Nat.mul_left_comm,Nat.mul_assoc] using Nat.mul_le_mul_left factor (v.head_rows_paid h nextUnit height selected live wide density)

theorem head_transfer_paid (factor saving : ℕ) :
    ∀ᶠ h : ℕ in atTop,∀(v : PhysicalOrdinary F Pin)(floor w J original nextUnit : ℕ)(c : v.SignedChart),
    v.payload=h → v.signed=v.signedLayout.format v.payload → 0<v.signed.hosts →
    2*v.signedLayout.unit≤h → 0<v.resolver.lanes → v.resolver.lanes≤h → h≤v.resolver.lanes*nextUnit →
    J≤Nat.log 2 h → 2^h≤original → w+1≤factor*h →
    let code:=v.headTransferPhase floor c w
    (code.ticks+7*names code.program)*(w+1) ≤ 2*(original/(2^J)^saving)+
      factor*v.headUnit*(v.signed.hosts*h+v.signed.hosts*v.signed.groups*(4*v.signedLayout.unit+nextUnit)) :=
  (head_transfer_paid_all (F:=F) factor saving).mono (fun _ all => all Pin)

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
