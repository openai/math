import OAI.Hierarchy.DescentResetReceiverCPU

namespace OAI
/-! # Address bounds for the measured old signed columns and their public projections -/
namespace Hierarchy.DescentFallbackPeriod.Projected.Receiver
open DescentGLPacked DescentGLPacked.BankImage DescentGLPacked.BankImage.SignedFields
open DescentGLNielsen DescentGLControlCode DescentSIMDLookup DescentPackedZip
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {D cap N n r c H G K R M h l t field Ht w : ℕ}
  (a : Receiver D cap N n r c H G K R M h l t field Ht w)
local notation "b" => DescentSignedCableCodec.width D cap
local notation "ports" => 2*cap
local notation "L" => 2^r

theorem tapped_fits (j : Fin ports) (room : a.signedEnd<2^w) : (a.tapped j).Fits w a.signedEnd := by
  let C:=a.signedChart
  let d:=h+l
  have qr:=SignedFields.allocation a.signedOrigin ports H h l b w room
  have sz:=qr.1
  have jump:j.val*H*2^h≤ ports*H*2^h:=Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ j.isLt.le)
  have whole:H*2^h≤ ports*H*2^h:=by
    have positive:1≤ ports:=by have:=j.isLt;omega
    simpa using Nat.mul_le_mul_right (2^h) (Nat.mul_le_mul_right H positive)
  have width:2^(Nat.clog 2 (H*2^h))≤ C.page:=
    Nat.pow_le_pow_right (by decide) (Nat.clog_le_of_le_pow (whole.trans sz.rows))
  have pad:((C.chosen d).bank (schedule d).length).base+j.val*H*2^h+2^(Nat.clog 2 (H*2^h))≤ a.signedEnd:=by
    change _≤ C.heap d+((schedule d).length+1)*C.page
    cases eq:(schedule d).length with
    | zero=>
      have addr:C.input.base+C.input.size≤ C.start:=sz.input.2.2
      have low:C.start≤ C.heap d:=Nat.le_add_right ..
      change C.input.base+j.val*H*2^h+2^(Nat.clog 2 (H*2^h))≤ C.heap d+(0+1)*C.page
      have raw:=jump.trans sz.inputSize
      simpa only [Nat.zero_add,Nat.one_mul] using
        (Nat.add_le_add ((Nat.add_le_add_left raw _).trans (addr.trans low)) width)
    | succ s=>
      change (C.heap d+s*C.page)+j.val*H*2^h+2^(Nat.clog 2 (H*2^h))≤ C.heap d+(s+1+1)*C.page
      have raw : j.val*H*2^h ≤ C.page := jump.trans sz.rows
      rw [Nat.succ_mul (s+1) C.page, Nat.succ_mul s C.page]
      omega
  change 0<2^(Nat.clog 2 (H*2^h)) ∧ 2^(Nat.clog 2 (H*2^h))<2^w ∧ _
  exact ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (pad.trans_lt room),pad⟩

theorem prefix_fits
    (old : ∀j x,(a.old j x).Fits w a.origin)
    (capacity : ∀j x,H*chunks G (R*M)≤(a.old j x).size)
    (saved : a.saved.Fits w a.retileEnd)
    (stencil : a.stencil.Fits w a.signedEnd)
    (rows : H*chunks (2^c) M≤ a.stencil.size)
    (laneRows : chunks (2^c) M=2^h)
    (packed : M*max (maxBits t D cap L) field≤ w/2)
    (top : a.projectionEnd<2^w) : a.PrefixFits := by
  have signed:a.signedEnd<2^w:=(Nat.le_add_right ..).trans_lt top
  have control:a.retileEnd≤ a.signedOrigin:=Nat.le_add_right ..
  have here:a.signedOrigin≤ a.signedEnd:=by
    change a.signedOrigin≤ Dated.endAddress a.signedOrigin (ports*H) h l b
    simp only [Dated.extent, Nat.add_assoc]
    exact Nat.le_add_right ..
  refine ⟨old,capacity,(control.trans here).trans_lt signed,saved,signed,?_⟩
  intro j
  have before:a.signedEnd≤ a.atQuery j:=Nat.le_add_right ..
  have bound:(a.lookup j).loBits≤ maxBits t D cap L:=word_bound a.stencil a.tapped _
  have fit (B : Bank) (ok : B.Fits w a.signedEnd) : B.Fits w (a.atQuery j):=
    ⟨ok.1,ok.2.1,ok.2.2.trans before⟩
  have prior (z : Column L cap) : (spec a.stencil a.tapped t D z).source.Fits w (a.atQuery j) ∧
      H*chunks (2^c) M≤(spec a.stencil a.tapped t D z).source.size := by
    rcases z with ⟨which,i⟩|⟨port,i⟩
    · exact ⟨fit _ stencil,rows⟩
    · refine ⟨fit _ (a.tapped_fits port signed),?_⟩
      rw [laneRows]
      exact Nat.le_pow_clog (by decide) _
  have q:=prior ((column L cap).symm j)
  refine ⟨q.1,q.2,(Nat.mul_le_mul_left _ (max_le_max_right _ bound)).trans packed,?_⟩
  exact (extent (a.lookup j) a.signedEnd (maxBits t D cap L) j bound).trans_lt
    ((Nat.add_le_add_left (Nat.mul_le_mul_left _ j.isLt) _).trans_lt top)

/-- Every emitted window word can be used as an indirect table at the next phase,
including the rounded tail of the last signed column at the last old host. -/
theorem window_fits (z : Column L cap) (top : a.projectionEnd<2^w) :
    (bankAt a.stencil a.tapped t D a.signedEnd H (2^c) M z).Fits w a.projectionEnd := by
  let j:=column L cap z
  let q:=spec a.stencil a.tapped t D z
  let unit:=maxBits t D cap L
  let step:=stride unit H (2^c) M
  have key:q.loBits≤ unit:=word_bound a.stencil a.tapped z
  have budget:=Nat.pow_le_pow_right (by decide : 0<2) (Nat.mul_le_mul_right M key)
  have last:a.signedEnd+step*(j.val+1)≤ a.projectionEnd:=
    Nat.add_le_add_left (Nat.mul_le_mul_left _ j.isLt) _
  rw [Nat.mul_succ] at last
  change 0<2^(Nat.clog 2 (H*chunks (2^c) M)) ∧ 2^(Nat.clog 2 (H*chunks (2^c) M))<2^w ∧ _
  have stop:q.out (a.signedEnd+step*j.val) H (2^c) M+2^(Nat.clog 2 (H*chunks (2^c) M))≤ a.projectionEnd:=by
    unfold Query.out
    have size:step=2^(unit*M)+2^(Nat.clog 2 (H*chunks (2^c) M))+2^(Nat.clog 2 (H*chunks (2^c) M)):=rfl
    omega
  exact ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (stop.trans_lt top),stop⟩

end
end Hierarchy.DescentFallbackPeriod.Projected.Receiver

end OAI
