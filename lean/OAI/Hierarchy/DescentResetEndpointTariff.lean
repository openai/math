import OAI.Hierarchy.DescentResetStencilCalendar
import OAI.Hierarchy.DescentGlobalControlRoom

namespace OAI
/-! # Bit cost of the post-Walsh re-packing and endpoint instructions at the selected public date -/
namespace Hierarchy.DescentSixParty
open Filter DescentCompiler DescentCompiler.TerminalScale DescentPlainTerminal.Suffix
open PackedFlow.Padded DescentPackedWalsh DescentSIMDLookup ProtocolRAM
noncomputable section

def endpointInvoice (P : StencilBook) (X : StencilBook.Sources) (chip : Bank)
    (first base out f full quota g Y w ratio : ℕ) {K₀ : ℕ}
    (grouped : 2^P.c=K₀*(ratio*P.M)) (pos : 0<ratio) (live : 0<P.M) :=
  let reader:=repackProgram P chip first ratio grouped pos live w
  let writer:=paidProgram P X base out f full quota g full Y w
  let ticks:=repackTime P chip first ratio grouped pos live+paidTime P X base out f full g
  (ticks+7*DescentStaticWordColumn.names (reader.seq writer))*w

variable {F : Type} [Field F] (G : PoweredGadget F)

def endpointFactor (ratio : ℕ) := 140000000*(ratio+1)

private theorem scale_power (k j d : ℕ) : (2 : ℕ)^(d*k*(j+1)) = (2^(k*(j+1)))^d := by
  rw [← Nat.pow_mul]
  congr 1
  ring

private theorem endpoint_invoice_le (bill C a h hosts groups radix unit hot rem : ℕ)
    (book : bill ≤ C*(a+1)^3*(h+2*hosts*h+8*hosts*groups*(30*(a+1)^3)+hot*h))
    (alone : C*(a+1)^3*(hot*h+h)≤rem) (coeff : 2*C*(a+1)^3≤unit)
    (fieldsFit : 240*C*(a+1)^6≤unit) (grow : groups≤groups*radix) :
    bill ≤ hosts*h*unit + hosts*(groups*radix)*unit + rem := by
  have hbill := Nat.mul_le_mul_left (hosts*h) coeff
  have low := Nat.mul_le_mul (Nat.mul_le_mul_left hosts grow) fieldsFit
  nlinarith only [book, alone, hbill, low]

theorem endpoint_date_tariff (t f g reset τ B D n ratio saving : ℕ) (den : 0<B)
    (bought : 2*(3*stencilRate G t f g reset+1)≤B) :
    ∀ᶠ h : ℕ in atTop, ∀M i p w : ℕ,
      let J:=Nat.log 2 h/(2*B)
      let S:=stageNumbers G t J f g reset M (tail τ J)
      let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
      let P:=S.endpointBook k (tail τ J) i p f D h n
      let e:=S.endpointExponent k (tail τ J) i p f D h n
      let r:=2^(laneBits P.m h P.b-P.r-e)
      let unit:=endpointFactor ratio*TerminalScale.scale J (6*stencilRate G t f g reset)
      ∀(X : StencilBook.Sources) (chip : Bank) (first base out full : ℕ),
      i≤S.length→p≤h→2^h≤M→w≤ratio*h→X.count.work≤6→
      ∃grouped : 2^P.c=2^P.high*(r*P.M), ∃positive : 0<P.M,
        endpointInvoice P X chip first base out f full (quota t) g (2^n) w r grouped
          (Nat.two_pow_pos _) positive≤S.hostSize i*h*unit+S.hostSize i*(S.groupCount i*S.radix)*unit+
            M/(2^J)^saving := by
  let κ:=stencilRate G t f g reset
  let C:=580000*ratio
  filter_upwards [endpoint_shape_at G t f g reset τ B D n den bought,
    global_control_shared (2*C) 1 (3*κ) 1 saving] with h shapes shared
  intro M i p w J S k P e r unit X chip first base out full date dataSize ambient hardware work
  let A:=stencilCapacity k P.b D n
  obtain ⟨size,wide,cut,hb,inside,aligned,all⟩:=shapes M i p X date dataSize work
  obtain ⟨blocks,axes,degree,b,nb,tb,count,channels⟩:=all
  have pos:0<P.M:=Nat.two_pow_pos _
  have high:S.hostSize i= P.hosts:=rfl
  have radix:0<S.radix:=Nat.two_pow_pos _
  have Hpos:0<P.hosts:=by
    have old:0<M:=(Nat.two_pow_pos h).trans_le ambient
    change 0<M*(2^S.hostGain*S.radix)^i;positivity
  have rows:0<P.rows:=by
    change 0<P.hosts*chunks (2^P.c) (2^Stencil.laneExponent P.c (sharedWidth P) h)
    rw [(Stencil.pitch P.c P.r (sharedWidth P) h).2.2]
    exact Nat.mul_pos Hpos (Nat.two_pow_pos _)
  have cm:P.c≤P.m:=Nat.le_add_right ..
  have book:=suffix_fee P X chip first base out f full (quota t) g full (2^n) h w ratio A hb rows cm wide cut
    (S.endpoint_batch k (tail τ J) i p f D h n) blocks axes degree b nb tb count channels hardware aligned
  refine ⟨aligned,pos,?_⟩
  change endpointInvoice P X chip first base out f full (quota t) g (2^n) w r aligned _ pos≤_
  change endpointInvoice P X chip first base out f full (quota t) g (2^n) w r aligned _ pos≤
      C*(A+1)^3*(h+2*P.hosts*h+8*P.hosts*2^P.c*(30*(A+1)^3)+2^(h/2)*h) at book
  let V:=2^(κ*(J+1))
  have localBound: A+1≤V:=size
  have L:1≤V:=Nat.two_pow_pos _
  have allGroups:2^P.c=S.groupCount i:=S.group_power (tail:=tail τ J) (k:=k) rfl rfl i
  have cube:(A+1)^3≤V^3:=Nat.pow_le_pow_left localBound 3
  have sixth:(A+1)^6≤V^6:=Nat.pow_le_pow_left localBound 6
  have scale6:TerminalScale.scale J (6*κ)=V^6:=scale_power κ J 6
  have local3:(A+1)^3≤V^6:=cube.trans (Nat.pow_le_pow_right L (by decide))
  have F₀:240*C≤endpointFactor ratio:=by dsimp [C,endpointFactor];omega
  have coeff:2*C*(A+1)^3≤unit:=by
    change 2*C*(A+1)^3≤endpointFactor ratio*TerminalScale.scale J (6*κ)
    rw [scale6];exact Nat.mul_le_mul (by omega) local3
  have fieldBill:240*C*(A+1)^6≤unit:=by
    change _≤endpointFactor ratio*TerminalScale.scale J (6*κ)
    rw [scale6];exact Nat.mul_le_mul F₀ sixth
  have af:S.groupCount i≤S.groupCount i*S.radix:=Nat.le_mul_of_pos_right _ radix
  have jL:J≤Nat.log 2 h:=Nat.div_le_self ..
  have residual:=shared J (3*κ*(J+1)) M jL (by simp) ambient
  have mode:2^(3*κ*(J+1))=V^3:=scale_power κ J 3
  rw [mode,pow_one] at residual
  have alone:C*(A+1)^3*((2^(h/2))*h+h)≤M/(2^J)^saving:=by
    have heat:2^(h/2)*h+h≤(2*(h+1))*2^(h/2):=by
      have g1:=Nat.mul_le_mul_left h (show 1≤2^(h/2) from Nat.two_pow_pos _)
      nlinarith only [g1,Nat.zero_le (2^(h/2))]
    calc
      _ ≤ (C*V^3)*((2*(h+1))*2^(h/2)):=Nat.mul_le_mul (Nat.mul_le_mul_left _ cube) heat
      _ = (2*C*(h+1)*V^3)*2^(h/2):=by ring
      _ ≤ _:=residual
  rw [high, ←allGroups]
  apply endpoint_invoice_le _ C A h P.hosts (2^P.c) S.radix unit (2^(h/2)) _ book alone coeff fieldBill
  simpa only [allGroups] using af

end
end Hierarchy.DescentSixParty

end OAI
