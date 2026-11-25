import OAI.Hierarchy.DescentResetRemixTariff
import OAI.Hierarchy.DescentResetEndpointLedger

namespace OAI
/-! # Combined instruction, lookup and clock bill for the actual middle of the physical reset -/
namespace Hierarchy.DescentSixParty
open Filter DescentCompiler DescentCompiler.TerminalScale DescentPackedWalsh DescentDatedAddressBook
open DescentPlainTerminal.Suffix DescentSIMDLookup ProtocolRAM PackedFlow.Padded
noncomputable section

private theorem same_repack (P : StencilBook) (chip : Bank) (first w : ℕ)
    {groups group' r r' : ℕ} (hg : groups=group') (hr : r=r')
    (old : 2^P.c=groups*(r*P.M)) (new : 2^P.c=group'*(r'*P.M))
    (rp : 0<r) (rp' : 0<r') (mp : 0<P.M) :
    repackProgram P chip first r old rp mp w=repackProgram P chip first r' new rp' mp w ∧
      repackTime P chip first r old rp mp=repackTime P chip first r' new rp' mp := by
  subst group' r'
  exact ⟨rfl,rfl⟩

variable {F : Type} [Field F] (G : PoweredGadget F)

/-- Every offset remains arbitrary. The chart comes directly from the same numerical reset
constructor as the true execution on the recorded graph. -/
theorem physical_stencil_tariff (t f g reset τ B D n ratio saving : ℕ) (den : 0<B)
    (bought : 2*(3*stencilRate G t f g reset+1)≤B) :
    ∀ᶠ h : ℕ in atTop, ∀M i p w : ℕ,
      let J:=Nat.log 2 h/(2*B)
      let S:=stageNumbers G t J f g reset M (tail τ J)
      let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
      let P:=S.endpointBook k (tail τ J) i p f D h n
      let e:=S.endpointExponent k (tail τ J) i p f D h n
      let unit:=(remixFactor ratio+endpointFactor ratio)*TerminalScale.scale J (6*stencilRate G t f g reset)
      ∀(calendar : List ℕ) (addr : ℕ→ℕ→Bank) (roster : Bank) (out : ResetOutput)
        (floor : ℕ) (count hub : Bank),
      let a:=PhysicalReset.fromCalendar S k (tail τ J) i G.b p f D h e P.n P.t calendar addr roster out
      i≤S.length→p≤h→2^h≤M→w≤ratio*h→
      ∃sh : a.StencilShape,let txn:=a.stencilPhase sh floor count hub g (2^n)
        (txn.time w+7*DescentStaticWordColumn.names (txn.code w))*w≤
          S.hostSize i*h*unit+S.hostSize i*(S.groupCount i*S.radix)*unit+2*(M/(2^J)^saving) := by
  filter_upwards [endpoint_shape_at G t f g reset τ B D n den bought,
    endpoint_date_tariff G t f g reset τ B D n ratio saving den bought,
    remix_date_tariff G t f g reset τ B D n ratio saving den] with h shape rear front
  intro M i p w J S k P e unit calendar addr roster out floor count hub a age dataSize ambient machine
  let l:=laneBits P.m h P.b
  let X:=ClosedReset.Recorded.stencilSources (a.estimator floor) count hub roster
  have entry:X.count.work≤6:=by rfl
  obtain ⟨_,_,_,positive,inside,aligned,_⟩:=shape M i p X age dataSize entry
  have depth:P.r=k:=by change S.groupWidth k (tail τ J) i+k-S.groupWidth k (tail τ J) i=k;omega
  have packing:e≤l-k:=by change e+P.r≤l at inside;omega
  have sh:a.StencilShape:=PhysicalReset.calendar_shape S k (tail τ J) i G.b p f D h e P.n P.t calendar addr roster out packing
  let R:=a.stencilPhase sh floor count hub g (2^n)
  have chart:R.chart.bits=DescentGLPacked.BankImage.chartBits (((1+D)+P.m)*P.hosts) P.high l P.b:=by
    change DescentGLPacked.BankImage.chartBits _ _ _ _=_
    have split:P.high+l=P.m:=Nat.sub_add_cancel (Nat.min_le_left ..)
    congr 1
    change ((1+D)+(P.high+l))*P.hosts=((1+D)+P.m)*P.hosts
    rw [split]
  obtain ⟨posM,raw⟩:=front M i p w R.chart R.origin R.solve R.fresh R.counts R.peers age dataSize ambient machine chart
  obtain ⟨grouped,batch,price⟩:=rear M i p w R.X R.chip R.first R.base R.bank R.B age dataSize ambient machine entry
  have ratioEq:R.ratio=2^(l-P.r-e):=by rw [depth];rfl
  have groups:R.groups=2^P.high:=by
    apply a.stencil_group_count sh (2^P.high)
    change 2^P.c=2^P.high*(R.ratio*P.M)
    rw [ratioEq]
    exact grouped
  obtain ⟨sameCode,sameTime⟩:=same_repack P R.chip R.first w groups ratioEq R.factor grouped R.ratioPos
    (Nat.two_pow_pos _) batch
  let low:=endpointFactor ratio*TerminalScale.scale J (6*stencilRate G t f g reset)
  let high:=remixFactor ratio*TerminalScale.scale J (5*stencilRate G t f g reset)
  have together:high+low≤unit:=by
    have monotone:TerminalScale.scale J (5*stencilRate G t f g reset)≤ TerminalScale.scale J (6*stencilRate G t f g reset):=
      Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega))
    dsimp only [low,high,unit]
    rw [Nat.add_mul]
    gcongr
  have same:(R.time w+7*DescentStaticWordColumn.names (R.code w))*w=
      remixInvoice P R.chart R.origin R.solve R.fresh R.counts R.peers h w posM+
      endpointInvoice P R.X R.chip R.first R.base R.bank f R.B (quota t) g (2^n) w
        (2^(l-P.r-e)) grouped (Nat.two_pow_pos _) batch:=by
    change repackProgram R.S R.chip R.first R.ratio R.factor R.ratioPos R.batchPos w = _ at sameCode
    change repackTime R.S R.chip R.first R.ratio R.factor R.ratioPos R.batchPos = _ at sameTime
    dsimp only [PackedFlow.ResetMiddle.time,PackedFlow.ResetMiddle.code,remixInvoice,endpointInvoice]
    rw [DescentStaticWordColumn.names_seq]
    rw [sameCode,sameTime]
    have combine (x y u v w : ℕ) : (x+y+7*(u+v))*w=(x+7*u)*w+(y+7*v)*w := by ring
    exact combine _ _ _ _ _
  refine ⟨sh,?_⟩
  change (R.time w+7*DescentStaticWordColumn.names (R.code w))*w≤_
  rw [same]
  have paidH:=Nat.mul_le_mul_left (S.hostSize i*h) together
  have paidG:=Nat.mul_le_mul_left (S.hostSize i*(S.groupCount i*S.radix)) together
  change _≤S.hostSize i*h*high+S.hostSize i*(S.groupCount i*S.radix)*high+_ at raw
  change _≤S.hostSize i*h*low+S.hostSize i*(S.groupCount i*S.radix)*low+_ at price
  have sum_bound (x y a b u v unit tail : ℕ) (hx : x ≤ a*u+b*u+tail)
      (hy : y ≤ a*v+b*v+tail) (rate : u+v ≤ unit) : x+y ≤ a*unit+b*unit+2*tail := by
    have ha := Nat.mul_le_mul_left a rate
    have hb := Nat.mul_le_mul_left b rate
    nlinarith only [hx,hy,ha,hb]
  exact sum_bound _ _ _ _ _ _ _ _ raw price together

end
end Hierarchy.DescentSixParty

end OAI
