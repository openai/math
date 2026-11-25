import OAI.Hierarchy.DescentResetSuffixScale
import OAI.Hierarchy.DescentResetSuffixFee
import OAI.Hierarchy.DescentPhysicalResetReceipt

namespace OAI
/-! # The public reset date selects the post-Walsh pitch and both output widths -/
namespace Hierarchy
open DescentSixParty DescentCompiler DescentCompiler.TerminalScale DescentPlainTerminal.Suffix
open DescentSixParty.PackedFlow.Padded DescentSIMDLookup DescentPackedWalsh
open Filter
noncomputable section

namespace DescentCompiler.AtomSchedule
variable (S : AtomSchedule)

def endpointPlan (k tail age p f D h n : ℕ) : StencilBook :=
  let c:=S.groupWidth k tail age
  let m:=c+k
  let b:=S.localWalshBits p m f (quota S.rounds)
  let l:=laneBits m h b
  ⟨S.hostSize age,c,m,D,D,m-l,1,b,k+b+2,2*k+n+2,Nat.clog 2 (m+2),m+S.censusBits p⟩

def endpointExponent (k tail age p f D h n : ℕ) :=
  let P:=S.endpointPlan k tail age p f D h n
  Stencil.laneExponent P.c (sharedWidth P) h

def endpointBook (k tail age p f D h n : ℕ) : StencilBook :=
  {S.endpointPlan k tail age p f D h n with M:=2^S.endpointExponent k tail age p f D h n}

theorem endpoint_batch (k tail age p f D h n : ℕ) :
    let P:=S.endpointBook k tail age p f D h n
    P.M=2^Stencil.laneExponent P.c (sharedWidth P) h:=rfl

theorem endpoint_fromCalendar (k tail age radix p f D h n : ℕ)
    (calendar : List ℕ) (addr : ℕ→ℕ→ProtocolRAM.Bank) (roster : ProtocolRAM.Bank)
    (out : DescentDatedAddressBook.ResetOutput) :
    let P:=S.endpointBook k tail age p f D h n
    (DescentDatedAddressBook.PhysicalReset.fromCalendar S k tail age radix p f D h
      (S.endpointExponent k tail age p f D h n) P.n P.t calendar addr roster out).successor.middle.stencil=P:=rfl

theorem endpoint_fields (k tail age p f D h n full : ℕ)
    (load : full<2^(S.censusBits p)) :
    let P:=S.endpointBook k tail age p f D h n
    2^P.r*full<2^P.n ∧ P.r<2^P.n ∧ 1<2^P.n ∧
      2*DescentFallbackShapeTable.rows P.r (2^n)≤2^P.t := by
  let c:=S.groupWidth k tail age
  let b:=S.localWalshBits p (c+k) f (quota S.rounds)
  have B:S.censusBits p≤b:=by
    dsimp [b,localWalshBits,DescentWalshPrecision.bits];omega
  have last:2^k*full<2^(k+b+2):=calc
    _ < 2^k*2^b:=Nat.mul_lt_mul_of_pos_left (load.trans_le (Nat.pow_le_pow_right (by decide) B)) (Nat.two_pow_pos _)
    _ ≤ _:=by rw [←pow_add];exact Nat.pow_le_pow_right (by decide) (by omega)
  simp only [endpointBook,endpointPlan,StencilBook.r,Nat.add_sub_cancel_left]
  exact ⟨last,Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_right (by decide) (by omega)),
    Nat.one_lt_pow (by omega) (by decide),Stencil.shape_width ..⟩

end DescentCompiler.AtomSchedule

namespace DescentSixParty.AtomSchedule
export DescentCompiler.AtomSchedule (endpointPlan endpointExponent endpointBook endpoint_batch endpoint_fromCalendar endpoint_fields)
end DescentSixParty.AtomSchedule

namespace DescentSixParty

variable {F : Type} [Field F] (G : PoweredGadget F)

theorem endpoint_shape_at (t f g reset τ B D n : ℕ) (den : 0<B)
    (bought : 2*(3*stencilRate G t f g reset+1)≤B) :
    ∀ᶠ h : ℕ in atTop, ∀M i p : ℕ, ∀X : StencilBook.Sources,
      let J:=Nat.log 2 h/(2*B)
      let S:=stageNumbers G t J f g reset M (tail τ J)
      let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
      let P:=S.endpointBook k (tail τ J) i p f D h n
      let old:=laneBits P.m h P.b
      let e:=S.endpointExponent k (tail τ J) i p f D h n
      let a:=stencilCapacity k P.b D n
      i≤S.length→p≤h→X.count.work≤6→
      a+1≤ scale J (stencilRate G t f g reset) ∧ 4*sharedWidth P≤h ∧
      P.levels+P.total≤h/2 ∧ 0<P.b ∧ e+P.r≤old ∧
      2^P.c=(2^P.high)*(2^(old-P.r-e)*P.M) ∧
      2^P.r≤a ∧ P.m≤a ∧ P.degree≤a ∧ P.b≤a ∧ P.n≤a ∧ P.t≤a ∧ X.count.work≤a ∧ P.maxPorts≤a := by
  filter_upwards [stencil_capacity_at G t f g reset τ B (quota t) D n den,
    stencil_width_at (stencilRate G t f g reset) B den bought,
    eventually_actual_width G t f g reset B (quota t) τ] with h capacity width levels
  intro M i p X J S k P old e a date dataSize work
  have r:P.r=k:=by change (S.groupWidth k (tail τ J) i+k)-S.groupWidth k (tail τ J) i=k;omega
  have span:P.c+k=P.m:=rfl
  have small:P.m≤P.b:=by
    change P.m≤DescentWalshPrecision.bits P.m f (quota t) (S.censusBits p)
    unfold DescentWalshPrecision.bits;omega
  have one:0<P.b:=by change 0<DescentWalshPrecision.bits _ _ _ _;unfold DescentWalshPrecision.bits;omega
  have ac:=capacity M i p date dataSize
  change a+1≤ scale J (stencilRate G t f g reset) at ac
  have blocks:2^P.r≤a:=by dsimp [a,stencilCapacity];rw [r];omega
  have extra : 8*(P.b+D+n+7)≤a:=Nat.le_add_left ..
  have linear : P.b+D+n+7≤a:=(Nat.le_mul_of_pos_left _ (by decide : 0<8)).trans extra
  have md:P.degree=D:=rfl
  have slots:P.maxPorts=D:=rfl
  have nb:P.n=k+P.b+2:=rfl
  have tb:P.t=2*k+n+2:=rfl
  have cm:P.c≤P.m:=by omega
  have all:=coefficient P X a blocks (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have wide:4*sharedWidth P≤h:=(Nat.mul_le_mul_left 4 all.1).trans (width a ac)
  have height:=pitch_inside P h one cm wide
  change e+P.r≤old at height
  have jL:J≤Nat.log 2 h:=Nat.div_le_self ..
  have tailBudget:tail τ J≤τ*(Nat.log 2 h+1)^2:=Nat.mul_le_mul_left _ ((Nat.succ_le_succ jL).trans (by nlinarith))
  have wroom: P.m+Nat.clog 2 (P.m+2)+8*P.b≤h/2:=(levels M (tail τ J) i p dataSize tailBudget date).2.2
  have mass:S.censusBits p≤P.b:=by change _≤DescentWalshPrecision.bits _ _ _ _;unfold DescentWalshPrecision.bits;omega
  have cut:P.levels+P.total≤h/2:=by change Nat.clog 2 (P.m+2)+(P.m+S.censusBits p)≤_;omega
  have oldLe:old≤P.m:=Nat.min_le_left ..
  have orig:P.high=P.m-old:=rfl
  have rep:2^P.c=2^P.high*(2^(old-P.r-e)*P.M):=by
    change 2^P.c=2^P.high*(2^(old-P.r-e)*2^e)
    rw [←pow_add,←pow_add];congr 1;omega
  exact ⟨ac,wide,cut,one,height,rep,blocks,by omega,by omega,by omega,by omega,by omega,by omega,by omega⟩

end DescentSixParty
end
end Hierarchy

end OAI
