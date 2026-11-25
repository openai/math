import OAI.Hierarchy.DescentNamedFundedScale
import OAI.Hierarchy.DescentResetStencilCalendar
import OAI.Hierarchy.DescentIssuedRootWidths

namespace OAI
/-! # Common per-group input and projection width of every calendar reset -/
namespace Hierarchy.DescentDatedAddressBook.ResetMiddle
open DescentSixParty DescentCompiler DescentCompiler.TerminalScale DescentPlainTerminal.Suffix
open DescentNamedFundedChart DescentFallbackPeriod DescentSIMDLookup DescentPackedWalsh
open DescentSixParty.PackedFlow.Padded Filter LinearAlgebra.SpectralBooks ThreeFlat
open scoped Classical
noncomputable section

def rootControlBits (m : ResetMiddle) (cap : ℕ) :=
  let arity := Projected.Receiver.arityLimit m.rootDegree (2^m.rootDepth) cap m.rotorBits m.rootDepth
  max (sharedWidth m.stencil) (max m.stencil.n (max m.projectBits
    (max ((m.signedBits+m.signedBits)*2^m.rootDepth) (max (m.rootField*(arity+1)) arity))))

theorem rootControl_le (m : ResetMiddle) (cap : ℕ) :
    let L:=2^m.rootDepth
    let n:=Projected.Receiver.arityLimit m.rootDegree L cap m.rotorBits m.rootDepth
    ∀ q ∈ [sharedWidth m.stencil,(m.signedBits+m.signedBits)*L,m.projectBits,m.stencil.n,
      m.rootField*(n+1),m.rootField*n,m.signedBits*L,n],q≤rootControlBits m cap := by
  intro L n q member
  have one:=Nat.mul_le_mul_left m.rootField (Nat.le_add_right n 1)
  have pair:=Nat.mul_le_mul_right L (Nat.le_add_right m.signedBits m.signedBits)
  dsimp only [rootControlBits]
  change q ≤ max (sharedWidth m.stencil) (max m.stencil.n (max m.projectBits
    (max ((m.signedBits+m.signedBits)*L) (max (m.rootField*(n+1)) n))))
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  omega

private theorem arity_budget (D n k Ht cap U : ℕ) (big : 16≤U) (deg : D+1≤U)
    (board : 2^n+1≤U) (depth : Ht+2≤U) (window : 2^k≤U) (ports : cap+1≤U) :
    let A:=Projected.Receiver.arityLimit D (2^k) cap n k
    A≤U^8 ∧ fieldWidth D cap n k Ht*(A+1)≤U^13 ∧
    (DescentSignedCableCodec.width D cap+DescentSignedCableCodec.width D cap)*2^k≤U^4 := by
  let L:=2^k
  obtain ⟨_,wire,field,entries⟩:=field_budget_details D n k Ht cap 0 U big deg board depth window ports (Nat.zero_le _)
  have pos:0<U:=by omega
  have up {x y:ℕ} (h:x≤y):U^x≤U^y:=Nat.pow_le_pow_right pos h
  have d:D≤U:=by omega
  have c:cap≤U:=by omega
  have l:L≤U:=window
  have square : U≤U*U := Nat.le_mul_of_pos_left U pos
  have dl:=Nat.mul_le_mul d l
  have lc:=Nat.mul_le_mul l c
  have ll:=Nat.mul_le_mul l l
  have dd:=Nat.mul_le_mul d d
  have unique : 1≤U*U :=Nat.mul_pos pos pos
  have triple : U*(U*U)=U^3:=by ring
  have guard : DescentIssuedRotorRoles.guardInputs D L cap ≤ U^3 := by
    change L+D*L+L*(2*cap)+(L*L+D*(D*6))+1+2 ≤ _
    calc
      _ ≤ 16*(U*U) := by nlinarith only [l,l.trans square,dl,lc,ll,dd,unique]
      _ ≤ U*(U*U) := Nat.mul_le_mul_right _ big
      _ = _ := triple
  have ar : Projected.Receiver.arityLimit D L cap n k ≤ U^8 :=
    max_le (guard.trans (up (by decide))) entries
  have add : Projected.Receiver.arityLimit D L cap n k+1 ≤ U^9 := by
    have power:1≤U^8:=Nat.pow_pos pos
    calc
      _ ≤ 2*U^8 := by omega
      _ ≤ U*U^8 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by ring
  refine ⟨ar,(Nat.mul_le_mul field add).trans_eq (by ring),?_⟩
  calc
    _ ≤ (U^2+U^2)*U := Nat.mul_le_mul (Nat.add_le_add wire wire) window
    _ = 2*U^3 := by ring
    _ ≤ U*U^3 := Nat.mul_le_mul_right _ (by omega)
    _ = _ := by ring

variable {F : Type} [Field F] (G : PoweredGadget F)

/-- The width is uniform in both the old and new lane exponents and does not
depend on the selected layout, host occupancy, or path. -/
theorem root_controls_at (t f g reset τ B D n : ℕ) (den : 0<B) :
    ∀ᶠ h : ℕ in atTop, ∀ M age p e oldPow : ℕ, p≤h →
      let J:=Nat.log 2 h/(2*B)
      let S:=stageNumbers G t J f g reset M (tail τ J)
      let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
      let calendar:=capCalendar G.b S.rounds g S.height
      let mid:=fromCalendar S k (tail τ J) age p f D h e oldPow n (GroupStage.depthBound D n f g) calendar
      rootControlBits mid ((calendar.take age).prod*256) ≤ scale J (13*localRate G t f g reset D n) := by
  filter_upwards [stencil_capacity_at G t f g reset τ B (quota t) D n den] with h capacity
  intro M age p e oldPow hp
  let J:=Nat.log 2 h/(2*B)
  let S:=stageNumbers G t J f g reset M (tail τ J)
  let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
  let Ht:=GroupStage.depthBound D n f g
  let R:=localRate G t f g reset D n
  let U:=scale J R
  let cap:=((capCalendar G.b t g J).take age).prod*256
  let mid:=fromCalendar S k (tail τ J) age p f D h e oldPow n Ht (capCalendar G.b t g J)
  let P:=mid.stencil
  let A:=stencilCapacity k P.b D n
  have trim : S.groupWidth k (tail τ J) (min age S.length)=S.groupWidth k (tail τ J) age := by
    apply congrArg (fun z=>tail τ J+k*z)
    omega
  have quotaPaid:=capacity M (min age S.length) p (Nat.min_le_right ..) hp
  have previous : A+1≤ scale J (stencilRate G t f g reset) := by
    change stencilCapacity k (S.localWalshBits p (S.groupWidth k (tail τ J) (min age S.length)+k) f (quota t)) D n+1≤_ at quotaPaid
    rw [trim] at quotaPaid
    exact quotaPaid
  let q:=8+((capPeriod G.b t g).map (·+1)).prod
  have parts (deg size depth coef limit : ℕ) :
      let rate:=16+deg+size+depth+coef+limit+1
      16≤rate ∧ deg≤rate ∧ size≤rate ∧ depth≤rate ∧ coef+4≤rate ∧ limit+1≤rate := by
    dsimp
    omega
  obtain ⟨large, degree, boardSize, depthRoom, sr, margin⟩ := parts (D+1) (2^n+1) (Ht+2)
    (1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g) q
  have sr' : stencilRate G t f g reset ≤ R := sr
  have ac:A+1≤U:=previous.trans (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ sr'))
  have maxR : R≤U:=(Nat.lt_two_pow_self (n:=R)).le.trans
    (Nat.pow_le_pow_right (by decide) (Nat.le_mul_of_pos_right _ (Nat.succ_pos J)))
  have big:16≤U:=large.trans maxR
  have pos:0<U:=by omega
  change q+1≤R at margin
  have cap0:cap≤ scale J q:=capPrefix G.b t g J age
  have cap1:cap+1≤U:=by
    have mult:=Nat.mul_le_mul_right (J+1) margin
    rw [Nat.add_mul,Nat.one_mul] at mult
    have exp:q*(J+1)+1≤R*(J+1):=
      (Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le J)) _).trans mult
    have small : 1≤ scale J q:=Nat.two_pow_pos _
    calc
      _ ≤ scale J q+scale J q:=Nat.add_le_add cap0 small
      _ = 2^(q*(J+1)+1):=by rw [pow_succ];change 2^(q*(J+1))+2^(q*(J+1))=_;omega
      _ ≤ _:=Nat.pow_le_pow_right (by decide) exp
  have blocks:2^k≤A:=by dsimp [A,stencilCapacity];omega
  have r:P.r=k:=by change S.groupWidth k (tail τ J) age+k-S.groupWidth k (tail τ J) age=k;omega
  have room₀:=arity_budget D n k Ht cap U big
    (degree.trans maxR)
    (boardSize.trans maxR)
    (depthRoom.trans maxR)
    (blocks.trans (by omega)) cap1
  have msmall:P.m≤P.b:=by change P.m≤DescentWalshPrecision.bits P.m f (quota t) (S.censusBits p);unfold DescentWalshPrecision.bits;omega
  have span:P.c+k=P.m:=rfl
  have units:8*(P.b+D+n+7)≤A:=Nat.le_add_left ..
  have coeff:=coefficient P (⟨.lit 0,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,0⟩ : StencilBook.Sources) A
    (by simpa only [r] using blocks) (by omega) (by change D≤A;omega) (by omega) (by change k+P.b+2≤A;omega)
    (by change 2*k+n+2≤A;omega) (by change 1≤A;omega) (by change D≤A;omega)
  have cube:sharedWidth P≤U^5:=by
    calc
      _ ≤ 30*U^3:=coeff.1.trans (Nat.mul_le_mul_left 30 (Nat.pow_le_pow_left ac 3))
      _ ≤ U^2*U^3:=Nat.mul_le_mul_right _ (by nlinarith only [big] : 30≤U^2)
      _ = _:=by ring
  have lift {a b : ℕ} (le:a≤b) : U^a≤U^b:=Nat.pow_le_pow_right pos le
  have cash : (2*k+n+2)*2^k≤U^2 := by
    have left:2*k+n+2≤U:=by omega
    simpa only [pow_two] using Nat.mul_le_mul left (blocks.trans (show A≤U by omega))
  have signed : DescentSignedCableCodec.width D cap*2^k≤U^4 := by
    have m:=Nat.mul_le_mul_right (2^k) (Nat.le_add_right (DescentSignedCableCodec.width D cap) (DescentSignedCableCodec.width D cap))
    exact m.trans room₀.2.2
  have scalar : P.n≤U := by change k+P.b+2≤U;omega
  have nbit:P.n≤U^13 := scalar.trans (by simpa only [pow_one] using (lift (by decide : 1≤13)))
  have done : rootControlBits mid cap≤U^13 := max_le (cube.trans (lift (by decide))) (max_le nbit
    (max_le (max_le (cash.trans (lift (by decide))) (signed.trans (lift (by decide))))
      (max_le (room₀.2.2.trans (lift (by decide))) (max_le room₀.2.1 (room₀.1.trans (lift (by decide)))))))
  apply done.trans_eq
  change (2^(R*(J+1)))^13=2^((13*R)*(J+1))
  rw [←pow_mul];congr 1;ring

end
end Hierarchy.DescentDatedAddressBook.ResetMiddle

end OAI
