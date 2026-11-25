import OAI.Hierarchy.DescentFundedCalendar
import OAI.Hierarchy.DescentMatcherCensusRoom

namespace OAI
/-! # Local digit widths of every actual scheduled funded reset -/
namespace Hierarchy.DescentNamedFundedChart
open DescentDatedAddressBook DescentSixParty DescentSixParty.Chronology DescentCompiler DescentCompiler.TerminalScale
open DescentFundedCensus DescentFallbackPeriod DescentFallbackShapeTable DescentSignedCableCodec DescentSharedCableNames
open Filter LinearAlgebra.SpectralBooks ThreeFlat RouteUnits Expander NonlinearExpanders
open scoped Classical
noncomputable section

/-- Only locally stored fields enter the rooted exceptional query. -/
theorem field_budget_details (D n k Ht cap b U : ℕ) (big : 16≤U) (deg : D+1≤U) (board : 2^n+1≤U)
    (depth : Ht+2≤U) (window : 2^k≤U) (ports : cap+1≤U) (paid : b≤U) :
    max (1+b) (max (((2*k+n+2)+b)*2^k)
      (1+ResetMiddle.fieldWidth D cap n k Ht*inputCount D (2^k) cap n k))≤U^13 ∧
      DescentSignedCableCodec.width D cap ≤ U^2 ∧ ResetMiddle.fieldWidth D cap n k Ht ≤ U^4 ∧
      inputCount D (2^k) cap n k ≤ U^8 :=by
  have pos:0<U:=by omega
  have incr {x y:ℕ} (xy:x≤y) : U^x≤U^y:=Nat.pow_le_pow_right pos xy
  have k':k+1≤U:=(Nat.lt_two_pow_self : k<2^k).trans_le window
  have n':n+1≤U:=(Nat.lt_two_pow_self : n<2^n).trans_le (by omega)
  have row : rows k (2^n)≤U^3 :=by
    calc
      _ ≤ (U*U)*U:=Nat.mul_le_mul (Nat.mul_le_mul k' window) board
      _ = _ :=by ring
  have book : DescentSharedBookScan.width k (2^n) D≤U^7:=by
    calc
      _ ≤ U^3*(U*U^3):=Nat.mul_le_mul row (Nat.mul_le_mul deg row)
      _ = _ :=by ring
  have clog (x : ℕ) : Nat.clog 2 x≤x :=Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  have per : DescentSignedCableCodec.width D cap≤U^2:=by
    have a:=(clog (D+1)).trans deg
    have c:=(clog (cap+1)).trans ports
    change Nat.clog 2 (D+1)+(Nat.clog 2 (cap+1)+(Nat.clog 2 (cap+1)+(Nat.clog 2 (cap+1)+2)))≤_
    calc
      _ ≤ 6*U:=by omega
      _ ≤ U*U:=Nat.mul_le_mul_right U (by omega)
      _ = _ :=by ring
  have single:U≤U^4:=by simpa only [pow_one] using incr (show 1≤4 by decide)
  have shape:2+Nat.clog 2 (rows k (2^n))≤U^4:=by
    have three:1≤U^3:=Nat.one_le_pow _ _ pos
    calc
      _ ≤ 3*U^3:=by have z:=(clog _).trans row;omega
      _ ≤ U*U^3:=Nat.mul_le_mul_right _ (by omega)
      _ = _ :=by ring
  have address : ResetMiddle.senderWidth k n Ht cap≤U^4:=by
    have capBits:=(clog _).trans ports
    unfold ResetMiddle.senderWidth
    calc
      _ ≤ 16*U:=by omega
      _ ≤ U*U:=Nat.mul_le_mul_right _ big
      _ ≤ U^4:=by simpa only [pow_two] using incr (show 2≤4 by decide)
  have packet:ResetMiddle.fieldWidth D cap n k Ht≤U^4:=by
    unfold ResetMiddle.fieldWidth packetField
    exact max_le (max_le (depth.trans single) (max_le (per.trans (incr (by decide))) shape))
      (max_le (k'.trans single) (max_le (n'.trans single) (max_le ((clog _).trans (ports.trans single)) address)))
  have two : U*U≤U^7:=by simpa only [pow_two] using incr (show 2≤7 by decide)
  have used : 2^k*(2*cap)≤U^7:=by
    calc
      _ ≤ 2*(U*U):=by rw [Nat.mul_left_comm];exact Nat.mul_le_mul_left _ (Nat.mul_le_mul window (by omega))
      _ ≤ U*(U*U):=Nat.mul_le_mul_right _ (by omega)
      _ = U^3:=by ring
      _ ≤ _ :=incr (by decide)
  have U7 : U≤U^7:=by simpa only [pow_one] using incr (show 1≤7 by decide)
  have readers : inputCount D (2^k) cap n k≤U^8:=by
    have own:=window.trans U7
    have neighbor:= (Nat.mul_le_mul (show D≤U by omega) window).trans two
    calc
      _ ≤ 4*U^7:=by unfold inputCount;omega
      _ ≤ U*U^7:=Nat.mul_le_mul_right _ (by omega)
      _ = _:=by ring
  have term : ResetMiddle.fieldWidth D cap n k Ht*inputCount D (2^k) cap n k≤U^12:=by
    simpa only [←pow_add] using Nat.mul_le_mul packet readers
  have final : 1+U^12≤U^13:=by
    have positive:0<U^12:=Nat.pow_pos pos
    calc
      _ ≤ 2*U^12:=by omega
      _ ≤ U*U^12:=Nat.mul_le_mul_right _ (by omega)
      _ = _:=by ring
  have first : 1+b≤1+U^12 :=Nat.add_le_add_left (paid.trans (U7.trans (incr (by decide)))) _
  have pair : ((2*k+n+2)+b)*2^k≤U^3:=by
    calc
      _ ≤ (5*U)*U:=Nat.mul_le_mul (by omega) window
      _ ≤ (U*U)*U:=Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
      _ = _:=by ring
  exact ⟨max_le (first.trans final) (max_le (pair.trans (incr (by decide))) ((Nat.add_le_add_left term 1).trans final)),per,packet,readers⟩

theorem field_budget (D n k Ht cap b U : ℕ) (big : 16≤U) (deg : D+1≤U) (board : 2^n+1≤U)
    (depth : Ht+2≤U) (window : 2^k≤U) (ports : cap+1≤U) (paid : b≤U) :
    max (1+b) (max (((2*k+n+2)+b)*2^k)
      (1+ResetMiddle.fieldWidth D cap n k Ht*inputCount D (2^k) cap n k))≤U^13 :=
  (field_budget_details D n k Ht cap b U big deg board depth window ports paid).1

private theorem positive_prefix (l : List ℕ) (i : ℕ) :
    (l.take i).prod≤(l.map (·+1)).prod :=by
  induction l generalizing i with
  | nil=>simp
  | cons a l ih=>
    cases i with
    | zero=>
      have h:=ih 0
      simp only [List.take_zero,List.prod_nil,List.map_cons,List.prod_cons] at *
      exact h.trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos a))
    | succ i=>
      simp only [List.take_succ_cons,List.prod_cons,List.map_cons]
      exact Nat.mul_le_mul (Nat.le_succ a) (ih i)

theorem capPrefix (radix t g J age : ℕ) :
    ((capCalendar radix t g J).take age).prod*256≤ scale J (8+((capPeriod radix t g).map (·+1)).prod) :=by
  let v:=((capPeriod radix t g).map (·+1)).prod
  have all:((capCalendar radix t g J).map (·+1)).prod=v^J:=by
    induction J with
    | zero=>rfl
    | succ J ih=>simp only [capCalendar,List.map_append,List.prod_append,ih,pow_succ']; rfl
  have guard:=(positive_prefix (capCalendar radix t g J) age).trans_eq all
  have lower:v^J≤(2^v)^J:=Nat.pow_le_pow_left Nat.lt_two_pow_self.le J
  calc
    _ ≤ (2^v)^J*2^8:=Nat.mul_le_mul_right _ (guard.trans lower)
    _ = 2^(v*J+8):=by rw [←pow_mul,←pow_add]
    _ ≤ _ := by apply Nat.pow_le_pow_right (by decide);change v*J+8≤(8+v)*(J+1);nlinarith

variable {F:Type} [Field F] (G:PoweredGadget F)

def localRate (t f g reset D n : ℕ) :=
  16+(D+1)+(2^n+1)+(GroupStage.depthBound D n f g+2)+
  (1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g)+
  (8+((capPeriod G.b t g).map (·+1)).prod)+1

theorem scale_at {n d:ℕ} (board:NonlinearExpanders.Graph n d) (t f g reset τ B D : ℕ) (den : 0<B) :
    ∀ᶠ h : ℕ in atTop,∀ M age p e oldPow : ℕ, p≤h →
      let J:=Nat.log 2 h/(2*B)
      let S:=stageNumbers G t J f g reset M (tail τ J)
      let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
      let calendar:=capCalendar G.b S.rounds g S.height
      let old:=previous S k age p D calendar (2^oldPow)
      let mid:=ResetMiddle.fromCalendar S k (tail τ J) age p f D h e oldPow n
        (GroupStage.depthBound D n f g) calendar
      (shape board old mid f g).broadcast≤ scale J (13*localRate G t f g reset D n) ∧
        (setup old mid).precision≤ scale J (localRate G t f g reset D n) :=by
  filter_upwards [census_board_room G t f g reset B den] with h paid
  intro M age p e oldPow hp
  let J:=Nat.log 2 h/(2*B)
  let R:=localRate G t f g reset D n
  let S:=stageNumbers G t J f g reset M (tail τ J)
  let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
  let U:=scale J R
  let A:=1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g
  let q:=8+((capPeriod G.b t g).map (·+1)).prod
  let cap:=((capCalendar G.b t g J).take age).prod*256
  have parts (deg size depth coef limit : ℕ) :
      let total := 16+deg+size+depth+coef+limit+1
      16≤total ∧ deg≤total ∧ size≤total ∧ depth≤total ∧ coef≤total ∧ limit+1≤total := by
    dsimp
    omega
  obtain ⟨big, degree, boardSize, depth, coeff, extent⟩ :=
    parts (D+1) (2^n+1) (GroupStage.depthBound D n f g+2) A q
  have K:k≤A*(J+1):=groupBits_linear ..
  have small : 2^k≤U:=Nat.pow_le_pow_right (by decide) (K.trans (Nat.mul_le_mul_right _ coeff))
  have precision: S.censusBits p≤U:=(paid M (tail τ J) p hp).trans small
  have cap0 : cap≤ scale J q:=capPrefix G.b t g J age
  have cap1:cap+1≤U:=by
    have high:q*(J+1)+1≤R*(J+1):=by
      calc
        _ ≤ q*(J+1)+(J+1) := Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le J)) _
        _ = (q+1)*(J+1) := (Nat.succ_mul ..).symm
        _ ≤ _ := Nat.mul_le_mul_right _ extent
    have s₀ : 0<scale J q:=Nat.two_pow_pos _
    have s₁ : 2*(scale J q)=2^(q*(J+1)+1):=by rw [pow_succ,Nat.mul_comm];rfl
    calc
      _ ≤ 2*scale J q:=by rw [two_mul]; exact Nat.add_le_add cap0 s₀
      _ = _ :=s₁
      _ ≤ U:=Nat.pow_le_pow_right (by decide) high
  have bound_R : R≤U:=(Nat.lt_two_pow_self (n:=R)).le.trans (Nat.pow_le_pow_right (by decide) (Nat.le_mul_of_pos_right _ (Nat.succ_pos J)))
  have field:=field_budget D n k (GroupStage.depthBound D n f g) cap (S.censusBits p) U
    (big.trans bound_R) (degree.trans bound_R) (boardSize.trans bound_R) (depth.trans bound_R)
    small cap1 precision
  refine ⟨field.trans_eq ?_,precision⟩
  change (2^(R*(J+1)))^13=2^((13*R)*(J+1))
  rw [←pow_mul];congr 1;ring

end
end Hierarchy.DescentNamedFundedChart

end OAI
