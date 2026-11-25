import OAI.Hierarchy.DescentOrdinaryBooksAtDate
import OAI.Hierarchy.DescentStageMouthRate
import OAI.Hierarchy.DescentSeedNumberRates

namespace OAI
/-! The four remaining ordinary mouth dimensions are read from the actual calendar book.
The chosen exponent is independent of the tail, the input size and the original graph. -/
namespace Hierarchy.DescentSixParty.Chronology.OrdinaryBooks
open DescentCompiler DescentCompiler.TerminalScale DescentHostDegree
open DescentDatedAddressBook DescentDatedSeedStartup DescentRawCablePanel Filter
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F)

def bookMouthRate (t f g reset : ℕ) :=
  2048+(1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g)+
    (2^packExponent 20 (initialDegreeMax t)+2)+(8+((capPeriod G.b t g).map (·+1)).prod)+
    G.b+G.C+G.k+4

private theorem rate_parts (groupRate degreeLabels capProduct blockBits cost keys : ℕ) :
    let total := 2048+groupRate+(degreeLabels+2)+(8+capProduct)+blockBits+cost+keys+4
    3 ≤ total ∧ 8+capProduct ≤ total ∧ degreeLabels+2 ≤ total ∧
      groupRate+1 ≤ total ∧ blockBits ≤ total ∧ cost+1+keys ≤ total := by
  dsimp only
  omega

theorem mouth_fields_at (op : RotorSpec) (t f g reset τ B drift degreeMax : ℕ) (den : 0 < B) :
    ∀ᶠ h : ℕ in atTop,∀fund i p degree seats (prior : DatePorts),
      let J:=Nat.log 2 h/(2*B)
      let S:=stageNumbers G t J f g reset fund (tail τ J)
      let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
      let L:=atDate G S op g k i p (tail τ J) drift degree h seats prior
      p ≤ h → degree ≤ degreeMax → let limit:=scale J (3*bookMouthRate G t f g reset)
      L.vector.lows ≤ limit ∧ L.bornBook.names ≤ limit ∧ L.bornBook.widths ≤ limit ∧ L.bornBook.bits ≤ limit :=by
  filter_upwards [DescentOperandWidth.issued G drift degreeMax t f g reset τ B den] with h words
  intro fund i p degree seats prior J S k L paid legal limit
  let d:=DonorDate.atDate G S g k i p
  let a:=bookMouthRate G t f g reset
  let u:=scale J a
  obtain ⟨smallRate, capRateBound, degreeRate, groupRateBound, blockRate, borderRate⟩ :=
    rate_parts (1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g)
      (2^packExponent 20 (initialDegreeMax t)) (((capPeriod G.b t g).map (·+1)).prod) G.b G.C G.k
  have mono {b : ℕ} (le : b ≤ a) : scale J b ≤ u:=
    Nat.pow_le_pow_right (n:=2) (by decide) (Nat.mul_le_mul_right (J+1) le)
  have const {b : ℕ} (le : b ≤ a) : b ≤ u :=
    le.trans ((Nat.le_mul_of_pos_right a (Nat.succ_pos J)).trans Nat.lt_two_pow_self.le)
  have two : 2 ≤ u := const ((by decide : 2 ≤ 3).trans smallRate)
  have up : u ≤ u^2:=by simpa only [pow_one] using
    (Nat.pow_le_pow_right (n:=u) (by omega) (show 1 ≤ 2 by decide))
  have lift_ : u^2 ≤ u^3:=Nat.pow_le_pow_right (n:=u) (by omega) (by decide)
  have cube : u^3=limit:=DescentMouthNumericBounds.power_scale J a 3
  have add : u^2+u ≤ u^3:=calc
    _ ≤ 2*u^2:=by omega
    _ ≤ u*u^2:=Nat.mul_le_mul_right _ two
    _ = _:=by ring
  have capped : d.cap ≤ u:=(DescentNamedFundedChart.capPrefix G.b t g J i).trans
    (mono capRateBound)
  have dd : d.degree ≤ initialDegreeMax t :=seed_degree t G.b _
  have exp : packExponent 20 d.degree ≤ packExponent 20 (initialDegreeMax t) :=
    Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.clog_mono_right 2 (Nat.mul_le_mul_left 2 dd))) _
  have label : 2^packExponent 20 d.degree+2 ≤ u:=
    (Nat.add_le_add_right (Nat.pow_le_pow_right (n:=2) (by decide) exp) 2).trans
      (const degreeRate)
  have klen : k ≤ (1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g)*(J+1):=groupBits_linear ..
  have tile : 2^(k+1) ≤ u:=by
    apply Nat.pow_le_pow_right (n:=2) (by decide)
    have rate : (1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g)+1 ≤ a := groupRateBound
    have step:=Nat.mul_le_mul_right (J+1) rate
    rw [Nat.add_mul,Nat.one_mul] at step
    exact (Nat.add_le_add klen (Nat.succ_le_succ (Nat.zero_le J))).trans step
  have layout : 2^(k+1)*(2^packExponent 20 d.degree+2) ≤ u^2:=by
    simpa only [pow_two] using Nat.mul_le_mul tile label
  have clog (n : ℕ) : Nat.clog 2 n ≤ n:=Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  have weight : d.cap*G.b ≤ u^2:=by
    simpa only [pow_two] using Nat.mul_le_mul capped (const blockRate)
  have border : G.C+1+G.k ≤ u := const borderRate
  have word : DescentOperandWidth.recordBits G S k (tail τ J) drift degree p ≤ u:=
    (words fund p degree paid legal).trans (mono smallRate)
  rw [←cube]
  refine ⟨?_,?_,?_,?_⟩
  · change (2^(k+1)-1)*(2^packExponent 20 d.degree+2) ≤ u^3
    exact ((Nat.mul_le_mul_right _ (Nat.sub_le (2^(k+1)) 1)).trans layout).trans lift_
  · change Nat.clog 2 (2^(k+1)*(2^packExponent 20 d.degree+2)) ≤ u^3
    exact (clog _).trans (layout.trans lift_)
  · change Nat.clog 2 (max (d.cap*G.b) (G.C+1+G.k)+1) ≤ u^3
    have peak:=max_le weight (border.trans up)
    exact (clog _).trans ((Nat.add_le_add peak (by omega : 1 ≤ u)).trans add)
  · have code:=record_width G S op g k i p (tail τ J) drift degree h seats prior
    exact (code.2.2.1.trans code.1).le.trans (word.trans (up.trans lift_))

def bookMouthParameters (b : OrdinaryBooks) :=
  mouthValues b.reference.degree b.reference.k b.reference.oldNodes b.reference.capacity b.resolver.nodes
    b.vector.lows b.vector.operands b.bornBook.names b.bornBook.widths b.bornBook.bits

/-- The attained 'atDate' consumes the node and operand dimensions published by its previous
date. The original degree and slot bounds follow directly from its public donor calendar. -/
theorem all_mouth_fields_at (op : RotorSpec) (t f g reset τ B drift driftRate degreeMax : ℕ) (den : 0 < B) :
    ∀ᶠ h : ℕ in atTop,∀fund i p degree seats (prior : DatePorts),
      let J:=Nat.log 2 h/(2*B)
      let S:=stageNumbers G t J f g reset fund (tail τ J)
      let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
      let L:=atDate G S op g k i p (tail τ J) drift degree h seats prior
      p ≤ h → degree ≤ degreeMax → prior.nodes ≤ S.retainedNodes →
      prior.argumentsPerNode ≤ S.retainedArgumentsAt G drift → drift+1 ≤ scale J driftRate →
      ∀j,L.bookMouthParameters j ≤ scale J
        (mouthRate G t f g reset (initialDegreeMax t) driftRate (3*bookMouthRate G t f g reset)) :=by
  filter_upwards [mouth_fields_at G op t f g reset τ B drift degreeMax den] with h shape
  intro fund i p degree seats prior J S k L paid legal old args dr
  have bounds:=shape fund i p degree seats prior paid legal
  exact stage_mouth_values G t f g reset (initialDegreeMax t) J fund (tail τ J) i drift driftRate
    (3*bookMouthRate G t f g reset) L.reference.degree L.reference.k L.reference.oldNodes L.reference.capacity
    L.resolver.nodes L.vector.lows L.vector.operands L.bornBook.names L.bornBook.widths L.bornBook.bits
    (seed_degree t G.b _) rfl old le_rfl le_rfl (max_le args le_rfl) dr
    bounds.1 bounds.2.1 bounds.2.2.1 bounds.2.2.2

end
end Hierarchy.DescentSixParty.Chronology.OrdinaryBooks

end OAI
