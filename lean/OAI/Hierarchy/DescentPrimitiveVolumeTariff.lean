import OAI.Hierarchy.DescentPlacedInvoiceVolume
import OAI.Hierarchy.DescentPrimitiveBirthTariff
import OAI.Hierarchy.DescentPrimitiveCheckpointTariff

namespace OAI
/-! # Clipped lookup and actual row prices for the reset primitive and donor-control phases -/
namespace Hierarchy.DescentPlacedInvoiceVolume
open DescentSIMDLookup DescentResetRetainedSetup
noncomputable section

theorem half_table {w h T : ℕ} (cells : w≤h/2) (room : (h+1)^3*2^(h/2)≤T) : 2^w≤T:=
  (Nat.pow_le_pow_right (by decide) cells).trans ((Nat.le_mul_of_pos_left _ (by positivity : 0<(h+1)^3)).trans room)

def printed (c : ℕ) :=4+10*(c*2)+7*(15*(c*2+1))
private theorem mounted (c a M h T : ℕ) (width : a*M≤h/2) (room : (h+1)^3*2^(h/2)≤T) :
    DescentPrimitiveBirth.Layout.mountBill (c*(2*2^(a*M)))≤printed c*(T+1):=by
  have f:=half_table width room
  unfold DescentPrimitiveBirth.Layout.mountBill
  apply le_trans (b:=4+10*(c*(2*T))+7*(15*(c*(2*T)+1)))
  · gcongr
  · unfold printed;ring_nf;omega

def controlFactor (K U : ℕ) := printed K+
  ((4+K*(4+2*(U+12)+4))+7*(15+K*(11+4*(U+12))))+
  (109+K*2048*5)+printed (2*K)

theorem control (s : DescentRetainedControl.Layout) (h T U : ℕ)
    (prev : 0<s.oldLanes) (first : s.oldLanes≤h) (last : s.lanes≤h)
    (input : s.rootWidth*s.oldLanes≤h/2) (gate : s.aperture*s.lanes≤h/2)
    (intermediate : s.selectorBits*s.oldLanes≤h/2)
    (from_ : s.hosts*chunks s.groups s.oldLanes≤T) (to_ : s.hosts*chunks s.groups s.lanes≤T)
    (room : (h+1)^3*2^(h/2)≤T) : s.invoice U≤controlFactor s.targets U*(T+1):=by
  have a:=mounted s.targets s.rootWidth s.oldLanes h T input room
  have b:=mounted (2*s.targets) s.aperture s.lanes h T gate room
  have c:Layout.stripCharge s.hosts s.groups s.oldLanes s.lanes s.selectorBits≤2048*(4*T+1):=by
    have d:=(pieces_price s.groups s.oldLanes s.lanes s.selectorBits h prev first last intermediate).trans (Nat.mul_le_mul_left _ room)
    unfold Layout.stripCharge Overlap.rows
    omega
  unfold DescentRetainedControl.Layout.invoice
  apply le_trans (b:=printed s.targets*(T+1)+
    ((4+s.targets*(4+T*(2*(U+12)+4)))+7*(15+s.targets*(11+4*(U+12))))+
    (109+s.targets*(2048*(4*T+1)))+printed (2*s.targets)*(T+1))
  · dsimp only
    refine Nat.add_le_add (Nat.add_le_add (Nat.add_le_add a ?_) ?_) b
    · gcongr; exact from_
    · exact Nat.add_le_add_left (Nat.mul_le_mul_left _ c) _
  · unfold controlFactor;ring_nf;omega

def birthFactor (z : DescentPrimitiveBirth.Layout) :=
  printed z.nodes+stemFactor z.batch.fields z.placement.blocks z.rootBudget+
    suffixFactor z.placement.shapes z.batch.fields z.placement.blocks+printed z.gates

theorem birth (z : DescentPrimitiveBirth.Layout) (h T : ℕ) (r : ScanRoom z.placement z.batch h T)
    (guard : (z.rootBits*z.stop)*z.sourceLanes≤h/2) (gate : z.aperture*z.placement.lanes≤h/2) :
    z.invoice≤birthFactor z*(T+1):=by
  have a:=mounted z.nodes (z.rootBits*z.stop) z.sourceLanes h T guard r.tables
  have b:=mounted z.gates z.aperture z.placement.lanes h T gate r.tables
  have c:=placement z.placement z.batch h T z.rootBudget r
  unfold DescentPrimitiveBirth.Layout.invoice birthFactor
  rw [show printed z.nodes+stemFactor z.batch.fields z.placement.blocks z.rootBudget+
      suffixFactor z.placement.shapes z.batch.fields z.placement.blocks+printed z.gates=
      printed z.nodes+(stemFactor z.batch.fields z.placement.blocks z.rootBudget+
      suffixFactor z.placement.shapes z.batch.fields z.placement.blocks)+printed z.gates by omega]
  simpa only [Nat.add_mul] using Nat.add_le_add (Nat.add_le_add a c) b

def finalFactor (N X U : ℕ) :=
  8+10*4+(4+X*N*(4+(2*(3*U+26)+4)))+(4+10*(N+1)+(4+X*(4+2*(1+18*N)+4)))+
  7*(15*(4+2)+(15+X*N*(11+4*(3*U+26)))+(15*(N+1+1)+(15+X*(11+4*(1+18*N)))))

theorem checkpoint (v : DescentResetPrimitiveCheckpoint.Shape) (h T U : ℕ)
    (raw : v.rawBits*v.chart.lanes≤h/2) (one : v.chart.lanes≤h/2)
    (merge : (v.chart.bits*v.chart.nodes+v.chart.bits)*v.chart.lanes≤h/2)
    (rows : v.chart.rows≤T) (room : (h+1)^3*2^(h/2)≤T) :
    v.clockBound U+7*v.nameBound U≤finalFactor v.chart.nodes v.chart.blocks U*(T+1):=by
  let N:=v.chart.nodes
  let X:=v.chart.blocks
  have stored:DescentResetPrimitivePage.words v.rawBits v.chart.lanes≤4*T:=by
    unfold DescentResetPrimitivePage.words
    have a:=half_table raw room
    have b:=half_table one room
    omega
  have dict:v.chart.dictionary≤(N+1)*T:=Nat.mul_le_mul_left _ (half_table merge room)
  unfold DescentResetPrimitiveCheckpoint.Shape.clockBound DescentResetPrimitiveCheckpoint.Shape.nameBound
    DescentResetPrimitivePage.clock DescentResetPrimitivePage.size DescentResetPrimitiveCheckpoint.Shape.operandWork
  apply le_trans (b:=8+10*(4*T)+(4+X*N*(4+T*(2*(3*U+26)+4)))+
    (4+10*((N+1)*T)+(4+X*(4+T*(2*(1+18*N)+4))))+
    7*(15*(4*T+2)+(15+X*N*(11+4*(3*U+26)))+(15*((N+1)*T+1)+(15+X*(11+4*(1+18*N))))))
  · dsimp only [N,X] at *;gcongr
  · change _≤finalFactor N X U*(T+1);unfold finalFactor;ring_nf;omega

end
end Hierarchy.DescentPlacedInvoiceVolume

end OAI
