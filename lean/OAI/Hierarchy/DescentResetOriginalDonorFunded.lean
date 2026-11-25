import OAI.Hierarchy.DescentResetOriginalDonorTariff
import OAI.Hierarchy.DescentResetStemFunded

namespace OAI
/-! # The original donor publisher has a host-linear bill at the clipped reset pitches -/
namespace Hierarchy.DescentResetOriginalDonors
open DescentSIMDLookup DescentDatedAddressBook.CandidateFront DescentStaticWordColumn
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
namespace Panel
variable (P : Panel)
def coefficient (T : ℕ) :=339+4096*volumeFactor P.fields P.blocks+
  (4+P.fields*(4+(2*(T+12)+4)))+7*(15+P.fields*(11+4*(T+12)))

theorem funded (h H T : ℕ) (x : 0<P.blocks) (m : 0<P.lanes) (lane : P.lanes≤h)
    (cast : P.oldBits*P.lanes≤h/2) (window : P.bits*P.lanes≤h/2) (project : (P.bits*P.blocks)*P.lanes≤h/2) :
    P.price T≤P.coefficient T*stemEnvelope h P.sparseHosts H P.groups P.blocks P.lanes P.lanes:=by
  let E:=stemEnvelope h P.sparseHosts H P.groups P.blocks P.lanes P.lanes
  have one : 1≤E:=by
    change 0 < E
    dsimp only [E,stemEnvelope]
    positivity
  have table : (h+1)^3*2^(h/2)≤E:=by dsimp [E,stemEnvelope];omega
  have pow : 2^(P.oldBits*P.lanes)≤E:=(Nat.pow_le_pow_right (by decide) cast).trans
    ((Nat.le_mul_of_pos_left _ (by positivity : 0<(h+1)^3)).trans table)
  have rows : P.sparseHosts*chunks (P.groups*P.blocks) P.lanes≤E:=by dsimp [E,stemEnvelope];omega
  have cost:=volume_paid h P.fields P.sparseHosts H P.groups P.blocks P.bits P.lanes P.lanes x m lane lane window project
  have rom : DescentContactWidthPage.clock P.oldBits P.lanes+7*DescentContactWidthPage.size P.oldBits P.lanes≤339*E:=by
    dsimp [DescentContactWidthPage.clock,DescentContactWidthPage.size,DescentContactWidthPage.words]
    omega
  have score : 4+P.fields*(4+P.sparseHosts*chunks (P.groups*P.blocks) P.lanes*(2*(T+12)+4))
      ≤(4+P.fields*(4+(2*(T+12)+4)))*E:=by
    rw [Nat.add_mul,Nat.mul_assoc P.fields,Nat.add_mul _ _ E]
    apply Nat.add_le_add (Nat.le_mul_of_pos_right _ one)
    apply Nat.mul_le_mul_left
    exact Nat.add_le_add (Nat.le_mul_of_pos_right _ one) ((Nat.mul_le_mul_right _ rows).trans_eq (Nat.mul_comm ..))
  have text :=Nat.le_mul_of_pos_right (7*(15+P.fields*(11+4*(T+12)))) one
  dsimp only [price,coefficient]
  calc
    _ ≤ 339*E+4096*(volumeFactor P.fields P.blocks*E)+(4+P.fields*(4+(2*(T+12)+4)))*E+
        (7*(15+P.fields*(11+4*(T+12))))*E :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add rom (Nat.mul_le_mul_left 4096 cost)) score) text
    _ = _ := by dsimp only [E];ring
end Panel
namespace Layout
variable (L : Layout)
def coefficient (T : ℕ) := L.labels.coefficient T+L.tickets.coefficient T+L.halos.coefficient T

theorem funded (h H T : ℕ) (x : 0<L.blocks) (m : 0<L.lanes) (lane : L.lanes≤h)
    (cast : max L.fieldBits L.metaBits*L.lanes≤h/2)
    (project : max L.selectorBits L.shortBits*(L.blocks+1)*L.lanes≤h/2) :
    L.price T≤L.coefficient T*stemEnvelope h L.sparseHosts H L.groups L.blocks L.lanes L.lanes:=by
  have raw (b) (hb : b≤ max L.fieldBits L.metaBits) := (Nat.mul_le_mul_right L.lanes hb).trans cast
  have src (b) (hb : b≤ max L.selectorBits L.shortBits) : b*L.lanes≤h/2:=
    (Nat.mul_le_mul_right _ (hb.trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)))).trans project
  have dst (b) (hb : b≤ max L.selectorBits L.shortBits) : (b*L.blocks)*L.lanes≤h/2:=
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul hb (Nat.le_succ _))).trans project
  have a:=L.labels.funded h H T x m lane (raw _ (le_max_left ..)) (src _ (le_max_left ..)) (dst _ (le_max_left ..))
  have b:=L.tickets.funded h H T x m lane (raw _ (le_max_left ..)) (src _ (le_max_right ..)) (dst _ (le_max_right ..))
  have c:=L.halos.funded h H T x m lane (raw _ (le_max_right ..)) (src _ (le_max_right ..)) (dst _ (le_max_right ..))
  rw [coefficient,Nat.add_mul,Nat.add_mul]
  exact Nat.add_le_add (Nat.add_le_add a b) c
end Layout
end
end Hierarchy.DescentResetOriginalDonors

end OAI
