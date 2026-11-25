import OAI.Hierarchy.DescentTerminalRouteInvoice
import OAI.Hierarchy.DescentNativeSocketScale

namespace OAI
/-! # Complete mixed-radix terminal book at the actual joint height -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentCompiler.TerminalScale DescentTerminalLocalPortBook Filter
open scoped Classical
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F)

def bookRate (t f g reset τ : ℕ) :=
  3*((τ+(1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g)+4)+(localSocketRate G t g+Nat.clog 2 G.b*(t+1)))+8

/-- This book uses the authentic effective number of ordinary vertices,
all formal operands, and all possible distinct names at a measured home.
The public modulus may be enlarged before `h` or the payload is selected. -/
theorem terminal_book_and_route_room (t f g reset τ B : ℕ) (pos : 0<B)
    (budget : 2*bookRate G t f g reset τ≤B) :
    ∀ᶠ h : ℕ in atTop, let J:=Nat.log 2 h/(2*B)
      ∀ M : ℕ, let S:=stageNumbers G t J f g reset M (tail τ J)
      let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
      let V:=S.groupCount S.length*2^k
      let A:=NativeBranch.localLimit G S
      let W:=NativeBranch.binLimit (k:=k) S
      let q:=2^Nat.clog 2 A*(G.b^(t*J)*G.b)
      Book.fixedWords V A W q ≤ 2^(h/2) := by
  let P:=τ+(1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g)+4
  let L:=localSocketRate G t g
  let Q:=L+Nat.clog 2 G.b*(t+1)
  let σ:=bookRate G t f g reset τ
  have bought : 2*(0+0+σ)≤B := by simpa using budget
  filter_upwards [eventually_home 0 0 σ B pos bought] with h roomy
  dsimp only
  intro M
  let J:=Nat.log 2 h/(2*B)
  let S:=stageNumbers G t J f g reset M (tail τ J)
  let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
  let V:=S.groupCount S.length*2^k
  let A:=NativeBranch.localLimit G S
  let W:=NativeBranch.binLimit (k:=k) S
  let q:=2^Nat.clog 2 A*(G.b^(t*J)*G.b)
  let n:=scale J (P+Q)
  have sizes:=native_socket_scale G t J f g reset M τ
  have low : A≤ scale J L:=sizes.2.1.trans sizes.2.2.1
  have web : W≤ scale J P:=sizes.2.2.2.2.1
  have sub : V≤W := by change V≤3*V+6;omega
  have q_le : q≤ scale J Q:=sizes.2.2.2.2.2.2.1
  have lq : scale J L≤ scale J Q := Nat.pow_le_pow_right (by decide)
    (Nat.mul_le_mul_right _ (Nat.le_add_right ..))
  have n_eq : n=scale J P*scale J Q := by simp [n,scale,Nat.add_mul,pow_add]
  have pp : 0< scale J P:=Nat.two_pow_pos _
  have pl : 0< scale J Q:=Nat.two_pow_pos _
  have w_le : W≤n := by rw [n_eq];exact web.trans (Nat.le_mul_of_pos_right _ pl)
  have a_le : A≤n := by rw [n_eq];exact (low.trans lq).trans (Nat.le_mul_of_pos_left _ pp)
  have m_le : V*A≤n := by rw [n_eq];exact Nat.mul_le_mul (sub.trans web) (low.trans lq)
  have fullBin : q≤n := by rw [n_eq];exact q_le.trans (Nat.le_mul_of_pos_left _ pp)
  have limit : 256*(n*n*n)≤ scale J σ := by
    have e : 8+(((P+Q)*(J+1)+(P+Q)*(J+1))+(P+Q)*(J+1))≤(3*(P+Q)+8)*(J+1) := by nlinarith
    change 2^8*((2^((P+Q)*(J+1))*2^((P+Q)*(J+1)))*2^((P+Q)*(J+1)))≤2^((3*(P+Q)+8)*(J+1))
    simp only [←pow_add]
    exact Nat.pow_le_pow_right (by decide) e
  have cost:=roomy.2 0 1 (256*(n*n*n)) (by simp [tail]) (by simp) limit
  exact (Book.fixed_envelope V A W q n (sub.trans w_le) m_le a_le w_le fullBin (Nat.two_pow_pos _)).trans
    (Nat.pow_le_pow_right (by decide) (by omega))

theorem terminal_book_room (t f g reset τ B : ℕ) (pos : 0<B)
    (budget : 2*bookRate G t f g reset τ≤B) :
    ∀ᶠ h : ℕ in atTop, let J:=Nat.log 2 h/(2*B)
      ∀ M : ℕ, let S:=stageNumbers G t J f g reset M (tail τ J)
      let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
      let V:=S.groupCount S.length*2^k
      let A:=NativeBranch.localLimit G S
      let W:=NativeBranch.binLimit (k:=k) S
      Book.lookupWords V A W ≤ 2^(h/2) := by
  filter_upwards [terminal_book_and_route_room G t f g reset τ B pos budget] with h room
  dsimp only
  intro M
  exact (Book.lookup_le_fixed ..).trans (room M)

end
end Hierarchy.DescentSixParty

end OAI
