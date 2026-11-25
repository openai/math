import OAI.Hierarchy.DescentResetMiddleCalendar
import OAI.Hierarchy.DescentIssuedRootWidths

namespace OAI
/-! # The address range of the actual reset root dictionary at the selected lane count -/
namespace Hierarchy.DescentDatedAddressBook.ResetMiddle
open DescentSixParty DescentCompiler DescentFallbackPeriod DescentFallbackPeriod.Projected DescentSIMDLookup
open DescentPackedWalsh DescentSixParty.Chronology
noncomputable section

theorem page_arity (D cap n k : ℕ) (p : RootPage k (2^n)) :
    rootArity D cap n k p≤Receiver.arityLimit D (2^k) cap n k := by
  rcases p with ⟨s,(⟨t,j⟩|q)⟩
  · cases j with
    | inl flag=>
      cases flag
      · exact (Nat.le_add_right ..).trans ((Nat.le_add_right ..).trans (le_max_left ..))
      · have lo : 3≤DescentIssuedRotorRoles.guardInputs D (2^k) cap:=by unfold DescentIssuedRotorRoles.guardInputs;omega
        exact lo.trans (le_max_left ..)
    | inr _=>exact le_max_left ..
  · exact le_max_right ..

def bankBound (h H G M : ℕ) :=
  let P:=2^h
  (1+(P*(2*P)+P+2^(Nat.clog 2 (H*chunks G M))))+max P (P+P+2^(Nat.clog 2 H)+2^(Nat.clog 2 H))

theorem law_bounded (D cap n k H G M b prior levels total h : ℕ) (lane : 0<M) (field : 0<b)
    (operands : b*(Receiver.arityLimit D (2^k) cap n k+1)*M≤h)
    (cast : prior*M≤h) (reserves : levels+total≤h) :
    lawWidth D cap n k H G M b prior levels total≤bankBound h H G M := by
  let A:=Receiver.arityLimit D (2^k) cap n k
  have room : A≤h:=calc
    A≤A+1 :=Nat.le_succ _
    _≤b*(A+1):=Nat.le_mul_of_pos_left _ field
    _≤b*(A+1)*M:=Nat.le_mul_of_pos_right _ lane
    _≤h:=operands
  have words : ∀p:RootPage k (2^n),
      let N:=rootArity D cap n k p
      N*(2*2^((b*N+b)*M))+2^(b*N*M)+2^(Nat.clog 2 (H*chunks G M))≤
        2^h*(2*2^h)+2^h+2^(Nat.clog 2 (H*chunks G M)) :=by
    intro p
    let N:=rootArity D cap n k p
    have small : N≤A:=page_arity ..
    have Nroom : N≤2^h:=(small.trans room).trans Nat.lt_two_pow_self.le
    have key : (b*N+b)*M≤h:=by
      calc
        _ ≤ (b*A+b)*M :=Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.mul_le_mul_left _ small) _)
        _ = b*(A+1)*M :=by ring
        _ ≤ h :=operands
    have one : b*N*M≤h:=(Nat.mul_le_mul_right _ (Nat.le_add_right ..)).trans key
    exact Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul Nroom (Nat.mul_le_mul_left 2
      (Nat.pow_le_pow_right (by decide) key))) (Nat.pow_le_pow_right (by decide) one)) _
  have count := Finset.sup_le (fun p (_ : p∈(Finset.univ : Finset (RootPage k (2^n))))=>words p)
  have lvl : levels≤h:=(Nat.le_add_right ..).trans reserves
  have shared : DescentReservationHeader.reserveEntries H levels total≤
      2^h+2^h+2^(Nat.clog 2 H)+2^(Nat.clog 2 H) :=by
    exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add (Nat.pow_le_pow_right (by decide) lvl)
      (Nat.pow_le_pow_right (by decide) reserves)) _) _
  exact Nat.add_le_add (Nat.add_le_add_left count 1)
    (max_le_max (Nat.pow_le_pow_right (by decide) cast) shared)

variable (S : AtomSchedule) (k tail age p f D h e previous n Ht : ℕ) (calendar : List ℕ)
local notation "a₀" => fromCalendar S k tail age p f D h e previous n Ht calendar
local notation "q₀" => List.prod (calendar.take age)*256
local notation "args" => Receiver.arityLimit D (2^k) q₀ n k

theorem calendar_law_bound
    (key : (a₀).rootField*(args+1)*(a₀).rootLanes≤h/2)
    (order : (a₀).stencil.n*(a₀).rootLanes≤h/2) :
    (a₀).rootLawWidth≤bankBound h (a₀).rootHosts (a₀).rootGroups (a₀).rootLanes :=by
  let m:=S.groupWidth k tail age+k
  let b:=S.localWalshBits p m f (quota S.rounds)
  have pos : 0<fieldWidth D q₀ n k Ht:=by unfold fieldWidth;omega
  have fit : (k+b+2)*2^e≤h:=order.trans (Nat.div_le_self ..)
  have prior : k+b+2≤h:=(Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)).trans fit
  have level : Nat.clog 2 (m+2)≤ m+2:=Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  have bank : Nat.clog 2 (m+2)+(m+S.censusBits p)≤h := by
    dsimp [b,AtomSchedule.localWalshBits,DescentWalshPrecision.bits] at prior
    omega
  exact law_bounded D q₀ n k _ _ _ _ _ _ _ h (Nat.two_pow_pos _) pos
    (key.trans (Nat.div_le_self ..)) fit bank

end
end Hierarchy.DescentDatedAddressBook.ResetMiddle

end OAI
