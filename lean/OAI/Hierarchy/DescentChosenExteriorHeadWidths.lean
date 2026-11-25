import OAI.Hierarchy.DescentEarlyMatrixBudget
import OAI.Hierarchy.DescentExteriorTableBits
import OAI.Hierarchy.DescentSeedTokenNumbers

namespace OAI
/-! # The exterior table and seed word at the selected first grain -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentCompiler.TerminalScale DescentExteriorShelf DescentSeedRoot Filter
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F)

def headChunk (S : AtomSchedule) := Nat.clog 2 (NativeBranch.localLimit G S)
def headRest (S : AtomSchedule) (k tail : ℕ) := S.groupWidth k tail 0+k-2*headChunk G S
def headGrain (S : AtomSchedule) (k h : ℕ) :=
  let split:=NativeBranch.binLimit (k:=k) S
  let unit:=G.b^(S.rounds*S.height)*G.b
  split*(h/(16*((2^(headChunk G S)*unit)*split)))

variable (rounds f g reset τ B : ℕ)
local notation "κ" => 1+(hostRate rounds reset+capRate G rounds g)*(rounds+1)+8+cutRate rounds f g
local notation "bits" => fun J => groupBits rounds J (hostRate rounds reset) (capRate G rounds g) (cutRate rounds f g)
local notation "sched" => fun J M => stageNumbers G rounds J f g reset M (tail τ J)

theorem chosen_exterior_full_widths (large : 20≤B) (reserve : 2*localSocketRate G rounds g≤τ)
    (budget : 2*(localSocketRate G rounds g+(τ+κ+4))+Nat.clog 2 G.b*(rounds+1)≤B) :
    ∀ᶠ h : ℕ in atTop, let J:=Nat.log 2 h/(2*B)
      ∀M, let S:=sched J M
        let k:=bits J
        let j:=headChunk G S
        let r:=headRest G S k (tail τ J)
        let s:=S.firstWidth G.b (headGrain G S k h)
        16*digitsNeeded s≤h ∧ tableBits j r s≤h/2 ∧ S.copies=2^(j+(j+r)) :=by
  filter_upwards [early_native_packing G rounds f g reset τ B large reserve budget,
    early_matrix_words G rounds f g reset τ B large] with h pack matrix
  intro J M S k j r s
  have native : S.groupWidth k (tail τ J) 0+k=j+(j+r) ∧ S.copies=2^(j+(j+r)) ∧
      2^J≤ s ∧ 16*(2^j*s)≤h ∧ h≤32*(2^j*s) :=pack M
  obtain ⟨shape,copies,young,fits,_⟩:=native
  have squares : 4*((S.groupWidth k (tail τ J) 0+k)*(S.groupWidth k (tail τ J) 0+k)+
    (S.groupWidth k (tail τ J) 0+k)+1)≤h :=(matrix M).2.2
  rw [shape] at squares
  have ps : 0< s :=(Nat.two_pow_pos J).trans_le young
  have digit : digitsNeeded s≤ s :=(Nat.log2_lt ps.ne').mpr Nat.lt_two_pow_self
  have tile : s≤2^j*s :=by simpa only [Nat.one_mul] using Nat.mul_le_mul_right s (Nat.one_le_two_pow (n:=j))
  refine ⟨(Nat.mul_le_mul_left 16 (digit.trans tile)).trans fits,?_,copies⟩
  unfold tableBits DescentExterior.keyBits
  omega

theorem chosen_exterior_head_widths (large : 20≤B) (reserve : 2*localSocketRate G rounds g≤τ)
    (budget : 2*(localSocketRate G rounds g+(τ+κ+4))+Nat.clog 2 G.b*(rounds+1)≤B) :
    ∀ᶠ h : ℕ in atTop, let J:=Nat.log 2 h/(2*B)
      ∀M, let S:=sched J M
        let k:=bits J
        let j:=headChunk G S
        let r:=headRest G S k (tail τ J)
        let s:=S.firstWidth G.b (headGrain G S k h)
        2*digitsNeeded s≤h ∧ tableBits j r s≤h/2 ∧ S.copies=2^(j+(j+r)) :=by
  filter_upwards [chosen_exterior_full_widths G rounds f g reset τ B large reserve budget] with h widths
  intro J M S k j r s
  obtain ⟨seed,table,copies⟩:=widths M
  refine ⟨?_,table,copies⟩
  exact (Nat.mul_le_mul_right (digitsNeeded s) (by decide : 2≤16)).trans seed

end
end Hierarchy.DescentSixParty

end OAI
