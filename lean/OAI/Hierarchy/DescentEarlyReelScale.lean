import OAI.Hierarchy.DescentEarlyReelPrice
import OAI.Hierarchy.DescentEarlyMatrixBudget
import OAI.Hierarchy.DescentOpenSplitStageCount

namespace OAI
/-! # Dated matrix ROM and the price of the original open-port reel at a common height -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentCompiler.TerminalScale DescentExteriorMatrixUpdate
open DescentExteriorShelf DescentStaticWordColumn Catalyst Filter
open scoped Topology
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F)
variable (rounds f g reset τ B : ℕ)
local notation "κ" => 1+(hostRate rounds reset+capRate G rounds g)*(rounds+1)+8+cutRate rounds f g
local notation "bits" => fun J => groupBits rounds J (hostRate rounds reset) (capRate G rounds g) (cutRate rounds f g)
local notation "sched" => fun J M => stageNumbers G rounds J f g reset M (tail τ J)

theorem early_matrix_room (large : 20≤B) :
    ∀ᶠ h : ℕ in atTop, let J:=Nat.log 2 h/(2*B)
      ∀ M, let S:=sched J M
        let d:=S.groupWidth (bits J) (tail τ J) 0+bits J
        S.length*Calendar.stride S (bits J) (tail τ J)≤2^(h/2) ∧
          S.length≤2^(h/2) ∧ 4*(d*d+d+1)≤h := by
  exact early_matrix_words G rounds f g reset τ B large

/-- Price of the very program used by the history, including the sixteenth and seventeenth
exterior columns and the dated matrix register. Both slab and table ceilings are paid here. -/
theorem stage_early_reel_price (large : 20≤B) :
    ∀ᶠ h : ℕ in atTop, let J:=Nat.log 2 h/(2*B)
      ∀M j r s w factor base lo compact : ℕ, let S:=sched J M
        ∀ {cp P : ℕ} (X : Approximation F cp P) (tag : ℕ→Bool) (rot loc : ℕ→ℕ),
          let n:=(Chronology.countDates 0 (Chronology.kindCalendar S.rounds S.height)).length
          let E:=Fintype.card (Port P X.width)
          let code:=SeedNamed.Branch.historyCountReel X S base tag rot loc lo compact
            (bits J) (tail τ J) j r s w
          S.groupWidth (bits J) (tail τ J) 0+bits J=j+(j+r) →
          S.copies=2^(j+(j+r)) → 2^h≤2*(M*S.copies) → 2^J≤ s → w≤factor*h →
          16*(2^j*s)≤h → h≤32*(2^j*s) →
          (4+11*n+Calendar.earlyClock S (bits J) (tail τ J) j r s E+7*names code)*(w+1)*2^J≤
            (262144*(factor+1))*((S.copies*s)*(M+2^J*E)) := by
  filter_upwards [early_matrix_room G rounds f g reset τ B large,eventually_ge_atTop 10] with h matrix hh
  intro J M j r s w factor base lo compact S cp P X tag rot loc n E code shape copies support power arch young packed
  obtain ⟨rom,dates,squares⟩:=matrix M
  rw [shape] at squares
  have look:tableBits j r s≤h/2 := by
    unfold tableBits DescentExterior.keyBits
    omega
  exact SeedNamed.Branch.counted_open_price X S base tag rot loc lo compact _ _ j r s w h M S.copies s
    (2^(Nat.log 2 h/(2*B))) (factor+1) hh support power (by rw [Nat.add_mul];omega)
    copies packed rom dates look

/-- The selected split quantum, initial exterior packing and seventeen-column cost with
the same choice of parameters as the ultimately purchased native epoch. -/
theorem stage_early_native_price (large : 20≤B) (reserve : 2*localSocketRate G rounds g≤τ)
    (budget : 2*(localSocketRate G rounds g+(τ+κ+4))+Nat.clog 2 G.b*(rounds+1)≤B) :
    ∀ᶠ h : ℕ in atTop, let J:=Nat.log 2 h/(2*B)
      ∀M w factor base lo compact : ℕ, let S:=sched J M
        let j:=Nat.clog 2 (NativeBranch.localLimit G S)
        let dim:=S.groupWidth (bits J) (tail τ J) 0+bits J
        let r:=dim-2*j
        let split:=NativeBranch.binLimit (k:=bits J) S
        let U:=G.b^(rounds*J)*G.b
        let p:=split*(h/(16*((2^j*U)*split)))
        let s:=S.firstWidth G.b p
        ∀ {cp P : ℕ} (X : Approximation F cp P) (tag : ℕ→Bool) (rot loc : ℕ→ℕ),
          let n:=(Chronology.countDates 0 (Chronology.kindCalendar S.rounds S.height)).length
          let E:=Fintype.card (Port P X.width)
          let code:=SeedNamed.Branch.historyCountReel X S base tag rot loc lo compact
            (bits J) (tail τ J) j r s w
          2^h≤2*(M*S.copies) → w≤factor*h →
          (4+11*n+Calendar.earlyClock S (bits J) (tail τ J) j r s E+7*names code)*(w+1)*2^J≤
            (262144*(factor+1))*((S.copies*s)*(M+2^J*E)) := by
  filter_upwards [stage_early_reel_price G rounds f g reset τ B large,
    early_native_packing G rounds f g reset τ B large reserve budget] with h fee packing
  intro J M w factor base lo compact S j dim r split U p s cp P X tag rot loc n E code support arch
  obtain ⟨shape,copies,power,low,high⟩:=packing M
  exact fee M j r s w factor base lo compact X tag rot loc shape copies support power arch low high

end
end Hierarchy.DescentSixParty

end OAI
