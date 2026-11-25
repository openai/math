import OAI.Hierarchy.TaggedWideCalendarShelf
import OAI.Hierarchy.TaggedWireTurnCost
import OAI.Hierarchy.TaggedWireRoleSemantics
import OAI.Hierarchy.ProbeFixedWideTerminal
import OAI.Hierarchy.TaggedWideControl

namespace OAI
/-! # The native terminal comparator on every actual paid site -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open AdaptiveProbe ProbeStage CoreBoard HistoryRoles RoleProgram WireTelescope Tagged WideControlJoin
open ThreeFlat Routing Filter Real
open scoped Classical BigOperators
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
local notation "d" => 2^v.W
local notation "shelfSlots" => WordSeats.room (k:=k) (attempts:=v.wideJobs) v.sampler

def wideShelfRoles := 2*WordSeats.fixedRoom (k:=k) (attempts:=v.wideJobs) v.sampler

theorem wide_shelf_role_fit (h : ℕ) (u : Public v.sampler h v.W k v.wideJobs) (out : Bool) :
    RoleProgram.labelled v.sampler out u<2^TurnShelf.exponent v.wideShelfRoles := by
  have small:=code_bound v.sampler u
  have positive : 0<v.wideShelfRoles:=by unfold wideShelfRoles WordSeats.fixedRoom;omega
  apply lt_trans ?_ (TurnShelf.dyadic_room v.wideShelfRoles positive).1
  unfold RoleProgram.labelled wideShelfRoles WordSeats.fixedRoom
  cases out <;> simp only [Bool.toNat_false,Bool.toNat_true] <;> omega

theorem wide_terminal_site_price {κ A : ℝ} (K : ℕ) (positive : 0<K) :
    ∃C:ℝ,0<C ∧ ∀ᶠx : WideParent κ A in WideParent.large κ A,
      let sites:=siteLast x.h d k+1
      let roles:=TurnShelf.exponent v.wideShelfRoles
      let bits:=TurnShelf.exponent (K*x.w)
      ∀{E Q Data : Type} [Fintype E] [Fintype Q] [Fintype Data] (G : Gate) (base : ℕ)
        (operand : Fin sites→TurnShelf.Aperture roles bits→Data⊕Bool),
        let net:=fun i : Fin sites=>G.shelfNet (F:=F) (E:=E) (Q:=Q) (slots:=shelfSlots) base i (operand i)
        ((∑ i : Fin sites, ((net i).cells + (net i).internal) : ℕ) : ℝ)≤C*((2:ℝ)^x.h*x.w*log (x.h:ℝ)) := by
  have rolePos : 0<v.wideShelfRoles:=by unfold wideShelfRoles WordSeats.fixedRoom;omega
  obtain ⟨C,Cpos,bill⟩:=TurnShelf.work_bound F A shelfSlots v.wideShelfRoles K (siteFactor d k) positive rolePos
  have high : Tendsto (WideParent.h (κ:=κ) (A:=A)) (WideParent.large κ A) atTop:=tendsto_comap
  refine ⟨C,Cpos,?_⟩
  filter_upwards [high.eventually bill] with x price
  intro sites roles bits E Q Data fE fQ fD G base operand net
  let n:=TurnShelf.network F shelfSlots roles bits
  have same (i : Fin sites) : (net i).cells+(net i).internal=n.cells+n.internal := by
    rw [show (net i).cells+(net i).internal=_ from WideHost.localFamily_size ..]
    simp [n]
  have total : (∑ i : Fin sites, ((net i).cells + (net i).internal)) =
      sites * (n.cells + n.internal) := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      (Finset.sum_const_nat (s := Finset.univ) (fun i _ => same i))
  rw [total]
  exact price x.w sites x.formats.2.1 x.property.1.2.2 (site_count x.h d k Nat.one_le_two_pow)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
