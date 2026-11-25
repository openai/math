import OAI.Hierarchy.DescentOriginalHostPurchase
import OAI.Hierarchy.DescentStageDateResources
import OAI.Hierarchy.DescentTerminalHostWords

namespace OAI
/-! # Startup cost and physical word fields at the compiler's common cutoff -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentCompiler.TerminalScale Filter
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F)

/-- Uniform in the input, the last populated RAM address and the number of original sites. -/
def StartupWordsAt (t f g reset W τ β h : ℕ) : Prop :=
  ∀ M last : ℕ, 2^h≤M → M≤(2^h)^2 → (2*last+7)*h≤W*h →
    let J:=Nat.log 2 h/(2*β)
    let S:=stageNumbers G t J f g reset M (tail τ J)
    let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
    HostWordRoom G S k (tail τ J) (headGrain G S k h) (headChunk G S) W h

/-- The actual machine tariff, startup widths and register conditions may be
purchased before the input. Every witness uses the same word and the same reset circuit. -/
theorem cofinal_startup_price (op : RotorSpec) (t f g reset n depth C drift limit W : ℕ)
    (branch : G.b≤2^(capRate G t g)) (ratio : 9≤W) :
    ∃τ₀ : ℕ, ∀τ≥τ₀, ∃β₀ : ℕ, ∀β≥β₀, ∀ᶠ h : ℕ in atTop,
      OriginalPurchaseAt G op t f g reset n depth C drift limit W τ β h ∧
      StartupWordsAt G t f g reset W τ β h ∧
      ∀M : ℕ, 2^h≤M → M≤(2^h)^2 → StageDateResources G op t f g reset drift limit n depth τ β h M (W*h) :=by
  obtain ⟨tPrice,bPrice,buy⟩:=original_purchase G op t f g reset n depth C drift limit W branch (by omega)
  let a:=localSocketRate G t g
  refine ⟨max tPrice (2*a),?_⟩
  intro τ bought
  have tPaid : tPrice≤τ := (le_max_left ..).trans bought
  have reserve : 2*a≤τ := (le_max_right ..).trans bought
  obtain ⟨bDates,datesAt⟩:=cofinal_stage_date_resources G op t f g reset drift limit n depth τ
  let packing:=2*(a+(τ+groupRate G t f g reset+4))+Nat.clog 2 G.b*(t+1)
  refine ⟨max (max 20 packing) (max (bPrice τ) bDates),?_⟩
  intro β paid
  have size : max 20 packing≤β := (le_max_left ..).trans paid
  have prices : max (bPrice τ) bDates≤β := (le_max_right ..).trans paid
  have large : 20≤β := (le_max_left ..).trans size
  have enough : packing≤β := (le_max_right ..).trans size
  filter_upwards [buy τ β tPaid ((le_max_left ..).trans prices),
    terminal_host_words G t f g reset τ β large reserve enough,
    datesAt β ((le_max_right ..).trans prices)] with h actual words dates
  exact ⟨actual,fun M last low high budget=>words M W last low high budget,
    fun M low high=>dates M (W*h) low high (Nat.mul_le_mul_right h ratio)⟩

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
