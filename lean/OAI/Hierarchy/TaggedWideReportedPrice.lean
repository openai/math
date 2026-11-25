import OAI.Hierarchy.TaggedWideSettledRows
import OAI.Hierarchy.TaggedWideReportGrouping
import OAI.Hierarchy.TaggedShorterPrune
import OAI.Hierarchy.ProbeOuterLedger
import OAI.Hierarchy.ProbeFinalRoutes

namespace OAI
/-! # Pricing the native group's actual transported units from the outer ledger -/

noncomputable section
namespace Hierarchy.Tagged.WideStack
open TaggedShorterBudget ProtocolRAMReportedPorts AdaptiveProbe
open scoped Classical BigOperators

def rowRatio {rows : ℕ} (report : Fin rows → ProtocolRAMEmit.Row) (w : ℕ) (i : Fin rows) : ℝ :=
  (report i).width/(w:ℝ)

/-- Apply the uniform dyadic menu directly to a native report. In
particular its budget argument is the result of
`ProtocolRAM.RouteSettlement.report_termBudget` on the actual final emitter. -/
theorem reported_menu {u : ℝ→ℝ} {A ε p q Q σ L δ η ξ C : ℝ}
    (purchase : Choice u A ε p q Q σ L δ η ξ) (hC : 0≤C) :
    ∃ m : ℕ, ∀ a∈Set.Icc 1 A, ∀ {rows groups : ℕ} (report : Fin rows → ProtocolRAMEmit.Row)
      (stage : Fin rows → ℕ) (t len : Fin rows → ℝ) (cross : Finset (Fin rows))
      (n w M Nc : ℕ), (∀ i,0≤t i) → (∀ i,0≤len i) →
      (∀ i∈cross,t i=0) → (∀ i,0<t i → t i=dyadic (stage i) ∧ L*t i^σ≤len i) →
      ((Finset.univ.filter (fun i=>0<t i)).card:ℝ)≤C*n →
      TermBudget p q Q L n w M Nc t len (rowRatio report w) →
      2*(M:ℝ)*Nc/w-n≤∑ i∈cross,len i*rowRatio report w i →
      ∀ j γ, ((∑ g : Fin groups, count (atScale (fun i=>0<t i) stage j report) w m γ g.val : ℕ):ℝ) ≤
        fraction ξ (u a+a*(-deriv u a)-δ) (1-(-deriv u a)-δ) j γ*n := by
  obtain ⟨m,price⟩ := purchase.pruned_active_types hC
  refine ⟨m,fun a ha {rows groups} report stage t len cross n w M Nc nonnegative lengthPos
    separated scales many budget kept j γ => ?_⟩
  have bound := count_atScale_le (fun i=>0<t i) stage report j m γ w groups
  apply (Nat.cast_le.mpr bound).trans
  exact price a ha (Fin rows) stage t len (rowRatio report w) cross n w M Nc nonnegative
    lengthPos (fun i => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) separated scales many budget kept j γ

/-- The protocol-level inputs are the spent-cash bound and the physical
lane/capacity charge of the reported rows after catalyst restoration.
Inactive rows have zero width and scale and contribute zero. Retaining
the native sum supplies the shorter allocation at every scale and width. -/
theorem reported_price {u : ℝ→ℝ} {A ε p q Q σ L δ η ξ C : ℝ}
    (purchase : Choice u A ε p q Q σ L δ η ξ) (hC : 0≤C) :
    ∃ m : ℕ, ∀ a∈Set.Icc 1 A, ∀ {rows groups : ℕ} (report : Fin rows → ProtocolRAMEmit.Row)
      (stage : Fin rows → ℕ) (t len : Fin rows → ℝ) (cross : Finset (Fin rows))
      (n w M Nc used : ℕ) (charge : ℝ), 0<n → 0<w → used≤Nc →
      (∀ i,0≤t i) → (∀ i,0≤len i) →
      (∀ i∈cross,t i=0) → (∀ i,0<t i → t i=dyadic (stage i) ∧ L*t i^σ≤len i) →
      ((Finset.univ.filter (fun i=>0<t i)).card:ℝ)≤C*n →
      charge-2*(M:ℝ)*used/w≤6*n →
      (∑ i,(len i*rowRatio report w i+L*AdaptiveProbe.capacity p q Q (t i) (len i)))≤
        charge+2*(M:ℝ)*(Nc-used:ℕ)/w →
      2*(M:ℝ)*Nc/w-n≤∑ i∈cross,len i*rowRatio report w i →
      ∀ j γ, ((∑ g : Fin groups, count (atScale (fun i=>0<t i) stage j report) w m γ g.val : ℕ):ℝ) ≤
        fraction ξ (u a+a*(-deriv u a)-δ) (1-(-deriv u a)-δ) j γ*n := by
  obtain ⟨m,price⟩ := reported_menu purchase hC
  refine ⟨m,fun a ha {rows groups} report stage t len cross n w M Nc used charge hn hw inside
    nonnegative lengthPos separated scales many paid reserved kept j γ => ?_⟩
  have budget := outer_termBudget p q Q L n w M Nc used t len (rowRatio report w) charge
    hn hw inside paid reserved
  exact price a ha report stage t len cross n w M Nc nonnegative lengthPos separated
    scales many budget kept j γ

/-- The positive-scale slot bound with the native final stock settlement.
Each reported row exposes the sum of its already-installed integer load,
the remaining routed core bits, and the unused catalyst return bits.
Repeated edges in a route are included by routeLoad. -/
theorem reported_route_price {u : ℝ→ℝ} {A ε p q Q σ L δ η ξ C : ℝ}
    (purchase : Choice u A ε p q Q σ L δ η ξ) (hC : 0≤C) :
    ∃ m : ℕ, ∀ a∈Set.Icc 1 A, ∀ {rows groups : ℕ} (report : Fin rows → ProtocolRAMEmit.Row)
      (stage : Fin rows → ℕ) (t len : Fin rows → ℝ) (cross : Finset (Fin rows))
      (n w M : ℕ) (I K : Type) [Fintype I] [Fintype K]
      (installed : Fin rows → ℕ) (cash : ℝ) (box : I → ℝ) (core : I → List (Fin rows))
      (stock : I → ℕ) (center : K → List (Fin rows)) (reserved used : K → ℕ),
      0<n → 0<w → (∀ i,0≤t i) → (∀ i,0≤len i) →
      (∀ i∈cross,t i=0) → (∀ i,0<t i → t i=dyadic (stage i) ∧ L*t i^σ≤len i) →
      ((Finset.univ.filter (fun i=>0<t i)).card:ℝ)≤C*n → (∀ c,used c≤reserved c) →
      (∀ i,((core i).map len).sum≤box i) → (∀ c,((center c).map len).sum≤2*M) →
      (∑ e,(len e*((installed e:ℝ)/w)+L*AdaptiveProbe.capacity p q Q (t e) (len e))) ≤
        cash+2*M*(∑ c,(used c:ℝ))/w →
      cash+pairing (fun i=>(stock i:ℝ)/w) box≤6*n →
      (∀ e,(report e).width = installed e+routeLoad core stock e+
        routeLoad center (fun c=>reserved c-used c) e) →
      2*(M:ℝ)*(∑ c,reserved c:ℕ)/w-n≤∑ i∈cross,len i*rowRatio report w i →
      ∀ j γ, ((∑ g : Fin groups, count (atScale (fun i=>0<t i) stage j report) w m γ g.val : ℕ):ℝ) ≤
        fraction ξ (u a+a*(-deriv u a)-δ) (1-(-deriv u a)-δ) j γ*n := by
  obtain ⟨m,price⟩ := reported_menu purchase hC
  refine ⟨m,fun a ha {rows groups} report stage t len cross n w M I K _ _ installed cash box core
    stock center reserved used hn hw nonnegative lengthPos separated scales many within
    coreLen centerLen prepaid net read kept j γ => ?_⟩
  have budget := settle_installed_routes p q Q L n w M hn hw t len installed cash box core stock
    center reserved used within coreLen centerLen prepaid net
  have actual : TermBudget p q Q L n w M (∑ c,reserved c) t len (rowRatio report w) := by
    have eq : rowRatio report w = fun e=>((installed e+routeLoad core stock e+
        routeLoad center (fun c=>reserved c-used c) e:ℕ):ℝ)/w := by
      funext e
      unfold rowRatio
      rw [read e]
    rw [eq]
    exact budget
  exact price a ha report stage t len cross n w M (∑ c,reserved c) nonnegative lengthPos
    separated scales many actual kept j γ

end Hierarchy.Tagged.WideStack

end
end OAI
