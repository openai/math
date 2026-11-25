import OAI.Hierarchy.TaggedWideSignedSiteFee
import OAI.Hierarchy.TaggedWideSiteCost

namespace OAI
/-! # Summing the genuine cubic-log packet charge over original sites and dates -/

noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open ThreeFlat Routing
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard PhysicalTerm
open HistoryRoles ReportSockets Tagged TaggedPrune TaggedShorterBudget TaggedShorterSupergroups
open WideStack WideCalendarSites WideControlJoin WireTelescope Filter Real
open RoleProgram
open scoped Classical BigOperators
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A s : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (m ell short : ℕ) {u : ℝ→ℝ}
    (δ ξ : ℝ) (unitCost : ℕ) {N : ℕ} {x : WideParent κ A}
variable (cpu : v.ParentFullCPUs m ell short u δ ξ unitCost N x)
local notation "days" => events v.mesh
local notation "d" => 2^v.W
local notation "g" => v.wideDated x.h x.w ell unitCost
local notation "S" => v.wideInstalledSize x m ell unitCost g
local notation "seed" => v.wideInstalledHeader x m ell short u δ ξ unitCost g
  (v.wide_dated_sites x.h x.w ell unitCost) (v.wide_dated_edges x.h x.w ell unitCost) (fun _=>0)
local notation "slot" => (v.wideSelector x.h x.w cpu.age cpu.ready.credit cpu.ready.size_le).format.slot
local notation "G" => v.wideFullGates x m ell short u δ ξ unitCost cpu.room
local notation "D" => v.parentShared x m ell short unitCost ((days).length+1)
local notation "sites" => Fin (siteLast x.h d k+1)

namespace SignedSites
variable {v m ell short δ ξ unitCost cpu}

/-- The coefficient of a single dated circuit and its physical copy ceiling are
both chosen before the parent. This bound includes every site and original date. -/
theorem datedWork_of_per_step (P K : ℕ) :
    ∃C:ℝ,0≤ C ∧ ∀ᶠ x : WideParent κ A in WideParent.large κ A,
      ∀ N (cpu : v.ParentFullCPUs m ell short u δ ξ unitCost N x) (a : SignedSites v m ell short δ ξ unitCost cpu),
      (∀s j,(a.step s j).cells+(a.step s j).internal≤ P*(x.w+1)*(Nat.log 2 (K*x.w+1)+2)^3) →
      (a.datedWork:ℝ)≤ C*((2:ℝ)^x.h*x.w*(log (x.h:ℝ))^(3:ℝ)) := by
  let scaled:=max 1 K
  let batches:=(events v.mesh).length*P
  obtain ⟨C,hC,fees⟩:=eventually_site_bill A 1 scaled batches 0 (siteFactor d k)
  refine ⟨C,hC.le,?_⟩
  have high : Tendsto (WideParent.h (κ:=κ) (A:=A)) (WideParent.large κ A) atTop:=tendsto_comap
  filter_upwards [high.eventually fees] with x usable
  intro N cpu a estimate
  let w:=x.w
  let atSite (i : Fin (siteLast x.h d k+1)):=∑j,((a.step i j).cells+(a.step i j).internal)
  have paid (i) : atSite i≤ (days).length*(P*(w+1)*(Nat.log 2 (K*w+1)+2)^3) := by
    simpa only [atSite,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] using
      Finset.sum_le_sum (fun j (_:j∈(Finset.univ : Finset (Fin (days).length)))=>estimate i j)
  have multiple : w≤ w*scaled:=Nat.le_mul_of_pos_right _ (Nat.zero_lt_one.trans_le (le_max_left 1 K))
  have copies : K*w≤ w*scaled:=(Nat.mul_le_mul_right w (le_max_right 1 K)).trans_eq (Nat.mul_comm _ _)
  have digits : Nat.log 2 (K*w+1)+2≤ Nat.log 2 (w*scaled+1)+2:=
    Nat.add_le_add_right (Nat.log_mono_right (b:=2) (Nat.succ_le_succ copies)) 2
  have coef : batches≤ 128000*batches:=by omega
  have sums (i) : atSite i≤ w*0+2*(batches*(w*scaled))+
      128000*batches*(w*scaled+1)*(Nat.log 2 (w*scaled+1)+2)^3 := by
    have p:=paid i
    have small : batches*(w+1)*(Nat.log 2 (K*w+1)+2)^3≤
        128000*batches*(w*scaled+1)*(Nat.log 2 (w*scaled+1)+2)^3 :=
      Nat.mul_le_mul (Nat.mul_le_mul coef (Nat.succ_le_succ multiple)) (Nat.pow_le_pow_left digits 3)
    have grouped : (days).length*(P*(w+1)*(Nat.log 2 (K*w+1)+2)^3)=
        batches*(w+1)*(Nat.log 2 (K*w+1)+2)^3:=by dsimp [batches];ring
    exact (p.trans_eq grouped).trans (small.trans (Nat.le_add_left ..))
  have final:=usable x.formats.2.1 x.property.1.2.2 (site_count x.h d k Nat.one_le_two_pow)
    (fun _=>w) atSite (fun _=>by simp [w]) sums
  simpa only [datedWork,atSite,Real.rpow_ofNat] using final

/-- The final tariff takes the literal per-date bound supplied by a signed packet.
Its logarithmic exponent is three, including both original endpoint controllers. -/
theorem price_of_steps (terminalWidth P K : ℕ) (positive : 0<terminalWidth) :
    ∃C:ℝ,0≤ C ∧ ∀ᶠ x : WideParent κ A in WideParent.large κ A,
      ∀ N (cpu : v.ParentFullCPUs m ell short u δ ξ unitCost N x) (bounds : cpu.SiteRoom)
        (a : SignedSites v m ell short δ ξ unitCost cpu),
      a.EndpointWiring terminalWidth →
      (∀s j,(a.step s j).cells+(a.step s j).internal≤ P*(x.w+1)*(Nat.log 2 (K*x.w+1)+2)^3) →
      (((a.installed bounds).frame.site.cells+(a.installed bounds).frame.site.internal:ℕ):ℝ)≤
        C*((2:ℝ)^x.h*x.w*(log (x.h:ℝ))^(3:ℝ)) := by
  obtain ⟨R,pos,dates⟩:=datedWork_of_per_step (v:=v) (κ:=κ) (A:=A) (m:=m) (ell:=ell)
    (short:=short) (u:=u) (δ:=δ) (ξ:=ξ) (unitCost:=unitCost) P K
  obtain ⟨C,hC,price⟩:=price_of_dates (v:=v) (κ:=κ) (A:=A) (m:=m) (ell:=ell)
    (short:=short) (u:=u) (δ:=δ) (ξ:=ξ) (unitCost:=unitCost) terminalWidth positive R 3 pos
  refine ⟨C,hC,?_⟩
  filter_upwards [dates,price] with x measured total
  intro N cpu bounds a endpoints fee
  simpa only [show max (1:ℝ) 3=3 by norm_num] using total N cpu bounds a endpoints (measured N cpu a fee)

end SignedSites
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
