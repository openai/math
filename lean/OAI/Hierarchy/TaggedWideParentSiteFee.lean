import OAI.Hierarchy.TaggedWideParentSiteFrame
import OAI.Hierarchy.TaggedWideMaskTariff

namespace OAI
/-! # The five installed ordinary site circuits and all dated site factors -/
noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat.ParentFullCPUs
open ThreeFlat Routing
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard PhysicalTerm
open HistoryRoles ReportSockets Tagged TaggedPrune TaggedShorterBudget ProtocolRAMFrozenWindow
open TaggedShorterSupergroups WideStack WideCalendarSites WideControlJoin WireTelescope Filter
open scoped Classical BigOperators
private theorem frame_sum_arithmetic {a b c d e f g : ℕ} (size : f = g) :
    a+(b+(c+(d+(e+f)))) = (a+b+c+d+e)+g := by omega

private theorem fee_components {whole p b h o : ℕ} (parts : whole=p+(2*b+(h+o))) :
    p ≤ whole ∧ b ≤ whole ∧ h ≤ whole ∧ o ≤ whole := by omega

private theorem fee_factor {a b m : ℕ} (small : a ≤ b) :
    200*a+65 ≤ 200*b+65+48*(2*(m+1))+98 := by omega

private theorem fee_plane {a m : ℕ} :
    48*(2*(m+1))+98 ≤ 200*a+65+48*(2*(m+1))+98 := by omega

private theorem fee_sum {whole tariff keep positive privateGate printed timeline bank subtotal : ℕ}
    (keepCost : keep = 1) (positiveCost : positive ≤ whole*tariff)
    (privateCost : privateGate ≤ 2*subtotal+bank) (privateSub : subtotal ≤ whole*tariff)
    (bankRoom : bank ≤ whole) (planeCost : printed ≤ whole*tariff)
    (timeCost : timeline ≤ whole*tariff) (paid : 0 < tariff) :
    keep+positive+privateGate+printed+timeline ≤ 7*(whole+1)*tariff := by
  have bound : whole ≤ whole*tariff := Nat.le_mul_of_pos_right _ paid
  rw [Nat.mul_assoc 7, Nat.add_mul whole 1, Nat.one_mul]
  omega

private theorem fee_cofinal_factor {d space n : ℕ} (ws : d ≤ space*n) (volume : 1 ≤ n) :
    7*(d+1) ≤ (7*(space+1))*n := by
  calc
    _ ≤ 7*(space*n+n) := Nat.mul_le_mul_left _ (Nat.add_le_add ws volume)
    _ = (7*(space+1))*n := by rw [Nat.mul_assoc, Nat.add_mul, Nat.one_mul]


variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A : ℝ} {v : FixedProtocolFormat F k p q Q σ Λ}
    {x : WideParent κ A} {m ell short : ℕ} {u : ℝ→ℝ} {δ ξ : ℝ} {unitCost N : ℕ}
    (cpu : v.ParentFullCPUs m ell short u δ ξ unitCost N x)
local notation "G" => v.wideFullGates x m ell short u δ ξ unitCost cpu.room
local notation "cap" => v.wideInstalledCap unitCost
local notation "paid" => v.widePrivateUnit unitCost
local notation "histUnit" => v.wideHistoryUnit unitCost

local notation "days" => events v.mesh
local notation "d" => 2^v.W
local notation "dated" => v.wideDated x.h x.w ell unitCost
local notation "rom" => v.wideInstalledRoot x
local notation "size" => v.wideInstalledSize x m ell unitCost dated
local notation "seed" => v.wideInstalledHeader x m ell short u δ ξ unitCost dated
  (v.wide_dated_sites x.h x.w ell unitCost) (v.wide_dated_edges x.h x.w ell unitCost) (fun _=>0)
local notation "slot" => (v.wideSelector x.h x.w cpu.age cpu.ready.credit cpu.ready.size_le).format.slot
local notation "R" => CatalystArchive.fuel v.mesh*x.w
local notation "roles" => HistoryRoles.ceiling v.sampler (h:=x.h) (W:=v.W) (k:=k) (attempts:=v.wideJobs)
  v.mesh unitCost v.keepLimit (CatalystArchive.fuel v.mesh) x.w
local notation "Private" => (v.widePlacement x.h x.w).catalogue.Private (v.wideOrder x.h x.w)
local notation "Data" => v.parentShared x m ell short unitCost ((days).length+1)
variable (ok : cpu.SiteRoom)
  (Z : CalendarTerms F x.h d k x.w R v.radius 1 slot days (v.wideOrigin x.h x.w size seed))
local notation "rout" => Z.nativeRouting Data
local notation "E" => OpenPins x.h x.w (rout).catalyst
local notation "Se" => Fin (rout).selectors
local notation "V" => SitePins E Se Data (G).2
local notation "sites" => Fin (siteLast x.h d k+1)
local notation "endRoom" => v.wide_full_end x m ell short u δ ξ unitCost cpu.room
local notation "addr" => v.wideWindowWidthRow x m ell short u δ ξ cap dated v.maxBits rom (G).2 endRoom
local notation "pWord" => Leaf.positiveWidthPin («E»:=E) («Se»:=Se) (Dst:=Data) (G).2 (cap*x.w) addr ok.positive

local notation "keep" => v.wideKeepNetwork x m ell short u δ ξ unitCost cpu.room E Se Data
local notation "pad" => cpu.positiveGate ok Z
local notation "priv" => v.widePrivateGate (Ex:=E) («Se»:=Se) x m ell short u δ ξ unitCost cpu.room ok.privateBits
local notation "plane" => v.widePlane (Ex:=E) («Se»:=Se) x m ell short u δ ξ unitCost cpu.room
local notation "timeline" => v.wideHistoryGate (Ex:=E) («Se»:=Se) x m ell short u δ ξ unitCost cpu.room ok.history


local notation "geom" => typeMenu κ A v.W m k v.wideJobs ell v.stage_positive (fun _=>short+ell)
local notation "dir" => WideMemory.dir x.h v.W k v.wideJobs
local notation "ports" => WideMemory.H x.h v.W k v.wideJobs
local notation "dates" => (days).length+1
local notation "bits" => WideParent.columnBits
local notation "limit" => max cap histUnit
local notation "space" => v.wideSpaceFactor (m+1) (2^ell) dates paid histUnit

/-- The actual cell and internal-wire counts of the five installed ordinary factors. -/
def ordinaryWork := ((keep).cells+(keep).internal)+((pad).cells+(pad).internal)+((priv).cells+(priv).internal)+
  ((plane).cells+(plane).internal)+((timeline).cells+(timeline).internal)

private theorem column_mono {a b : ℕ} (h : a≤ b) : bits a≤ bits b :=
  Nat.succ_le_succ (Nat.log_mono_right (b:=2) (Nat.succ_le_succ h))


attribute [local irreducible] Native.wordBits Nat.pow

/-- The four data banks are the four disjoint summands of the same native workspace. -/
theorem ordinary_work_bound :
    cpu.ordinaryWork ok Z≤ 7*(Fintype.card Data+1)*
      (200*bits (limit*x.w)+65+48*(2*(m+1))+98) := by
  let P:=OutputData (Fin (m+1)) (Fin (dir).groups) ports (2^ell)
    (fun i : Fin (m+1)=>⌈dyadic i.val*x.w⌉₊)
  let H:=(dates)*Fintype.card ((r:Public v.sampler x.h v.W k v.wideJobs)×Fin (roles r))
  let O:=(Fin (dir).groups×Fin ports)×Fin (histUnit*x.w)
  let B:=Fintype.card Private*(paid*x.w)
  let whole:=Fintype.card Data
  let tariff:=200*bits (limit*x.w)+65+48*(2*(m+1))+98
  have edge : Fintype.card ((e:Private)×Fin (paid*x.w))=B := by
    simp only [Fintype.card_sigma,Fintype.card_fin,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,B,Nat.cast_id]
  have parts : whole=Fintype.card P+(2*B+(H+Fintype.card O)) := by
    change Fintype.card (P ⊕ ((Bool×((e:Private)×Fin (paid*x.w))) ⊕ (Fin H ⊕ O)))=_
    simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_bool,Fintype.card_fin,edge]
  have sizes := fee_components parts
  have scale (a : ℕ) (small : a≤ limit) : 200*bits (a*x.w)+65≤ tariff :=
    fee_factor (column_mono (Nat.mul_le_mul_right x.w small))
  have charge (a b : ℕ) (ha : a≤ whole) (hb : b≤ tariff) : a*b≤ whole*tariff :=
    Nat.mul_le_mul ha hb
  have positive : (pad).cells+(pad).internal≤ Fintype.card P*(200*bits (cap*x.w)+65) := by
    have got:=Leaf.positiveMask_cost (F:=F) (w:=x.w) (Fin.val : Fin (m+1)→ℕ) pWord
      (fun t q=>.inr (.inr (.inl (.inl ⟨t,q.1,q.2⟩))))
    simpa only [positiveGate,P,OutputData,Fintype.card_sigma,Finset.sum_mul] using got
  have posCost:=positive.trans (charge _ _ sizes.1 (scale cap (le_max_left ..)))
  have privCost:=v.wide_private_fee (Ex:=E) («Se»:=Se) x m ell short u δ ξ unitCost cpu.room ok.privateBits
  have cube : paid≤ cap:=by unfold wideInstalledCap;omega
  have pr:=charge B _ sizes.2.1 (scale paid (cube.trans (le_max_left ..)))
  change (priv).cells+(priv).internal≤ 2*Fintype.card Private*(paid*x.w)*(200*bits (paid*x.w)+65)+B at privCost
  have two : 2*Fintype.card Private*(paid*x.w)*(200*bits (paid*x.w)+65)=
      2*(B*(200*bits (paid*x.w)+65)):=by dsimp only [B];ring
  rw [two] at privCost
  have time:=v.wide_history_fee (Ex:=E) («Se»:=Se) x m ell short u δ ξ unitCost cpu.room ok.history
  have timeCost:=time.trans (charge H _ sizes.2.2.1 (scale histUnit (le_max_right ..)))
  have printed:=v.wide_plane_fee (Ex:=E) («Se»:=Se) x m ell short u δ ξ unitCost cpu.room
  have planeCost:=printed.trans (charge (Fintype.card O) _ sizes.2.2.2 fee_plane)
  have keepCost:=v.wide_keep_cost x m ell short u δ ξ unitCost cpu.room E Se Data
  exact fee_sum keepCost posCost privCost pr sizes.2.1 planeCost timeCost (by
    show 0 < _ + 98
    exact Nat.zero_lt_succ _)

/-- One real coefficient, chosen before the parent, pays for the five actual
ordinary gates on any admissible mounted CPU and its observed calendar. -/
theorem cofinal_ordinary_fee : ∃K:ℝ,0≤ K ∧ ∀ᶠ x : WideParent κ A in WideParent.large κ A,
    ∀ (N : ℕ) (cpu : v.ParentFullCPUs m ell short u δ ξ unitCost N x) (ok : cpu.SiteRoom) Z,
      (cpu.ordinaryWork ok Z:ℝ)≤ K*((2:ℝ)^x.h*x.w*Real.log (x.h:ℝ)) := by
  obtain ⟨K,hK,rates⟩:=WideParent.logarithmic_mask_fee (κ:=κ) (A:=A) (7*(space+1)) limit (m+1)
  refine ⟨K,hK,?_⟩
  filter_upwards [rates] with x rate
  intro N cpu ok Z
  let D:=v.parentShared x m ell short unitCost ((events v.mesh).length+1)
  let n:=2^x.h*x.w
  have ws : Fintype.card D≤ space*n := by
    simpa only [Fintype.card_fin] using v.original_workspace (geom).index x.h x.w (2^ell) dates unitCost
  have volume : 1≤ n:=Nat.mul_pos (Nat.two_pow_pos _) x.formats.2.1
  have enlarged := fee_cofinal_factor ws volume
  exact rate _ _ enlarged (cpu.ordinary_work_bound ok Z)

variable (enter finish : sites→Net F V) (row : sites→Fin (days).length→Net F V)
local notation "part" => cpu.siteFrame ok Z enter finish row

/-- The remaining summands are the two endpoints at each original site and
one actual transition circuit for every original calendar date. -/
theorem frame_site_charge {n : ℕ} (cuts : Fin n→CutFormat F V) :
    (nativeCharges rout (G).1 (G).2 cuts (part).frame.site).site=cpu.ordinaryWork ok Z+
      ∑ s,((finish s).cells+(finish s).internal+(((enter s).cells+(enter s).internal)+
        ∑ j,((row s j).cells+(row s j).internal))) := by
  change (reportedSite keep pad priv plane timeline (network enter finish row)).cells +
    (reportedSite keep pad priv plane timeline (network enter finish row)).internal = _
  exact (reported_cost (F:=F) («V»:=V) keep pad priv plane timeline (network enter finish row)).trans
    (frame_sum_arithmetic (network_size (F:=F) («V»:=V) enter finish row))

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat.ParentFullCPUs

end
end OAI
