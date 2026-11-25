import OAI.Hierarchy.TaggedWireElectedSource
import OAI.Hierarchy.TaggedWireEarnedOffsite
import OAI.Hierarchy.TaggedWideSelectedSite
import OAI.Hierarchy.TaggedWidePacketAway

namespace OAI
/-! # Physical absence of every unvisited party of a selected strip -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat.ElectedSource
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard Strip
open StripChart StripDirectory CatalogueRows PurchaseFrozen BoughtSockets PurchaseStage ReportSockets
open LinearAlgebra.SpectralBooks ChordGraph
open ThreeFlat.Diagonal.MotifOuterTerms
open WireTelescope ChosenPackets ChosenPackets.RowRouting Probe
open scoped Classical Fin.CommRing BigOperators

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} {v : FixedProtocolFormat F k p q Q σ Λ}
  {h width : ℕ}
local notation "P" => v.widePlacement h width
local notation "D" => 2^v.W
local notation "N" => Stages h D
local notation "W" => wordBits h D copies
local notation "catRows" => (P).catalogue
local notation "K" => siteLast h D k+1
local notation "days" => (v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel
local notation "G" => Commodity (Fin (2^h)) N k
variable {π : Equiv.Perm (Fin (2^h))} {marks : Marks h v.W k ((v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel)}
    {ends : Fin (v.widePlacement h width).catalogue.rows → Site h (2^v.W) k × Site h (2^v.W) k} {m : Memory (wordBits h (2^v.W) copies)} {a : Attempt} {i : ℕ}
    (z : v.ElectedSource h width π marks ends m a i)
    (at₀ : v.widePacketMenuIndex h a) (rt : Fin (v.wideBallotParties h a)) (count : ℕ) (pad : Chord (siteLast h (2^v.W) k+1))
local notation "R" => z.routing at₀ rt count pad
local notation "Q" => z.placed at₀ rt
variable (hist : Histogram (Fin (z.placed at₀ rt).data.terms) count) (s : Fin (siteLast h (2^v.W) k+1)) (off : ∀j,z.site j≠s)

include off in
theorem site_outside : s∉Set.range (Q).place := by
  rintro ⟨j,hj⟩
  let t:=j.cast (z.parties at₀ rt)
  apply off t
  have index : t.cast (z.parties at₀ rt).symm = j := Fin.ext rfl
  exact (z.placed_site at₀ rt t).symm.trans ((congrArg (Q).place index).trans hj)

include off in
theorem away : Subsingleton (State (Row.packet Q count).input s) ∧ Subsingleton (State ((R).post hist) s) ∧
    ∀x y,(R).entry hist s x y=1 := by
  have outside:=z.site_outside at₀ rt s off
  refine ⟨(Q).wants_away count outside,?_,?_⟩
  · cases z <;> rename_i g held
    all_goals
      apply g.post_away
      intro x
      simpa only [site,Equiv.symm_apply_apply] using (off (SiteNaming.labels x))
  · have empty : ∀x y,Installs.transport ((R).shape hist) rfl ((R).install.operator (F:=F) (R).order ((R).bits hist) (R).ordinal) s x y=1 := by
      cases z <;> rename_i g held
      all_goals
        apply g.tender_away
        intro x
        simpa only [site,Equiv.symm_apply_apply] using (off (SiteNaming.labels x))
    let : Subsingleton (State ((Row.packet Q count).output hist) s):=(Q).offers_away hist outside
    let : Unique (State ((Row.packet Q count).output hist) s):=uniqueOfSubsingleton (fun _=>0)
    intro x y
    change (∑ t : State ((Row.packet Q count).output hist) s,
      Installs.transport ((R).shape hist) rfl
        ((R).install.operator (F:=F) (R).order ((R).bits hist) (R).ordinal) s t y *
        (Row.packet Q count).entry hist s x t) = 1
    rw [Fintype.sum_unique]
    exact (congrArg₂ (fun a b : F => a * b)
      (empty default y) ((Q).entry_away hist outside x default)).trans (one_mul 1)

private theorem same_pair {J X B : Type} {siteCount i i' : ℕ} (site : B×X ↪ Fin siteCount) (index : B→ℕ)
    (labels : J≃X) (b b' : B) (a : index b=i) (a' : index b'=i') (j j' : J)
    (eq : site (b,labels j)=site (b',labels j')) : i=i' ∧ j=j' := by
  have both:=site.injective eq
  exact ⟨a.symm.trans ((congrArg index (congrArg Prod.fst both)).trans a'),labels.injective (congrArg Prod.snd both)⟩

/-- An actual site collision identifies both the dated candidate and its participant. -/
theorem same_party {i' : ℕ} (z' : v.ElectedSource h width π marks ends m a i') (j j' : Fin (v.wideBallotParties h a))
    (eq : z.site j=z'.site j') : i=i' ∧ j=j' := by
  cases z with
  | payload ph tr row i ordinal g held =>
    cases z'; rename_i ordinal' g' held'
    exact same_pair _ Fin.val SiteNaming.labels.symm row _ ordinal ordinal' j j' eq
  | purchased ph tr sj ti hp ht unique path i ordinal g held =>
    cases z'; rename_i ordinal' g' held'
    exact same_pair _ (fun x=>(BoughtLocation.relative x).val) SiteNaming.labels.symm path _ ordinal ordinal' j j' eq

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat.ElectedSource
end

end OAI
