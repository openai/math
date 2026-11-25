import OAI.Hierarchy.TaggedWideSpillFieldRoom
import OAI.Hierarchy.ProtocolRAMDateSpillPrefixOrder
import OAI.Hierarchy.ProtocolRAMDateSpillPaidOrder
import OAI.Hierarchy.TaggedWideRoleChordRoom

namespace OAI
/-! # The complete dated site aperture pays both genuine sparsely indexed spill words -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.DatedSpillOffsets
open AdaptiveProbe ProbeStage ProbeStage.CoreBoard ProbeStage.CoreBoard.HistoryRoles
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open WireTelescope NamedAperture Tagged.PassiveWindow Computability.VPVNP.BurstRAM
open scoped BigOperators Classical
variable {h W k attempts axes native : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h))) (depth : ℕ)
    (marks : ReportSockets.Marks h W k attempts) (b : CatalogueRows.Board) (order : Fin b.coreRows ≃ Edges S h (2^W) k)
    (sized : attempts*(PurchaseFrozen.count h (2^W) k*PurchaseFrozen.paths h S.degree depth)=b.boughtRows)
    (axis : Catalysts h W k≃Fin axes) (m : Memory native)
    (pad : Chord (siteLast h (2^W) k+1)) (spill : Goods h W k→ℕ)
local notation "d" => 2^W
local notation "G" => Goods h W k
local notation "Cat" => Catalogue S π depth marks
local notation "names" => timeRows S π depth marks b order sized axis
local notation "whereAt" => sorted S π depth marks ∘ names
local notation "ord" => b.ordinal S π depth marks order sized
local notation "B" => b.coreMount π (siteNumber h d k) order m
local notation "sites" => siteLast h d k+1
local notation "L" => (B).datedLayout (siteNumber h d k).injective pad
local notation "mass" => routeLoad (B).ordinary spill
local notation "older" => (Sum.elim (fun _:Cat=>0) (Sum.elim spill (fun _:Catalysts h W k=>0))) ∘ names
local notation "newer" => (Sum.elim (fun c:Cat=>mass (ord c)) (fun _:G⊕Catalysts h W k=>0)) ∘ names

theorem old_chord_limit (cap : ℕ) (bounded : ∀c,installedWidths whereAt older c≤cap) (ch : Chord sites) :
    installedWidths (L).family ((L).bits spill) ch≤cap := by
  apply installed_le_of_datedBase _ _ cap _ ch
  intro i on
  have good : ∃g,(L).num i=.inr (.inl g) := by
    cases key:(L).num i with
    | inl e=>simp [SpillRows.Chart.bits,SettledMatrix.Layout.available,Function.comp_apply,key] at on
    | inr a=>cases a with
      | inl g=>exact ⟨g,rfl⟩
      | inr v=>exact v.elim
  obtain ⟨g,key⟩:=good
  let t:=(names).symm (.inr (.inl g))
  have same : ((L).num).symm (.inr (.inl g))=i := (L).num.symm_apply_eq.mpr key.symm
  have qty : (L).bits spill i=spill g:=by simp [SpillRows.Chart.bits,SettledMatrix.Layout.available,Function.comp_apply,key]
  have named : older t=spill g:=by simp [t]
  have start : datedBase whereAt older t=datedBase (L).family ((L).bits spill) i := by
    simpa only [datedBase,prefixAt,t,same] using
      old_prefix_on_goods S π depth marks b order sized axis B pad spill g
  have before:=(datedBase_room whereAt older t (by rw [named,←qty];exact on)).trans (bounded _)
  simpa only [start,named,qty] using before

theorem new_chord_limit (cap : ℕ) (bounded : ∀c,installedWidths whereAt newer c≤cap) (ch : Chord sites) :
    installedWidths (L).edge (routeLoad (L).routes ((L).bits spill)) ch≤cap := by
  have weights : routeLoad (L).routes ((L).bits spill)=mass:=funext ((L).measured spill)
  rw [weights]
  apply installed_le_of_datedBase _ _ cap _ ch
  intro i on
  obtain ⟨g,idx⟩:=core_only S π b order m spill i on
  let c : Cat:=.inl g
  let t:=(names).symm (.inl c)
  have ident : ord c=i:=idx
  have qty : newer t=mass i:=by simp [t,ident]
  have start : datedBase whereAt newer t=datedBase (L).edge mass i := by
    change datedBase whereAt newer t=datedBase (filledChord (B).actual pad) mass i
    simpa only [datedBase,prefixAt,t,ident] using
      new_prefix_on_paid S π depth marks b order sized axis m pad spill c (ident.symm ▸ on)
  have before:=(datedBase_room whereAt newer t (by rw [qty];exact on)).trans (bounded _)
  simpa only [start,qty] using before


end Hierarchy.ProtocolRAM.Calendar.DatedSpillOffsets
end

end OAI
