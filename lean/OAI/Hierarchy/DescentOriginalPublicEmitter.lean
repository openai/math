import OAI.Hierarchy.DescentOriginalSectorRetention
import OAI.Hierarchy.DescentResetOriginalPosted

namespace OAI
/-! Native donor selection and all four original-word formatter fields on the same public slot. -/
namespace Hierarchy.DescentResetPublicOriginalPhase.Layout
open DescentPackedZip DescentSIMDLookup DescentResetFieldAssembler DescentContactDonorSelection
open DescentResetOriginalSlots DescentResetMixedWordRAM OriginalDate
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {X Q K N w : ℕ} (L : Layout X Q K N) (ok : L.Room w) (m : Memory w)
local notation:max "cast_" x:arg => (x:Cell L.shortBits)
local notation "HB" => Fin L.hosts
local notation "GB" => Fin L.groups
local notation:max "key" j:arg => (L.req j).2
local notation:max "label" x:arg j:arg => L.old.label x (L.req j).1
local notation:max "paid" x:arg j:arg i:arg => L.old.cargo x (L.req j).1 i

include ok

private theorem held_source {b : ℕ} (op : Expr) (v : HB→GB→Cell b) (fit : op.Fits w L.donor)
    (prev : Source op v L.M m) : Source op v L.M (L.first m):=by
  have before:L.format<2^w:=(Nat.le_add_right ..).trans_lt
    (ok.formatEnd.trans_lt ((Nat.le_add_right ..).trans_lt ok.stop))
  have saved:=(DescentResetDonorBook.installed (fun j=>(L.req j).2) L.selectorBits L.shortBits L.M L.donor m
    (ok.donorEnd.trans_lt before)).2.2.2.1
  intro p
  exact (eval_below op _ _ _ fit (fun i hi=>saved i (.inl hi))).trans (prev p)

/-- Trunk inputs read only the original unsigned self name, receiver palette
and the occupied metadata. -/
theorem trunk_output (x : Fin X) («meta» : HB→GB→Meta) (zero : HB→GB→Bool)
    (self palette : HB→GB→Cell L.shortBits) (mb : 0<L.metaBits) (zb : 0<L.zeroBits)
    (blank : L.fn 0 0 0 0 0=0)
    (ms : Source (L.old.meta x 0) (fun h g=>raw L.metaBits («meta» h g)) L.M m)
    (zs : Source (L.old.zero x) (fun h g=>((zero h g).toNat:Cell L.zeroBits)) L.M m)
    (sf : Source (L.old.self x) self L.M m) (pl : Source (L.old.shape x) palette L.M m) :
    Source (.lookup (L.date.output x 0) .row)
      (fun h g=>(L.fn 0 («meta» h g).live.toNat (zero h g).toNat (self h g).val (palette h g).val:Cell L.resultBits))
      L.M (L.dst m):=by
  have f:=L.date.posted (L.dateRoom ok) (L.first m) x 0 rfl «meta» zero self palette mb zb blank
  apply f
  · simpa only [date, Layout.fields, Equiv.symm_apply_apply, Fin.cases_zero, Fin.cases_succ] using held_source L ok m _ _ (ok.meta x 0) ms
  · simp only [date, Layout.fields, Equiv.symm_apply_apply]
    exact held_source L ok m _ _ (ok.zero x) zs
  · simpa only [date, Layout.fields, Equiv.symm_apply_apply, Fin.cases_zero, Fin.cases_succ] using held_source L ok m _ _ (ok.self x) sf
  · simpa only [date, Layout.fields, Equiv.symm_apply_apply, Fin.cases_zero, Fin.cases_succ] using held_source L ok m _ _ (ok.shape x) pl

/-- The direct-contact law reads the two actual results of the old donor search.
Both selectors use the same measured positive endpoint label. -/
theorem contact_output (x : Fin X) (j : Fin Q) («meta» : HB→GB→Meta) (zero : HB→GB→Bool)
    (own : Fin N→HB→GB→Cell L.selectorBits) (cargo : Fin 2→Fin N→HB→GB→Cell L.shortBits)
    (mb : 0<L.metaBits) (zb : 0<L.zeroBits) (blank : L.fn 1 0 0 0 0=0)
    (ms : Source (L.old.meta x j.succ) (fun h g=>raw L.metaBits («meta» h g)) L.M m)
    (zs : Source (L.old.zero x) (fun h g=>((zero h g).toNat:Cell L.zeroBits)) L.M m)
    (ls : ∀i,Source (label x j i) (own i) L.M m)
    (cs : ∀c i,Source (paid x j c i) (cargo c i) L.M m) :
    let visit:=fun c h g=>visits (key j) (fun i=>own i h g) (fun i=>cargo c i h g)
    Source (.lookup (L.date.output x j.succ) .row)
      (fun h g=>(L.fn 1 («meta» h g).live.toNat (zero h g).toNat (visit 1 h g).val (visit 0 h g).val:Cell L.resultBits))
      L.M (L.dst m):=by
  intro visit
  have bound:L.format<2^w:=(Nat.le_add_right ..).trans_lt
    (ok.formatEnd.trans_lt ((Nat.le_add_right ..).trans_lt ok.stop))
  have seen (c : Fin 2) : Source (L.donorExpr x j c) (visit c) L.M (L.first m):=
    (DescentResetDonorBook.read (fun t=>(L.req t).2) L.donor L.format m j (label x j) (paid x j c) own (cargo c)
      (fun i=>⟨ok.label ..,ok.cargo ..⟩) (fun i=>⟨ls i,cs c i⟩) ok.donorEnd bound).2
  apply L.date.posted (L.dateRoom ok) (L.first m) x j.succ rfl «meta» zero (visit 1) (visit 0) mb zb blank
  · simpa only [date, Layout.fields, Equiv.symm_apply_apply, Fin.cases_zero, Fin.cases_succ] using held_source L ok m _ _ (ok.meta x _) ms
  · simp only [date, Layout.fields, Equiv.symm_apply_apply]
    exact held_source L ok m _ _ (ok.zero x) zs
  · simpa only [date, Layout.fields, Equiv.symm_apply_apply, Fin.cases_zero, Fin.cases_succ] using seen 1
  · simpa only [date, Layout.fields, Equiv.symm_apply_apply, Fin.cases_zero, Fin.cases_succ] using seen 0

end
end Hierarchy.DescentResetPublicOriginalPhase.Layout

end OAI
