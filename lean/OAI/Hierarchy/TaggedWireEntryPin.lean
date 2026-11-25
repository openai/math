import OAI.Hierarchy.TaggedWireEntrySource
import OAI.Hierarchy.TaggedWireTransportAt

namespace OAI
/-! # Literal initial-state socket and bit read by one genuine original routing pin -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.EntryOrder
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open WireTelescope WireTelescope.CalendarTape TaggedPrune Tagged Catalyst AdaptiveProbe HistoryRoles ReportSockets MatchingEntry
open scoped Classical BigOperators
variable {h W k w R epochs n : ℕ}
variable (S : PurchaseSampler) (p : Equiv.Perm (Row h)) (depth : ℕ) (marked : Marks h W k epochs)
local notation "Src" => HistoryRoles.Source S p.symm depth marked
local notation "SiteN" => siteLast h (2^W) k+1
local notation "τ" => exposedSite h (2^W) k w R
local notation "ord" => exposedOrder h (2^W) k w R
local notation "ε" => MatchingEntry.ends p τ (exposedDistinct p) ord
local notation "unit" => fun _ : Fin (Fintype.card (exposedEdges h (2^W) k w R))=>1
local notation "U" => exposedWidth p (2^W) k w R
local notation "srcEnds" rows => fun i=> HistoryRoles.sorted S p.symm depth marked (rows i)
local notation "srcBits" rows => fun i=> sourceWidth S p depth marked w R (rows i)

private theorem vertex_row {L J : ℕ} (ends : Fin J→Chord L) (bits : Fin J→ℕ)
    (q : Bundle bits) (s : Bool) :
    (bitGraph (rowGraph ends) bits).vertex q s=(portGraph L).vertex (ends q.1) s := by
  cases s <;> rfl

def matchingPort {s : Fin SiteN} (v : (matchGraph p τ).Port s) :
    (bitGraph (rowGraph ε) unit).Port s :=
  ⟨(⟨(ord).symm v.1.1,0⟩,MatchingEntry.side p τ v.1.1 v.1.2),
    (vertex_row ε unit _ _).trans (MatchingEntry.terminalPort p τ (exposedDistinct p) ord v).property⟩

theorem entry_to_pin {s : Fin SiteN} (z : State U s) (v : (matchGraph p τ).Port s) :
    let eq:=exposed_width (d:=2^W) (k:=k) (w:=w) (R:=R) p
    MatchingEntry.entryBits p τ (exposedDistinct p) ord (cast (congrArg (fun A=> State A s) eq.symm) z) v=
      siteBits U s z (NamedAperture.transportAt eq (NamedAperture.atPort ε unit (matchingPort p v))) := by
  intro eq
  let x:=cast (congrArg (fun A=> State A s) eq.symm) z
  let t:=matchingPort p v
  have bit (u : Fin (2^1)) : finTwoEquiv u=Computability.VPVNP.RAMSerialization.wordBits 1 u 0 := by
    rw [←Computability.VPVNP.LiveHeader.testBit_wordBits]
    fin_cases u <;> decide
  refine Eq.trans ?_ (NamedAperture.rowBits_transport ε unit eq z t)
  exact bit (chunk ε unit ((ord).symm v.1.1) (x (MatchingEntry.terminalPort p τ (exposedDistinct p) ord v)))

def sourcePortFor (rows : Fin n≃Src) {s : Fin SiteN} (v : (matchGraph p τ).Port s) :
    (bitGraph (rowGraph (srcEnds rows)) (srcBits rows)).Port s := by
  let e:=v.1.1
  let b:=bucket e
  let j:=rows.symm (source S p depth marked b)
  have amount : sourceWidth S p depth marked w R (rows j)=capacity w R b := by
    rw [rows.apply_symm_apply,source_width]
  let bit : Fin (sourceWidth S p depth marked w R (rows j)):=⟨digit e,(digit_lt e).trans_le amount.ge⟩
  let face:=MatchingEntry.side p τ e v.1.2
  have ch : HistoryRoles.sorted S p.symm depth marked (rows j)=ε ((ord).symm e) := by
    rw [rows.apply_symm_apply,source_chord,numbered_chord p,(ord).apply_symm_apply]
  exact ⟨(⟨j,bit⟩,face),(vertex_row (srcEnds rows) (srcBits rows) _ face).trans
    ((congrArg (fun c=>(portGraph SiteN).vertex c face) ch).trans (MatchingEntry.terminalPort p τ (exposedDistinct p) ord v).property)⟩

private theorem transport_port {L : ℕ} {A B : Widths L} (eq : A=B) {s : Fin L} (u : SiteBit A s) :
    (NamedAperture.transportAt eq u).1=u.1 ∧ (NamedAperture.transportAt eq u).2.val=u.2.val := by
  subst B;exact ⟨rfl,rfl⟩

/-- Both equality circuits read the identical oriented site port and the
same natural bit address after transporting their aggregate width proofs. -/
theorem pin_coordinate (rows : Fin n≃Src) {s : Fin SiteN} (v : (matchGraph p τ).Port s) :
    NamedAperture.transportAt (exposed_width (d:=2^W) (k:=k) (w:=w) (R:=R) p)
      (NamedAperture.atPort ε unit (matchingPort p v)) =
    NamedAperture.transportAt (source_aggregate (w:=w) (R:=R) S p depth marked rows)
      (NamedAperture.atPort (srcEnds rows) (srcBits rows) (sourcePortFor S p depth marked rows v)) := by
  let e:=v.1.1
  let b:=bucket e
  let j:=rows.symm (source S p depth marked b)
  let a:=matchingPort p v
  let u:=sourcePortFor S p depth marked rows v
  have ch : HistoryRoles.sorted S p.symm depth marked (rows j)=ε ((ord).symm e) := by
    rw [rows.apply_symm_apply,source_chord,numbered_chord p,(ord).apply_symm_apply]
  have eq1:=transport_port (exposed_width (d:=2^W) (k:=k) (w:=w) (R:=R) p) (NamedAperture.atPort ε unit a)
  have eq2:=transport_port (source_aggregate (w:=w) (R:=R) S p depth marked rows) (NamedAperture.atPort (srcEnds rows) (srcBits rows) u)
  have heads : (NamedAperture.atPort ε unit a).1=(NamedAperture.atPort (srcEnds rows) (srcBits rows) u).1 := by
    apply Subtype.ext
    exact Prod.ext ch.symm rfl
  have headEq:=eq1.1.trans (heads.trans eq2.1.symm)
  apply Sigma.ext headEq
  apply (Fin.heq_ext_iff (congrArg (fun t : (portGraph SiteN).Port s=> U t.1.1) headEq)).mpr
  rw [eq1.2,eq2.2]
  have first:=NamedAperture.offset ε unit a.1.1
  have second:=NamedAperture.offset (srcEnds rows) (srcBits rows) u.1.1
  change (NamedAperture.chordBits ε unit a.1.1).2.val=(NamedAperture.chordBits (srcEnds rows) (srcBits rows) u.1.1).2.val
  rw [first,second]
  change TaggedShorterCommonScan.earlier (NamedAperture.key ε) unit ((ord).symm e).val
      (NamedAperture.key ε ((ord).symm e))+0=
    TaggedShorterCommonScan.earlier (NamedAperture.key (srcEnds rows)) (srcBits rows) j.val
      (NamedAperture.key (srcEnds rows) j)+digit e
  rw [earlier_eq p e,earlier_source S p depth marked rows b,zero_add,add_zero]

private theorem decode_number {I : Type*} {source target : Fintype I} (q : I)
    {j : Fin (@Fintype.card I target)} (index : j.val = ((@Fintype.equivFin I source) q).val) :
    (@Fintype.equivFin I target).symm j=q := by
  cases Subsingleton.elim source target
  rw [Fin.ext index, Equiv.symm_apply_apply]

private theorem exterior_value {K : ℕ} {b : Fin k→ℕ} (perm : Equiv.Perm (Row h))
    (loc : RoutingPin h w b→Fin K) (different : ∀e,(matchGraph perm loc).tail e≠(matchGraph perm loc).head e)
    (order : Fin n≃MatchEdge h w b) {s : Fin K} (input : {i // loc i=s}→Bool)
    (z : State (installedWidths (MatchingEntry.ends perm loc different order) (fun _=>1)) s)
    (q : {i // loc i=s}) :
    MatchingEntry.exteriorView perm loc different order input z ((Fintype.equivFin _ q),2)=
      MatchingEntry.entryBits perm loc different order z ((MatchingEntry.atExterior perm loc s).symm q) := by
  simp only [MatchingEntry.exteriorView,show (2:Fin 3)≠0 by decide,
    show (2:Fin 3)≠1 by decide,ite_false]
  apply congrArg (fun j=>MatchingEntry.entryBits perm loc different order z ((MatchingEntry.atExterior perm loc s).symm j))
  apply decode_number q
  rfl

/-- No selector-dependent movement of the public bit is needed. The row
number on the goods or reserve aperture and its low digit specify the bit. -/
theorem exterior_read (rows : Fin n≃Src) {s : Fin SiteN} (x : {i // τ i=s}→Bool) (z : State U s)
    (orig : {i // τ i=s}) :
    let v:=(MatchingEntry.atExterior p τ s).symm orig
    let eq:=exposed_width (d:=2^W) (k:=k) (w:=w) (R:=R) p
    MatchingEntry.exteriorView p τ (exposedDistinct p) ord x (cast (congrArg (fun A=> State A s) eq.symm) z)
      ((Fintype.equivFin _ orig),2)=
    siteBits U s z (NamedAperture.transportAt (source_aggregate (w:=w) (R:=R) S p depth marked rows)
      (NamedAperture.atPort (srcEnds rows) (srcBits rows) (sourcePortFor S p depth marked rows v))) := by
  intro v eq
  exact (exterior_value p τ (exposedDistinct p) ord x _ orig).trans
    ((entry_to_pin p z v).trans (congrArg (siteBits U s z) (pin_coordinate S p depth marked rows v)))

theorem place_pin (unique : Exclusive marked) (rows : Fin n≃Src) (cap : Public S h W k epochs→ℕ)
    (room : ∀j side,sourceWidth S p depth marked w R (rows j)≤ cap (named S p.symm depth marked unique rows (j,side)))
    {s : Fin SiteN} (v : (matchGraph p τ).Port s) :
    let e:=v.1.1
    let j:=rows.symm (source S p depth marked (bucket e))
    let side:=MatchingEntry.side p τ e v.1.2
    let pin:=sourcePortFor S p depth marked rows v
    let place:=NamedAperture.place (srcEnds rows) (srcBits rows) (named S p.symm depth marked unique rows) cap room
    (place ⟨s,NamedAperture.atPort _ _ pin⟩).1=named S p.symm depth marked unique rows (j,side) ∧
      (place ⟨s,NamedAperture.atPort _ _ pin⟩).2.val=digit e := by
  intro e j side pin place
  have read:=NamedAperture.port_read (srcEnds rows) (srcBits rows) (named S p.symm depth marked unique rows) cap room pin
  exact ⟨congrArg Sigma.fst read,congrArg (fun a : Σ u,Fin (cap u)=> a.2.val) read⟩

end Hierarchy.ProbeStage.CoreBoard.EntryOrder
end

end OAI
