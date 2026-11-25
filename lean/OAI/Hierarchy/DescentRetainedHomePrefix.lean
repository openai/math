import OAI.Hierarchy.DescentPaidResetWindow
import OAI.Hierarchy.DescentRetainedHomeMask
import OAI.Hierarchy.DescentResetLocalNodes
import OAI.Hierarchy.DescentRotorWindowTicketRead

namespace OAI
/-! # Chronological retained-node offsets at the actual reset home -/
namespace Hierarchy.DescentPaidResidentCount.Reset
open DescentSixParty DescentSixParty.ResetInput DescentContacts DescentColonies DescentGL
open DescentPlainTerminal DescentPlainTerminal.Suffix DescentIssuedFallbackPanel DescentChosenRouter
open DescentRelativeContacts DescentResetHostSize DescentFallbackShapeTable
open DescentHostDirectory DescentPackedActorMask DescentSIMDLookup
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F P V : Type} [Field F] [Fintype V] [DecidableEq V] {d k : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
    {price ε : ℝ} {h C Ht g : ℕ} {Z : ResetInput A price ε h C Ht} {T : Terminals Z}
    {pos : A.graph.Site→V} {ix : A.graph.Site→Block k} {hub : V→Bool}
variable (frame : SourceFrame Z T pos ix hub g)
    (vertex : V↪ℕ) (near : V→Finset V) (n f B wire K Δ : ℕ) (wt : V→Block k→ℕ)
    (flow : V→V→Block k→ℝ) (roster : SourceFrame.Roster Z T pos ix hub g frame vertex near n f B wire K flow Δ wt)
local notation "c" => T.commonDepth
local notation "Y" => (2^Z.n:ℕ)
local notation "r" => Z.k-c
local notation "fit" => frame.enough.trans (Nat.sub_le ..)
set_option quotPrecheck false in
local notation "safe" => roster.2.2.2.2.2.choose
local notation "ep" => endpoint near (fun (v : V)=>Z.placement.b (frame.host v)) frame.basis wt f
  (32*Nat.clog 2 (2*Δ)) B g Y safe (fun (v : V) (j : ℕ)=>(frame.host v,j)∈Z.placement.keys) hub
local notation "μ" => rearrange frame.basis
variable (t : Z.Fallback)
set_option quotPrecheck false in
local notation "v₀" => frame.host.symm (T.code t).1
set_option quotPrecheck false in
local notation "hi" => Z.rootBlock T (.inr t)
set_option quotPrecheck false in
local notation:max "name" t:arg => (shortName c (T.code t)).2
local notation:max "code" t:arg => cell r (name t)
set_option quotPrecheck false in
local notation:max "raw" j:arg => (μ).symm (join fit hi j)
variable (word : Block (k-T.commonDepth)→ℕ)


omit [Fintype V] [DecidableEq V] in
theorem old_home_digit (pivot : DescentNamedContact.Fibre T.home t) :
    ix pivot.val=raw (low («c»:=c) (μ (ix pivot.val))) := by
  have coarse:=frame.homeHigh pivot.val
  rw [pivot.property] at coarse
  have here : high fit (μ (ix pivot.val))=hi:=Fin.ext coarse.symm
  have back : join fit hi (low («c»:=c) (μ (ix pivot.val)))=μ (ix pivot.val):=
    here ▸ join_high_low fit (μ (ix pivot.val))
  rw [back,Equiv.symm_apply_apply]

include roster in
theorem old_home_register (stencil : ∀lo : Block (k-c),word lo/2=Stencil.shapeCode (k-c) Y (fieldsRelative c (ep v₀ (raw lo))))
    (pivot : DescentNamedContact.Fibre T.home t) :
    word (low («c»:=c) (μ (ix pivot.val)))/2=code t := by
  have host:=frame.homeHost pivot.val
  rw [pivot.property] at host
  exact («matches» (A:=A) (Z:=Z) (T:=T) frame vertex near n f B wire K Δ wt flow roster t word stencil pivot.val (low («c»:=c) (μ (ix pivot.val)))
    ((Equiv.eq_symm_apply _).mpr host.symm) (old_home_digit frame t pivot)).mpr pivot.property

theorem homeTicket_lt {N : ℕ} (oldId : A.graph.Site↪Fin N) (i j : DescentNamedContact.Fibre T.home t) :
    Z.homeTicket T oldId t i < Z.homeTicket T oldId t j ↔ oldId i.val < oldId j.val := by
  let rank : DescentNamedContact.Fibre T.home t↪ℕ :=
    ((Function.Embedding.subtype _).trans oldId).trans Fin.valEmbedding
  have same (u : DescentNamedContact.Fibre T.home t) :
      Z.homeTicket T oldId t u=DescentPhysicalOrder.physical rank u:=by
    apply Fin.ext
    rw [Z.homeTicket_read,DescentPhysicalOrder.physical_val]
    rfl
  rw [same,same]
  exact DescentPhysicalOrder.physical_lt_iff rank i j

include roster in
/-- Restrict the previous paid prefix to this one home and sort by the
original donor coordinate recovered by the measured inverse GL comparator. -/
theorem ordered_window_sum (stencil : ∀lo : Block (k-c),word lo/2=Stencil.shapeCode (k-c) Y (fieldsRelative c (ep v₀ (raw lo))))
    {N : ℕ} (oldId : A.graph.Site↪Fin N)
    (ordered : ∀a b,pos a=pos b→(oldId a<oldId b ↔ ix a< ix b))
    (amount : A.graph.Site→ℕ) (old : Block (k-c)→ℕ)
    (previous : ∀lo,old lo=∑u : A.graph.Site,if pos u=v₀ ∧ ix u=raw lo then amount u else 0)
    (pivot : DescentNamedContact.Fibre T.home t) (atDigit : Block (k-c)) (position : ix pivot.val=raw atDigit) :
    (∑lo : Block (k-c),if raw lo<raw atDigit ∧ word lo/2=code t then old lo else 0)=
      ∑u ∈ Finset.univ.filter (fun u : DescentNamedContact.Fibre T.home t=>
        Z.homeTicket T oldId t u<Z.homeTicket T oldId t pivot),amount u.val := by
  have ownSite := frame.homeHost pivot.val
  rw [pivot.property] at ownSite
  have atHost : pos pivot.val=v₀ := (Equiv.eq_symm_apply _).mpr ownSite.symm
  let early (u : A.graph.Site):=if oldId u<oldId pivot.val then amount u else 0
  let count (lo : Block (k-c)):=if raw lo<raw atDigit then old lo else 0
  have counted (lo : Block (k-c)) :
      count lo=∑u : A.graph.Site,if pos u=v₀ ∧ ix u=raw lo then early u else 0 := by
    dsimp only [count]
    rw [previous]
    by_cases which : raw lo<raw atDigit
    · rw [ite_eq_left which]
      apply Finset.sum_congr rfl
      intro u _
      by_cases hpos : pos u=v₀ ∧ ix u=raw lo
      · have less := ordered u pivot.val (hpos.1.trans atHost.symm)
        rw [hpos.2,position] at less
        simp [early,hpos,less.mpr which]
      · simp [hpos]
    · rw [ite_eq_right which]
      symm
      apply Finset.sum_eq_zero
      intro u _
      by_cases hpos : pos u=v₀ ∧ ix u=raw lo
      · have less := ordered u pivot.val (hpos.1.trans atHost.symm)
        rw [hpos.2,position] at less
        have notEarly : ¬oldId u<oldId pivot.val := fun q=>which (less.mp q)
        simp [early,hpos,notEarly]
      · simp [hpos]
  have gathered:=window_sum (A:=A) (Z:=Z) (T:=T) frame vertex near n f B wire K Δ wt flow roster t word stencil
    id early count counted
  rw [Finset.sum_filter]
  convert gathered using 1
  · apply Finset.sum_congr rfl
    intro lo _
    by_cases past : raw lo<raw atDigit <;> by_cases here : word lo/2=code t <;> simp [past,here,count]
  · apply Finset.sum_congr rfl
    intro u _
    simp only [homeTicket_lt t oldId,early,id_eq]

/-- The rank used by the finite comparator is the rank of the real old
absolute donor digit restricted to the attained coarse window. -/
def physicalDonorOrder (v : DescentResetRetainedSetup.Layout) (coords : Fin v.donors ≃ Block (k-c)) :
    Fin v.donors ≃ Fin v.donors :=
  (DescentPhysicalOrder.physical (⟨fun i=>(raw (coords i)).val,by
    intro a b same
    apply coords.injective
    have joined:=(μ).symm.injective (Fin.ext same)
    simpa only [low_join] using congrArg (low («c»:=c)) joined⟩)).trans (finCongr (Fintype.card_fin _))

omit [Fintype V] [DecidableEq V] in
theorem physicalDonorOrder_lt (v : DescentResetRetainedSetup.Layout) (coords : Fin v.donors ≃ Block (k-c))
    (i j : Fin v.donors) :
    physicalDonorOrder frame t v coords i < physicalDonorOrder frame t v coords j ↔ raw (coords i)<raw (coords j) :=
  DescentPhysicalOrder.physical_lt_iff _ _ _

include roster in
theorem routed_home_prefix (stencil : ∀lo : Block (k-c),word lo/2=Stencil.shapeCode (k-c) Y (fieldsRelative c (ep v₀ (raw lo))))
    (v : DescentResetRetainedSetup.Layout) (coords : Fin v.donors ≃ Block (k-c))
    (siteWord : DescentSIMDLookup.Cell v.siteWord) {N : ℕ} (oldId : A.graph.Site↪Fin N)
    (ordered : ∀a b,pos a=pos b→(oldId a<oldId b ↔ ix a< ix b))
    (amount : A.graph.Site→ℕ)
    (previous : ∀lo,v.originalCount siteWord (coords.symm lo)=∑u : A.graph.Site,
        if pos u=v₀ ∧ ix u=raw lo then amount u else 0)
    (pivot : DescentNamedContact.Fibre T.home t) (d : Fin v.donors)
    (position : ix pivot.val=raw (coords d)) :
    let prior:=fun i j=>decide (raw (coords i)<raw (coords j))
    let accept:=fun j=>decide (word (coords j)/2=code t)
    let order:=physicalDonorOrder frame t v coords
    v.offset (v.routedWord accept prior siteWord) (order d)=
        ∑u ∈ Finset.univ.filter (fun u : DescentNamedContact.Fibre T.home t=>
           Z.homeTicket T oldId t u<Z.homeTicket T oldId t pivot),amount u.val := by
  intro prior accept order
  have sorted (i j : Fin v.donors) : prior i j=decide ((order i).val<(order j).val) :=
    by simp only [prior,order,←Fin.lt_def,(physicalDonorOrder_lt frame t v coords i j)]
  rw [v.routed_offset accept prior order (v.original_rank prior order sorted) siteWord d]
  rw [←ordered_window_sum frame vertex near n f B wire K Δ wt flow roster t word stencil oldId ordered amount
    (fun lo=>v.originalCount siteWord (coords.symm lo)) previous pivot (coords d) position,←coords.sum_comp]
  apply Finset.sum_congr rfl
  intro j _
  simp only [accept,decide_eq_true_eq,Equiv.symm_apply_apply]
  have cmp : (order j).val<(order d).val ↔ raw (coords j)<raw (coords d) := physicalDonorOrder_lt frame t v coords j d
  simp only [cmp]

/-- Count the occupancy flags in the actual reached metadata strip. If the
previous paid count fills the strip, the last occupied node is also included. -/
theorem count_occupied (v : DescentResetRetainedSetup.Layout) (siteWord : Cell v.siteWord)
    (d : Fin v.donors) (len : ℕ) (fits : len≤v.previousNodes)
    (occupied : ∀n : Fin v.previousNodes,(v.entry siteWord d n v.occupiedField).val≠0 ↔ n.val<len) :
    v.originalCount siteWord d=len:=by
  have counted : v.originalCount siteWord d=(Finset.univ.filter (fun n : Fin v.previousNodes=>n.val<len)).card:=by
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro n _
    by_cases yes:n.val<len
    · simp [yes,(occupied n).mpr yes]
    · have zero : (v.entry siteWord d n v.occupiedField).val=0:=by
        by_contra ne
        exact yes ((occupied n).mp ne)
      simp [yes,zero]
  rw [counted]
  rcases lt_or_eq_of_le fits with lt|eqn
  · change (Finset.univ.filter (fun n : Fin v.previousNodes=>n<(⟨len,lt⟩ : Fin v.previousNodes))).card=_
    have eqn : (Finset.univ.filter (fun n : Fin v.previousNodes=>n<(⟨len,lt⟩ : Fin v.previousNodes)))=
        Finset.Iio ⟨len,lt⟩:=by ext n; simp
    rw [eqn,Fin.card_Iio]
  · subst len
    simp

/-- A dense previous local-node number already equals its count of
predecessors, including in the empty and singleton menus. -/
private theorem card_before {U : Type} [Fintype U] (e : U≃Fin (Fintype.card U)) (a : U) :
    (Finset.univ.filter (fun v=>e v<e a)).card=(e a).val:=by
  have eqn : (Finset.univ.filter (fun v=>e v<e a)).map e.toEmbedding=Finset.Iio (e a):=by
    ext j
    constructor
    · intro h
      obtain ⟨v,hv,rfl⟩:=Finset.mem_map.mp h
      exact Finset.mem_Iio.mpr (Finset.mem_filter.mp hv).2
    · intro h
      apply Finset.mem_map.mpr
      exact ⟨e.symm j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa using Finset.mem_Iio.mp h⟩,e.apply_symm_apply _⟩
  simpa using congrArg Finset.card eqn

include roster in
theorem primary_node_number (stencil : ∀lo : Block (k-c),word lo/2=Stencil.shapeCode (k-c) Y (fieldsRelative c (ep v₀ (raw lo))))
    (v : DescentResetRetainedSetup.Layout) (coords : Fin v.donors ≃ Block (k-c))
    (siteWord : Cell v.siteWord) {N : ℕ} (oldId : A.graph.Site↪Fin N)
    (ordered : ∀a b,pos a=pos b→(oldId a<oldId b ↔ ix a< ix b))
    (Node : A.graph.Site→Type) [∀u,Fintype (Node u)] (priorNode : ∀u,Node u≃Fin (Fintype.card (Node u)))
    (previous : ∀lo,v.originalCount siteWord (coords.symm lo)=∑u : A.graph.Site,
        if pos u=v₀ ∧ ix u=raw lo then Fintype.card (Node u) else 0)
    (pivot : DescentNamedContact.Fibre T.home t) (z : Node pivot.val) :
    let d:=coords.symm (low («c»:=c) (μ (ix pivot.val)))
    let prior:=fun i j=>decide (raw (coords i)<raw (coords j))
    let accept:=fun j=>decide (word (coords j)/2=code t)
    let order:=physicalDonorOrder frame t v coords
    (DescentResetLocalNodes.oldOrder (fun u : DescentNamedContact.Fibre T.home t=>Node u.val)
      ((Z.homeTicket T oldId t).trans Fin.valEmbedding)
      (fun u=>(priorNode u.val).toEmbedding.trans Fin.valEmbedding) ⟨pivot,z⟩).val=
      v.offset (v.routedWord accept prior siteWord) (order d)+(priorNode pivot.val z).val := by
  intro d prior accept order
  rw [DescentResetLocalNodes.oldOrder_val]
  have atSlot : ix pivot.val=raw (coords d):=by
    simpa only [d,Equiv.apply_symm_apply] using old_home_digit frame t pivot
  rw [routed_home_prefix (A:=A) (Z:=Z) (T:=T) frame vertex near n f B wire K Δ wt flow roster t word stencil v coords siteWord
    oldId ordered (fun u=>Fintype.card (Node u)) previous pivot d atSlot]
  exact congrArg (_+·) (card_before (priorNode pivot.val) z)


end
end Hierarchy.DescentPaidResidentCount.Reset

namespace Hierarchy.DescentSixParty.GroupStage
open DescentCompiler DescentColonies
noncomputable section
variable {F P V : Type} [Field F] [Fintype V] [DecidableEq V] {d k i : ℕ}
    {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {q ε : ℝ}

theorem scheduled_site_order (S : AtomSchedule) {tail : ℕ} (A : GroupStage W G q ε (Fin (S.groupCount i)) V k)
    (baseGroups : S.baseGroups=2^tail) (radix : S.radix=2^k) (vertex : V↪Fin (Fintype.card V))
    (coords : Function.Injective (fun u=>(A.pos u,A.block u))) (u v : W.graph.Site)
    (same : (A.pos u).2=(A.pos v).2) :
    A.site vertex coords u<A.site vertex coords v ↔
      StarKeys.filled W.graph A.pos A.block (S.resetInputDigits baseGroups radix i) u <
      StarKeys.filled W.graph A.pos A.block (S.resetInputDigits baseGroups radix i) v := by
  change _ ↔ (StarKeys.filled W.graph A.pos A.block _ u).val<_
  rw [old_inputDigit S baseGroups radix A u,old_inputDigit S baseGroups radix A v]
  exact DescentPackedTicketChronology.site_source A vertex coords u v same

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
