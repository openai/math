import OAI.Hierarchy.DescentRetainedHomePrefix
import OAI.Hierarchy.DescentRetainedIssuedSelectors
import OAI.Hierarchy.DescentNativeRangePadding

namespace OAI
/-! # Live range fields and padding at the transmitted chronological primary node -/
namespace Hierarchy.DescentPaidResidentCount.Reset
open DescentSixParty DescentSixParty.ResetInput DescentContacts DescentColonies DescentGL
open DescentPlainTerminal DescentPlainTerminal.Suffix DescentIssuedFallbackPanel DescentChosenRouter
open DescentRelativeContacts DescentResetHostSize DescentFallbackShapeTable
open DescentHostDirectory DescentPackedActorMask DescentSIMDLookup
open DescentRetainedControl
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false
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


variable (stencil : ∀ lo : Block (k-T.commonDepth), word lo/2 =
    Stencil.shapeCode (k-T.commonDepth) (2^Z.n) (fieldsRelative T.commonDepth
      (endpoint near (fun (u : V) => Z.placement.b (frame.host u)) frame.basis wt f
        (32*Nat.clog 2 (2*Δ)) B g (2^Z.n) roster.2.2.2.2.2.choose
        (fun (u : V) (j : ℕ) => (frame.host u,j) ∈ Z.placement.keys) hub (frame.host.symm (T.code t).1)
        ((rearrange frame.basis).symm (join (frame.enough.trans (Nat.sub_le ..)) (Z.rootBlock T (.inr t)) (lo))))))


open DescentRetainedRangeDigits
variable (chart : DescentResetOperandSetup.Chart)
local notation "v" => chart.retained
variable (coords : Fin chart.retained.donors≃Block (k-T.commonDepth)) (shape : Fin chart.placement.shapes) (carrier : Fin chart.retained.hosts)
    (coarse : Fin chart.retained.grouped) (which : chart.seven.control.Targets) (window : chart.seven.Packets)
    (strips : chart.retained.Strips)
local notation "wrd" => (v).site strips carrier coarse
local notation "takeDonor" => (fun i : Fin (v).donors=>decide (word (coords i)/2=code t))
local notation "sorted" => (fun i j : Fin (v).donors=>decide (raw (coords i)<raw (coords j)))
local notation "accepted" => ownerAt chart which window shape carrier coarse
local notation "ranked" => priorAt chart window carrier coarse

include roster stencil in
/-- An accepted, occupied donor slot names an actual previous node in this same home fibre. -/
theorem primary_donor_original (owns : accepted=takeDonor)
    {N : ℕ} (oldId : A.graph.Site↪Fin N) (ordered : ∀a b,pos a=pos b→(oldId a<oldId b ↔ ix a< ix b))
    (Node : A.graph.Site→Type) [∀u,Fintype (Node u)] (priorNode : ∀u,Node u≃Fin (Fintype.card (Node u)))
    (previous : ∀lo,(v).originalCount wrd (coords.symm lo)=∑u : A.graph.Site,
      if pos u=v₀ ∧ ix u=raw lo then Fintype.card (Node u) else 0)
    (d₀ : Fin (v).donors) (j₀ : Fin (v).previousNodes)
    (active : accepted d₀=true) (occupied : j₀.val<(v).originalCount wrd d₀) :
    ∃u : DescentNamedContact.Fibre T.home t,∃z : Node u.val,
      pos u.val=v₀ ∧ ix u.val=raw (coords d₀) ∧ (priorNode u.val z).val=j₀.val :=by
  classical
  let lo:=coords d₀
  let resident:=fun u : A.graph.Site=>pos u=v₀ ∧ ix u=raw lo
  have tally : (v).originalCount wrd d₀ = ∑u,if resident u then Fintype.card (Node u) else 0 :=by
    simpa only [lo,Equiv.symm_apply_apply] using previous (coords d₀)
  have unique {u z : A.graph.Site} (hu : resident u) (hz : resident z) : u=z :=by
    apply oldId.injective
    apply le_antisymm
    · apply le_of_not_gt
      intro less
      have impossible:ix z< ix u:=(ordered z u (hz.1.trans hu.1.symm)).mp less
      exact (not_lt_of_ge (hu.2.trans hz.2.symm).le) impossible
    · apply le_of_not_gt
      intro less
      have impossible:ix u< ix z:=(ordered u z (hu.1.trans hz.1.symm)).mp less
      exact (not_lt_of_ge (hz.2.trans hu.2.symm).le) impossible
  have found : ∃u,resident u :=by
    by_contra! none
    simp [none] at tally
    omega
  obtain ⟨u,hu⟩:=found
  have nEq : (v).originalCount wrd d₀=Fintype.card (Node u) :=by
    rw [tally,Finset.sum_eq_single u,ite_eq_left hu]
    · intro u' _ ne
      exact ite_eq_right (fun h'=>ne (unique h' hu))
    · simp
  have indexed : word lo/2=code t:=by simpa only [owns,decide_eq_true_eq] using active
  have atHome : T.home u=t:=(«matches» frame vertex near n f B wire K Δ wt flow roster t word stencil u lo hu.1 hu.2).mp indexed
  let i : Fin (Fintype.card (Node u)):=⟨j₀.val,nEq ▸ occupied⟩
  refine ⟨⟨u,atHome⟩,(priorNode u).symm i,hu.1,hu.2,?_⟩
  simp only [Equiv.apply_symm_apply,i]

include roster stencil in
theorem primary_donor_receipt (owns : accepted=takeDonor) (compared : ranked=sorted)
    {N : ℕ} (oldId : A.graph.Site↪Fin N) (ordered : ∀a b,pos a=pos b→(oldId a<oldId b ↔ ix a< ix b))
    (Node : A.graph.Site→Type) [∀u,Fintype (Node u)] (priorNode : ∀u,Node u≃Fin (Fintype.card (Node u)))
    (previous : ∀lo,(v).originalCount wrd (coords.symm lo)=∑u : A.graph.Site,
      if pos u=v₀ ∧ ix u=raw lo then Fintype.card (Node u) else 0)
    (pivot : DescentNamedContact.Fibre T.home t) (z : Node pivot.val) (j : Fin (v).previousNodes)
    (former : j.val=(priorNode pivot.val z).val) (nxt : Fin (v).nodes)
    (named : nxt.val=(DescentResetLocalNodes.oldOrder (fun u : DescentNamedContact.Fibre T.home t=>Node u.val)
      ((Z.homeTicket T oldId t).trans Fin.valEmbedding)
      (fun u=>(priorNode u.val).toEmbedding.trans Fin.valEmbedding) ⟨pivot,z⟩).val) :
    let d:=coords.symm (low («c»:=c) (μ (ix pivot.val)))
    let order:=physicalDonorOrder frame t v coords
    accepted d=true ∧ j.val<(v).originalCount wrd d ∧
      nxt.val=(v).offset ((v).routedWord accepted ranked wrd) (order d)+j.val ∧
      ∀i,neighbors ranked i=(order i).val := by
  intro d order
  have comparison i k : sorted i k=decide ((order i).val<(order k).val):=by
    simp only [order,←Fin.lt_def,physicalDonorOrder_lt frame t v coords]
  have home:=old_home_register frame vertex near n f B wire K Δ wt flow roster t word stencil pivot
  have yes : takeDonor d=true:=by simp [d,home]
  have serial:=primary_node_number frame vertex near n f B wire K Δ wt flow roster t word stencil v coords wrd
    oldId ordered Node priorNode previous pivot z
  have src:=frame.homeHost pivot.val
  rw [pivot.property] at src
  have hh : pos pivot.val=v₀:=(Equiv.eq_symm_apply _).mpr src.symm
  have original:=old_home_digit frame t pivot
  have card : Fintype.card (Node pivot.val)≤(v).originalCount wrd d:=by
    rw [show d=coords.symm (low («c»:=c) (μ (ix pivot.val))) from rfl,previous]
    have term:=Finset.single_le_sum (f:=fun u : A.graph.Site=>if pos u=v₀ ∧ ix u=raw (low («c»:=c) (μ (ix pivot.val)))
      then Fintype.card (Node u) else 0) (fun _ _=>Nat.zero_le _) (Finset.mem_univ pivot.val)
    simpa only [ite_eq_left (And.intro hh original)] using term
  have occupied : j.val<(v).originalCount wrd d:=by rw [former];exact (priorNode pivot.val z).isLt.trans_le card
  have position : nxt.val=(v).offset ((v).routedWord accepted ranked wrd) (order d)+j.val:=by
    rw [owns,compared]
    exact named.trans (by simpa [d,order,former] using serial)
  have active : accepted d=true:=by simpa only [owns] using yes
  have rank : ∀i,neighbors ranked i=(order i).val:=by
    rw [compared]
    exact (v).original_rank sorted order comparison
  exact ⟨active,occupied,position,rank⟩

include roster stencil in
theorem primary_seven_spans (owns : accepted=takeDonor) (compared : ranked=sorted)
    {N : ℕ} (oldId : A.graph.Site↪Fin N) (ordered : ∀a b,pos a=pos b→(oldId a<oldId b ↔ ix a< ix b))
    (Node : A.graph.Site→Type) [∀u,Fintype (Node u)] (priorNode : ∀u,Node u≃Fin (Fintype.card (Node u)))
    (previous : ∀lo,(v).originalCount wrd (coords.symm lo)=∑u : A.graph.Site,
      if pos u=v₀ ∧ ix u=raw lo then Fintype.card (Node u) else 0)
    (pivot : DescentNamedContact.Fibre T.home t) (z : Node pivot.val) (j : Fin (v).previousNodes)
    (former : j.val=(priorNode pivot.val z).val) (nxt : Fin (v).nodes)
    (named : nxt.val=(DescentResetLocalNodes.oldOrder (fun u : DescentNamedContact.Fibre T.home t=>Node u.val)
      ((Z.homeTicket T oldId t).trans Fin.valEmbedding)
      (fun u=>(priorNode u.val).toEmbedding.trans Fin.valEmbedding) ⟨pivot,z⟩).val) :
    let d:=coords.symm (low («c»:=c) (μ (ix pivot.val)))
    (∀(arg : Fin (v).args) (oldArg : Fin (v).previousArgs) (f : Fin 3),arg.val=oldArg.val →
      oldArg.val<((v).entry wrd d j (v).arityField).val →
      chart.seven.decoded which window strips ((v).outputID 1 (page f) arg nxt) shape carrier coarse=
        (v).entry wrd d j ((v).operandField (page f) oldArg)) ∧
    (∀(arg : Fin (v).args) (f : Fin 3),((v).entry wrd d j (v).arityField).val≤arg.val →
      chart.seven.decoded which window strips ((v).outputID 1 (page f) arg nxt) shape carrier coarse=0) := by
  intro d
  let order:=physicalDonorOrder frame t v coords
  obtain ⟨active,occupied,position,rank⟩:=primary_donor_receipt frame vertex near n f B wire K Δ wt flow
    roster t word stencil chart coords shape carrier coarse which window strips owns compared oldId ordered
    Node priorNode previous pivot z j former nxt named
  constructor
  · intro arg oldArg f same present
    exact decoded_range chart which window strips shape carrier coarse 1 order rank d j oldArg active occupied
      present nxt position arg same f
  · intro arg f past
    exact decoded_padding chart which window strips shape carrier coarse 1 order rank d j active occupied
      nxt position arg past f

end
end Hierarchy.DescentPaidResidentCount.Reset

end OAI
