import OAI.Computability.BorderVNP.PackedFinalTieFrame
import OAI.Computability.BorderVNP.PackedSubdivisionGatePhysical
import OAI.Computability.BorderVNP.PackedInheritedTieFields

/-! # Final binding operands on a real sparse terminal network

The represented terminal directory supplies both absolute starts of each
equality. Its actual staging lengths and the region-end markers give the
range of every address, including the end of an empty word. -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FinalTies

open Crossing Shortening.PublicCapacity CellAddresses CellAddressCircuit CellAddressPhysical
open ParseBatchSort VPVNP.VerifierNetwork Subdivision.Gates
open private old_ptr from OAI.Computability.BorderVNP.PackedSubdivisionGatePhysical
open scoped Classical

variable {D np C d k w : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} {N : Network D P bits}
    {s : Shape} (rows : Rows s N) (ports : P ↪ Fin np) (cell : N.Site → Fin C) (state : N.Site → Site)
    {σ : Type*} [Fintype σ] (F : Fields s.sites s.edges np C d k w σ)
    (work : Fin s.sites → Fin w → σ) (occupied : Fin s.edges → σ) (portUsed : Fin np → Bool)
    {x : σ → Bool}

local notation3 "aux" => fun u => (state u).size

variable (rep : Represents N cell (fun u => (state u).size) rows.site rows.edge ports F x)
    (fit : ∀ c, guessedSize N cell c + siteSize N cell c (fun u => (state u).size) + suppliedSize N cell c < 2^w)
    (hin : ∀ v, (state v).incoming = incoming N v)
    (hw : ∀ v, value (x ∘ work (rows.site v)) = (state v).work)
    (v : N.Site) (r : Placement.Row N v)
local notation3 "here" => (⟨v,rfl⟩ : {t : N.Site // cell t = cell v})
local notation3 "name" => nameOld rows ports v r
local notation3 "a" => args F work occupied portUsed x (nameOld rows ports v r)

omit [Fintype P] [Fintype σ] in
include rep in
/-- The public slot names its true site, with source-first interpretation on loops. -/
theorem named_owner : value (x ∘ F.ptr (oldEnd name)) = (F.sites (rows.site v)).val :=
  old_ptr rows ports F (Views.EndpointData.of_rep N F rows.site rows.edge ports rep) v r

omit [Fintype σ] in
include rep hin in
private theorem incoming_fit (u : N.Site) : incoming N u < 2^w := by
  have h : (state u).size < 2^w := (rep.stage u).symm.trans_lt (value_lt _)
  change (state u).work + (state u).incoming < 2^w at h
  rw [← hin u]; omega

include rep fit in
private theorem physical_read :
    value (fun j => (CellAddressViews.frame F).eval x (.inl (oldEnd name),j)) =
      Placement.physicalStart N cell (cell v) rows.edge ports state here r := by
  cases r with
  | inl e =>
    obtain ⟨e,incident⟩ := e
    by_cases hs : N.src e = v
    · subst v
      change value (fun j => (CellAddressViews.frame F).eval x (.inl (Layer.edgeEnd (rows.edge e)
        (decide (N.src e = N.src e))),j)) = _
      rw [decide_eq_true (rfl : N.src e = N.src e)]
      exact CellAddressViews.source_value N cell aux rows.site rows.edge ports F rep fit e
    · have hd := incident.resolve_left hs
      subst v
      change value (fun j => (CellAddressViews.frame F).eval x (.inl (Layer.edgeEnd (rows.edge e)
        (decide (N.src e = N.dst e))),j)) = _
      rw [decide_eq_false hs]
      exact CellAddressViews.dest_value N cell aux rows.site rows.edge ports F rep fit e
  | inr p =>
    obtain ⟨p,rfl⟩ := p
    exact CellAddressViews.port_value N cell aux rows.site rows.edge ports F rep fit p

include rep fit hin hw in
/-- The six public scalar operands contain both genuine cell addresses and the entire width. -/
theorem operands :
    a .work = siteBase N cell (cell v) rows.site aux here ∧
    a .oldBase = (state v).work ∧
    a .clip = Placement.localStart N rows.edge ports v r ∧
    a .extent = 0 ∧
    a .newBase = Placement.physicalStart N cell (cell v) rows.edge ports state here r ∧
    a .width = Placement.width N v r := by
  have ptr := named_owner rows ports cell state F rep v r
  obtain ⟨workAt,virtual,zero,physical,width⟩ := other_reads F work occupied portUsed x name
  have data := Views.EndpointData.of_rep N F rows.site rows.edge ports rep
  have localFit := incoming_fit rows ports cell state F rep hin
  refine ⟨(stage_read F work occupied portUsed x name (rows.site v) ptr).trans
    (CellAddressViews.site_value N cell aux rows.site rows.edge ports F rep fit v),
    workAt.trans ((Layer.prefix_value F work x _ _ ptr).trans (hw v)),virtual.trans ?_,zero,
    physical.trans (physical_read rows ports cell state F rep fit v r),width.trans ?_⟩
  · cases r with
    | inl e => exact Views.incident_value N F rows.site rows.edge ports data localFit v e
    | inr p => exact Views.attached_value N F rows.site rows.edge ports data localFit v p
  · cases r with
    | inl e => exact rep.edge e.val
    | inr p => exact rep.port p.val

include rep fit hin hw in
/-- No address relocation remains when this serialized row is appended to its owning site. -/
theorem command_eq :
    Layer.command a = Placement.tie N cell (cell v) rows.site rows.edge ports state here r := by
  obtain ⟨base,workAt,localAt,zero,physical,width⟩ :=
    operands rows ports cell state F work occupied portUsed rep fit hin hw v r
  simp only [Layer.command,base,workAt,localAt,zero,physical,width,zero_add,← Nat.add_assoc,Placement.tie]

include rep fit hin hw in
/-- The end of each occupied word fits the corresponding field of the serialized command. -/
theorem address_room :
    a .work + (a .oldBase+a .clip) < 2^w ∧ a .extent+a .newBase < 2^w := by
  obtain ⟨base,workAt,localAt,zero,physical,_⟩ :=
    operands rows ports cell state F work occupied portUsed rep fit hin hw v r
  have staged := Placement.stagedStart_end_le N cell (cell v) rows.site rows.edge ports state here (hin v) r
  have real := Placement.physicalStart_end_le N cell (cell v) rows.edge ports state here r
  have endFit := fit (cell v)
  dsimp only at staged real
  rw [base,workAt,localAt,zero,physical,zero_add]; omega

/-- One uniform compiled frame before the actual terminal network, placement and work widths
are known. It emits the actual nine absolute words on every represented branch. -/
theorem emit (one : 1 < 2^w) :
    ∃ f : Frame σ (Row s.edges np × (Unit ⊕ (Fin d ⊕ Fin 9 × Fin w))),
      f.size ≤ (inputs F work occupied portUsed).size + 1 + (2*s.edges+np)*(4500*(w+1)^2) ∧
      (∀ x r, f.eval x (r,.inl ()) = (inputs F work occupied portUsed).eval x (r,.inl ())) ∧
      (∀ x r j, f.eval x (r,.inr (.inl j)) = (inputs F work occupied portUsed).eval x (r,.inr (.inl j))) ∧
      ∀ (x : σ → Bool) {D : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
        (rows : Rows s N) (ports : P ↪ Fin np) (cell : N.Site → Fin C) (state : N.Site → Site),
      Represents N cell (fun u => (state u).size) rows.site rows.edge ports F x →
      (∀ c, guessedSize N cell c + siteSize N cell c (fun u => (state u).size) + suppliedSize N cell c < 2^w) →
      (∀ v, (state v).incoming = incoming N v) →
      (∀ v, value (x ∘ work (rows.site v)) = (state v).work) →
      ∀ v (r : Placement.Row N v),
        List.ofFn (fun i => (Layer.kind i,value (fun j => f.eval x (nameOld rows ports v r,.inr (.inr (i,j)))))) =
          marked (Placement.tie N cell (cell v) rows.site rows.edge ports state ⟨v,rfl⟩ r) := by
  obtain ⟨f,cost,active,owner,fields⟩ := Layer.emit d w (inputs F work occupied portUsed)
  refine ⟨f,?_,active,owner,?_⟩
  · simpa only [Row,Subdivision.Gates.Old,Fintype.card_sum,Fintype.card_prod,Fintype.card_bool,
      Fintype.card_fin,Nat.mul_comm s.edges 2] using cost
  · intro x D P inst bits N rows ports cell state rep fit hin hw v r
    have room := address_room rows ports cell state F work occupied portUsed rep fit hin hw v r
    have cmd := command_eq rows ports cell state F work occupied portUsed rep fit hin hw v r
    exact (fields x (nameOld rows ports v r) one room.1 room.2).trans (congrArg marked cmd)

end Packing.Inherited.FinalTies

end BorderVNP
end Computability
end OAI
