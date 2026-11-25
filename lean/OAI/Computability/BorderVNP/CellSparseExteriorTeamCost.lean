import OAI.Computability.BorderVNP.CellSparseExteriorLoads
import OAI.Computability.BorderVNP.CellTeamOccurrenceClock

/-! # The native compression time and the bytes passed to the typed initializer -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.Fragments

open RoutingISA SparseExterior Packing.Directory BorderVNP.Cube

/-- Each descriptor emitted in the three native passes represents at least one live bit. -/
theorem stream_positive (l : HostScatter.Layout) (mem supplied : ℕ → ℕ) (rows : List Row)
    (data : ℕ → ℕ → Bool) (c : ℕ) (s : Span) (hs : s ∈ spans (stream l mem supplied rows) data c) :
    0 < s.bits.length := by
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hs
  have h := (stream_located l mem supplied rows q (List.mem_filter.mp hq).1).1
  simpa only [Quad.span,List.length_ofFn] using h

/-- The number of positive descriptors is bounded by the number of copied bits. -/
theorem span_count (ss : List Span) (pos : ∀ s ∈ ss, 0 < s.bits.length) : ss.length ≤ activeWidth ss := by
  induction ss with
  | nil => simp [activeWidth]
  | cons s ss ih =>
    have head := pos s (by simp)
    have tail := ih (fun x hx => pos x (by simp [hx]))
    simp only [activeWidth,List.map_cons,List.sum_cons,List.length_cons] at tail ⊢
    omega

end Diagonal.ExternalSew.Fragments

namespace RoutingISA.SparseExterior

open Cube.TeamRowClock Diagonal.ExternalSew.Fragments DiagonalTallyCellReports CellPacket
open scoped Classical

/-- The sparse field before the verbatim raw report suffix. -/
def Field.prefix (f : Field) := encode f.width [] 0 f.spans

/-- The report suffix has no framing cost beyond the already emitted end marker. -/
theorem Field.bytes_eq (f : Field) : f.bytes = f.prefix ++ f.tail := by
  have go (pos : ℕ) (ss : List Span) : encode f.width f.tail pos ss = encode f.width [] pos ss ++ f.tail := by
    induction ss generalizing pos with
    | nil => simp [encode]
    | cons s ss ih => simp [encode,ih,List.append_assoc]
  exact go 0 f.spans

private theorem prefix_charge (w : ℕ) (f : Field) (ordered : Ordered f.width 0 f.spans)
    (fit : f.width < 2^w) (pos : ∀ s ∈ f.spans, 0 < s.bits.length) :
    f.prefix.length ≤ (6*(w+1))*(activeWidth f.spans+1) := by
  have h := encode_length (w:=w) [] f.spans ordered fit
  change f.prefix.length ≤ (2*w+4)*(f.spans.length+1)+2*activeWidth f.spans+0 at h
  have pay := Nat.mul_le_mul_left (2*w+4) (Nat.add_le_add_right (span_count f.spans pos) 1)
  nlinarith only [h,pay,Nat.zero_le (w*activeWidth f.spans),Nat.zero_le w]

/-- Sum of the genuine compressed supplied fields, excluding their report suffixes.
Logical lengths of omitted zero runs are only read as word-sized integers. -/
theorem team_prefix {C : ℕ} (owner : Fin C → ℕ) (team w volume : ℕ) (f : Fin C → Field)
    (ordered : ∀ c, owner c=team → Ordered (f c).width 0 (f c).spans) (fit : ∀ c, owner c=team → (f c).width < 2^w)
    (pos : ∀ c, owner c=team → ∀ s ∈ (f c).spans, 0 < s.bits.length)
    (load : assignedSum owner team (fun c => activeWidth (f c).spans) ≤ volume) :
    assignedSum owner team (fun c => (f c).prefix.length) ≤ 6*(w+1)*(volume+C) := by
  let owned := Finset.univ.filter fun c => owner c=team
  have card : owned.card ≤ C := (Finset.card_le_card (Finset.filter_subset ..)).trans_eq (by simp)
  have sum := Finset.sum_le_sum (s:=owned) fun c hc =>
    let h := (Finset.mem_filter.mp hc).2
    prefix_charge w (f c) (ordered c h) (fit c h) (pos c h)
  simp only [←Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul,mul_one] at sum
  rw [TypedBatch.assigned_eq_sum] at load ⊢
  exact sum.trans (Nat.mul_le_mul_left _ (Nat.add_le_add load card))

/-- The actual owned order reindexes all natural-valued physical row charges. -/
theorem owned_sum {C count : ℕ} (owner : Fin C → ℕ) (team : ℕ) (order : Fin count ≃ {c : Fin C // owner c=team})
    (weight : Fin C → ℕ) :
    (∑ i : Fin count, weight (order i).val) = assignedSum owner team weight := by
  have h := report_sum owner team order id weight
  simpa only [id_eq,List.map_ofFn,List.sum_ofFn,Function.comp_def] using h

/-- The raw report suffix contains the actual public count positions and one bit
per source-indexed original use. -/
theorem team_tails {Site : Type} {C count p R H B : ℕ} (owner : Fin C → ℕ) (team : ℕ)
    (order : Fin count ≃ {c : Fin C // owner c=team}) (l : ReportLayout) (r : Fin C → ReportCell l)
    (places : Fin C → Placed Site) (number : ∀ c, (places c).reports.length=l.gadgets)
    (width : ∀ c, ∀ v ∈ (places c).reports, v.length=l.countWidth)
    (pub : assignedSum owner team (fun c => ((places c).parts.flatMap CellSparse.Packet.Source.Part.publicBuffer).length) ≤ 2^p)
    (original : ((c : {c : Fin C // owner c=team}) × UsePositions (r c.val).bundles) ↪
      Diagonal.CellEntries.PowerSlot (Fin R) (Fin H) B) :
    assignedSum owner team (fun c => (r c).tailWidth) ≤ 2^p+R*(H*B) := by
  have uses := owned_use_le owner team (fun c => (r c).bundles) original
  have counts := count_public_capacity owner team order l places number width pub
  rw [←owned_sum owner team order] at uses ⊢
  simp only [ReportCell.tailWidth,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
  have paid := Nat.mul_le_mul_left count (Nat.le_add_left (l.gadgets*l.countWidth) l.gadgets)
  omega

private theorem row_charge (o : Owned) (w : ℕ) (pos : ∀ s ∈ o.field.spans, 0 < s.bits.length) :
    o.charge w ≤ 200*(w+1)*(activeWidth o.field.spans+1)+7*o.field.tail.length := by
  have rows := Nat.mul_le_mul_left (20+11*w) (Nat.add_le_add_right (span_count o.field.spans pos) 1)
  change 1+readOwned.slots+(4+((20+11*w)*(o.field.spans.length+1)+7*activeWidth o.field.spans+7*o.field.tail.length))+publish.slots ≤ _
  have read : readOwned.slots=30 := by decide
  have out : publish.slots=6 := by decide
  rw [read,out]
  nlinarith only [rows,Nat.zero_le (w*activeWidth o.field.spans),Nat.zero_le w]

/-- The instruction-level budget in `prepare_run`, with charges for the true
owned cell spans, report bits and populated row headers. -/
theorem team_prepare {C count : ℕ} (owner : Fin C → ℕ) (team w volume reports : ℕ)
    (order : Fin count ≃ {c : Fin C // owner c=team}) (f : Fin C → Field) (os : ℕ → Owned)
    (fields : ∀ i : Fin count, (os i.val).field=f (order i).val)
    (pos : ∀ c, owner c=team → ∀ s ∈ (f c).spans, 0 < s.bits.length)
    (load : assignedSum owner team (fun c => activeWidth (f c).spans) ≤ volume)
    (tail : assignedSum owner team (fun c => (f c).tail.length) ≤ reports) :
    setup.slots+(∑ i ∈ Finset.range count, (os i).charge w)+1 ≤ 40+200*(w+1)*(C+volume)+7*reports := by
  have nrows : count ≤ C :=
    (Fintype.card_fin count ▸ Fintype.card_le_of_injective (fun i => (order i).val)
      (Subtype.val_injective.comp order.injective)).trans_eq (Fintype.card_fin C)
  have hs (i : Fin count) := row_charge (os i.val) w (fields i ▸ pos (order i).val (order i).property)
  have sum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hs i)
  simp only [fields,Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,Nat.cast_id,mul_one] at sum
  rw [←owned_sum owner team order] at load tail
  have both := Nat.mul_le_mul_left (200*(w+1)) (Nat.add_le_add load nrows)
  rw [Nat.add_comm volume C] at both
  have seven := Nat.mul_le_mul_left 7 tail
  rw [← Fin.sum_univ_eq_sum_range]
  have st : setup.slots ≤ 39 := by decide
  omega

end RoutingISA.SparseExterior

end BorderVNP
end Computability
end OAI
