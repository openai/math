import OAI.Computability.BorderVNP.CellTeamGeometryCharge
import OAI.Computability.BorderVNP.DiagonalTallyReportBatchCost

/-! # Native report-clock charge from original metadata and checked power slots -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open RoutingISA CellPacket CellSparse.Packet CellSparse.Packet.Source Cube.TeamRowClock
open scoped Classical

/-- A delivered sidecar pays for decoding its actual header and one-copy positions.
The field width is paid only once per such physical bit. -/
theorem original_decode_le {w description : ℕ} {l : ReportLayout} (bs : List ReportBundle) (q : LocalReportCursor)
    (p : ℕ) (m : ℕ → ℕ) (input : bundleInputs w l description bs q p m) :
    originalFields bs*(l.fieldWidth+1) ≤ 2*(description+1)*bs.length := by
  induction bs generalizing q p m with
  | nil => simp [originalFields]
  | cons b bs ih =>
    have size := input.1.descriptionRoom
    rw [TallySidecar.bits_length] at size
    have width := input.1.marked_le
    have tail := ih _ _ _ input.2
    have head : (1+b.positions.length)*(l.fieldWidth+1) ≤ 2*(description+1) := by
      nlinarith only [size,width,Nat.zero_le (b.positions.length*l.fieldWidth)]
    change (1+b.positions.length+originalFields bs)*(l.fieldWidth+1) ≤ 2*(description+1)*(bs.length+1)
    rw [Nat.add_mul,Nat.mul_succ]
    exact (Nat.add_le_add head tail).trans_eq (Nat.add_comm ..)

/-- This also holds for the complete chronological report input, including every
source's actual intermediate memory after the previous scans. -/
theorem original_team_le {w description : ℕ} {l : ReportLayout} (cs : List (ReportCell l))
    (q : ReportCursor) (p : ℕ) (m : ℕ → ℕ) (input : cellInputs w description cs q p m) :
    teamOriginal cs*(l.fieldWidth+1) ≤ 2*(description+1)*(cs.map (fun c => c.bundles.length)).sum := by
  induction cs generalizing q p m with
  | nil => simp [teamOriginal]
  | cons c cs ih =>
    have head := original_decode_le c.bundles (c.localStart q) _ _ input.1.1.bundles
    have tail := ih _ _ _ input.2
    change (originalFields c.bundles+teamOriginal cs)*(l.fieldWidth+1) ≤ 2*(description+1)*(c.bundles.length+_)
    rw [Nat.add_mul,Nat.mul_add (2*(description+1))]
    exact Nat.add_le_add head tail

/-- The vector length header and every actual count-bit address are public words. -/
theorem count_fields_le_public {Site : Type} (p : Placed Site) :
    p.reports.length+(p.reports.map List.length).sum ≤ (p.parts.flatMap Part.publicBuffer).length := by
  have bound (rs : List (List ℕ)) : rs.length+(rs.map List.length).sum ≤ (fieldList vector rs).length := by
    induction rs with
    | nil => simp [fieldList]
    | cons r rs ih =>
      simp only [fieldList,List.flatMap_cons,List.length_cons,List.length_append,vector,List.map_cons,List.sum_cons] at ih ⊢
      omega
  have h := bound p.reports
  simp only [Placed.parts,plan,List.flatMap_cons,List.flatMap_append,List.flatMap_nil,Part.publicBuffer,
    List.length_append,List.length_cons,List.length_nil,List.append_nil]
  omega

/-- The actual compact task order exactly reindexes the assigned global group load. -/
theorem report_sum {C count : ℕ} {α : Type} (owner : Fin C → ℕ) (team : ℕ)
    (order : Fin count ≃ {c : Fin C // owner c=team}) (row : Fin C → α) (f : α → ℕ) :
    ((List.ofFn (fun i => row (order i).val)).map f).sum = assignedSum owner team (f ∘ row) := by
  rw [List.map_ofFn,List.sum_ofFn,TypedBatch.assigned_eq_sum,
    Finset.sum_subtype (p:=fun c => owner c=team) _ (fun _ => by simp)]
  exact order.sum_comp (fun c => f (row c.val))

/-- All per-cell count headers and their digits occupy disjoint public words.
This compares the exact owning team's compact cell count to the sorted capacity. -/
theorem count_public_capacity {Site : Type} {C count p : ℕ} (owner : Fin C → ℕ) (team : ℕ)
    (order : Fin count ≃ {c : Fin C // owner c=team}) (l : ReportLayout) (places : Fin C → Placed Site)
    (number : ∀ c, (places c).reports.length=l.gadgets) (width : ∀ c, ∀ v ∈ (places c).reports, v.length=l.countWidth)
    (pub : assignedSum owner team (fun c => ((places c).parts.flatMap Part.publicBuffer).length) ≤ 2^p) :
    count*(l.gadgets+l.gadgets*l.countWidth) ≤ 2^p := by
  have both (c : Fin C) : l.gadgets+l.gadgets*l.countWidth ≤ ((places c).parts.flatMap Part.publicBuffer).length := by
    have len : ((places c).reports.map List.length).sum = l.gadgets*l.countWidth := by
      rw [List.map_congr_left (g:=fun _ => l.countWidth) (fun x hx => width c x hx)]
      simp [number c]
    have h := count_fields_le_public (places c)
    rwa [number c,len] at h
  let selected := Finset.univ.filter (fun c => owner c=team)
  let cs := List.ofFn (fun i => (order i).val)
  have size : cs.length=count := List.length_ofFn
  have cnt := report_sum owner team order id (fun _ => l.gadgets+l.gadgets*l.countWidth)
  change (cs.map (fun _ => l.gadgets+l.gadgets*l.countWidth)).sum = _ at cnt
  simp [size] at cnt
  rw [TypedBatch.assigned_eq_sum] at pub cnt
  have pay := Finset.sum_le_sum (s:=selected) fun c _ => both c
  exact cnt.trans_le (pay.trans pub)

/-- The ordinary clock for the genuine report-byte guesses and the occurrence
descriptor/bit stores is charged to the sorted public words, the original delivered
source bits and the individually indexed expanded power slots. -/
theorem occurrence_charge {Site A : Type} [Fintype A] {C p count : ℕ}
    (owner : Fin C → ℕ) (team w description X : ℕ) (positive : 1 ≤ description)
    (order : Fin count ≃ {c : Fin C // owner c=team}) (l : ReportLayout) (r : Fin C → ReportCell l)
    (recv : A → Fin C) (incoming : A → ℕ) (load : assignedSum (owner ∘ recv) team incoming ≤ X)
    (bundles : BitDelivery (fun j : (c : Fin C) × Fin (r c).bundles.length => j.1) (fun _ => description) recv incoming)
    (places : Fin C → Placed Site)
    (pub : assignedSum owner team (fun c => ((places c).parts.flatMap Part.publicBuffer).length) ≤ 2^p)
    (number : ∀ c, (places c).reports.length=l.gadgets) (width : ∀ c, ∀ v ∈ (places c).reports, v.length=l.countWidth)
    (R H B : ℕ) (original : ((c : {c : Fin C // owner c=team}) × UsePositions (r c.val).bundles) ↪
      Diagonal.CellEntries.PowerSlot (Fin R) (Fin H) B) (q : ReportCursor) (base : ℕ) (m : ℕ → ℕ) :
    let cs := List.ofFn (fun i => r (order i).val)
    cellInputs w description cs q base m →
    prepareSetup.slots+cellTicks cs q+(writeFrame 32 60 61 35).slots ≤
      54+79*count+105*2^p+516*X+131*(R*(H*B)) := by
  intro cs input
  have size : cs.length=count := List.length_ofFn
  have bound := original_team_le cs q base m input
  have del := (bundles.ordinal_load (fun c => (r c).bundles.length) description owner team).trans load
  have eq := report_sum owner team order r (fun c => c.bundles.length)
  change (cs.map (fun c => c.bundles.length)).sum = assignedSum owner team (fun c => (r c).bundles.length) at eq
  rw [←eq] at del
  have one := Nat.le_mul_of_pos_left (cs.map (fun c => c.bundles.length)).sum positive
  rw [Nat.mul_assoc,Nat.add_mul,Nat.one_mul] at bound
  have orig : teamOriginal cs*(l.fieldWidth+1) ≤ 4*X := by omega
  have use := owned_use_le owner team (fun c => (r c).bundles) original
  have corr := report_sum owner team order r (fun c => weightedCopies c.bundles)
  change teamWeighted cs = _ at corr
  have weighted : teamWeighted cs ≤ R*(H*B) := corr.trans_le use
  have gp := count_public_capacity owner team order l places number width pub
  have e := prepare_sparse_charge cs q
  rw [size] at e
  have paid : (105*l.gadgets+16*(l.gadgets*l.countWidth))*count ≤ 105*(2^p) := by
    apply le_trans _ (Nat.mul_le_mul_left 105 gp)
    calc
      _ ≤ (105*(l.gadgets+l.gadgets*l.countWidth))*count := Nat.mul_le_mul_right count (by omega)
      _ = _ := by ring
  nlinarith only [e,paid,orig,weighted]
end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
