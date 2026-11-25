import OAI.Computability.BorderVNP.CellTeamGeometryCharge

/-! # Complete sparse input charge for the Section 11 owned cell tasks

The common geometry packet pays for its public words, its box ordinals and all
count addresses. Both original-site tables and per-bundle binding records charge
the delivered source intervals. Extra individual-use bits are indexed by their
original batch, parameter and binary place.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.TypedBatch

open BorderVNP.Cube Cube.Physical Cube.TeamRowClock Crossing Packing.CellAddresses CellPacket
open DiagonalTallyCellReports CellSparse CellSparse.Packet CellSparse.Packet.Source CellPacketGeometry
open scoped Classical

private theorem report_width {l : ReportLayout} {Site : Type} (p : Placed Site)
    (number : p.reports.length=l.gadgets) (widths : ∀ v ∈ p.reports, v.length=l.countWidth) :
    l.gadgets*l.countWidth ≤ (p.parts.flatMap Part.publicBuffer).length := by
  have eq : (p.reports.map List.length).sum = p.reports.length*l.countWidth := by
    rw [List.map_congr_left (g := fun _ => l.countWidth) (fun v h => widths v h)]
    simp
  rw [←number,←eq]
  exact count_digits_le_public p

/-- Account for the genuine public and private parts of a supplemented packet.
The true external input may be either a contiguous field or a compressed stream. -/
theorem prepared_by_width {Site A : Type} [Fintype A] {dim blocks b K h : ℕ}
    {g : GroupWeights.Layout} {teams : TeamNative.Layout} {orig assigned : ℕ → ℕ} {D : LengthDeclaration dim g.groups}
    {label : Fin g.cells → Label (dim+1) g.groups} {recv : A → Fin g.cells} {incoming : A → ℕ}
    (schedule : GroupWeights.ScheduleResult g teams orig assigned)
    (image : GroupWeights.PhysicalImage g orig blocks b K h D label recv incoming)
    (team : Fin (teams.r+1)) (X w description : ℕ) (positive : 1 ≤ description)
    (pass : TeamNative.unscale (assigned (teams.totals+team.val)) ≤ (X:ℚ)/256)
    (places : Fin g.cells → Placed Site) (p d : ℕ)
    (counts : ∀ owner team, assignedSum owner team (fun c => ((places c).parts.flatMap Part.publicBuffer).length) ≤ 2^p ∧
      assignedSum owner team (fun c => (places c).boxes.length+6) ≤ 2^d)
    (l : ReportLayout) (r : Fin g.cells → ReportCell l) (cursor : Fin g.cells → LocalReportCursor)
    (bundleBase : Fin g.cells → ℕ) (memory : Fin g.cells → ℕ → ℕ)
    (rc : ∀ c, (places c).reports.length=l.gadgets)
    (digits : ∀ c, ∀ v ∈ (places c).reports, v.length=l.countWidth)
    (supply : Fin g.cells → ℕ) (limit : ℕ)
    (exterior : ∀ c, assigned (teams.owners+(label c D.1).val)=team.val →
      (places c).external.length=supply c+(r c).tailWidth)
    (hidden : BitDelivery (fun j : (c : Fin g.cells) × Fin ((places c).boxes.filterMap Sum.getRight?).length => j.1)
      (fun _ => description) recv incoming)
    (bundles : BitDelivery (fun j : (c : Fin g.cells) × Fin (r c).bundles.length => j.1) (fun _ => description) recv incoming)
    (R H B : ℕ) :
    let owner := fun c : Fin g.cells => assigned (teams.owners+(label c D.1).val)
    assignedSum owner team.val supply ≤ limit →
    (∀ c, owner c=team.val → bundleInputs w l description (r c).bundles (cursor c) (bundleBase c) (memory c)) →
    (((c : {c : Fin g.cells // owner c=team.val}) × UsePositions (r c.val).bundles) ↪
      Diagonal.CellEntries.PowerSlot (Fin R) (Fin H) B) →
    assignedSum owner team.val (fun c => Supplement.units (places c) (bindingRows (r c).bundles (cursor c)) w description) ≤
      2*(w+1)*(2^p+2^d) + 18*(w+1)*X + 2*X + limit + R*(H*B) := by
  intro owner supplied bundleInput original
  let selected := Finset.univ.filter fun c => owner c=team.val
  let Pwords (c : Fin g.cells) := ((places c).parts.flatMap Part.publicBuffer).length
  let Box (c : Fin g.cells) := (places c).boxes.length+6
  let O (c : Fin g.cells) := ((places c).boxes.filterMap Sum.getRight?).length
  let Fwords (c : Fin g.cells) := ((bindingRows (r c).bundles (cursor c)).flatMap record).length
  let U (c : Fin g.cells) := ((r c).bundles.map ReportBundle.useCount).sum
  let weight (f : Fin g.cells → ℕ) := ∑ c ∈ selected, f c
  have re (f : Fin g.cells → ℕ) : assignedSum owner team.val f = weight f := assigned_eq_sum ..
  obtain ⟨pub,box⟩ := counts owner team.val
  change assignedSum owner team.val Pwords ≤ 2^p at pub
  change assignedSum owner team.val Box ≤ 2^d at box
  rw [re] at pub box
  obtain ⟨del,_⟩ := assigned_input_bounds schedule image team X pass
  change assignedSum (owner ∘ recv) team.val incoming ≤ X at del
  have o := (hidden.ordinal_load O description owner team.val).trans del
  have ob := (bundles.ordinal_load (fun c => (r c).bundles.length) description owner team.val).trans del
  rw [re] at o ob
  have Fbound : weight Fwords ≤ 18*X := by
    have each (c : Fin g.cells) (hc : c ∈ selected) :
        Fwords c ≤ 18*description*(r c).bundles.length := by
      have h := binding_words_le l _ _ _ _ (bundleInput c (Finset.mem_filter.mp hc).2)
      exact h.trans (Nat.mul_le_mul_right _ (by omega))
    have h := Finset.sum_le_sum (s:=selected) each
    rw [←Finset.mul_sum,Nat.mul_assoc] at h
    exact h.trans (Nat.mul_le_mul_left 18 ob)
  have metadataCost : (description+1)*weight O ≤ 2*X := by
    have bound := Nat.le_mul_of_pos_left (weight O) positive
    rw [Nat.add_mul,Nat.one_mul]; omega
  rw [re] at supplied
  have uses := owned_use_le owner team.val (fun c => (r c).bundles) original
  change assignedSum owner team.val U ≤ R*(H*B) at uses
  rw [re] at uses
  have countBits : weight (fun _ => l.gadgets*l.countWidth) ≤ weight Pwords :=
    Finset.sum_le_sum (fun c _ => report_width (places c) (rc c) (digits c))
  have eq (c : Fin g.cells) (hc : owner c=team.val) : Supplement.units (places c) (bindingRows (r c).bundles (cursor c)) w description =
      (w+1)*(Pwords c+Box c+Fwords c) + (description+1)*O c + supply c + l.gadgets*l.countWidth + U c := by
    rw [Supplement.units,Placed.units_plan,exterior c hc,ReportCell.tailWidth]
    dsimp only [Pwords,Box,Fwords,O,U]
    ring
  rw [assigned_eq_sum]
  change (∑ c ∈ selected, _) ≤ _
  rw [Finset.sum_congr rfl (fun c (hc : c ∈ selected) => eq c (Finset.mem_filter.mp hc).2)]
  simp only [Finset.sum_add_distrib,←Finset.mul_sum]
  rw [show l.gadgets*(∑ _ ∈ selected,l.countWidth) = weight (fun _ => l.gadgets*l.countWidth) from Finset.mul_sum ..]
  change (w+1)*(weight Pwords+weight Box+weight Fwords)+(description+1)*weight O+weight supply+
    weight (fun _ => l.gadgets*l.countWidth)+weight U ≤ _
  have geom := Nat.mul_le_mul_left (w+1) (Nat.add_le_add pub box)
  have extra := Nat.mul_le_mul_left (w+1) Fbound
  have pay : weight Pwords ≤ (w+1)*(2^p+2^d) := pub.trans ((Nat.le_add_right ..).trans (Nat.le_mul_of_pos_left _ (by omega)))
  rw [Nat.mul_add (w+1) _ (weight Fwords)]
  calc
    _ ≤ (w+1)*(2^p+2^d)+(w+1)*(18*X)+2*X+limit+(w+1)*(2^p+2^d)+R*(H*B) :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add geom extra) metadataCost) supplied)
        (countBits.trans pay)) uses
    _ = _ := by ring

/-- True source ordinals, geometry sections and group-schedule loads bound the sum
of every native input unit in the owned supplemental tasks. The hypothesis about
power slots is a map on individual marked uses and preserves their multiplicity. -/
theorem prepared_units {Site E I A P : Type} [Fintype A] [Fintype P] {z s dim edges blocks b K h : ℕ}
    {g : GroupWeights.Layout} {teams : TeamNative.Layout} {orig assigned : ℕ → ℕ} {D : LengthDeclaration dim g.groups}
    {label : Fin g.cells → Label (dim+1) g.groups} {recv : A → Fin g.cells} {incoming : A → ℕ}
    {bits : P → ℕ} (N : Network z P bits) (cell : N.Site → Fin g.cells) (ord : N.CrossingEdge cell ≃ Fin edges)
    (schedule : GroupWeights.ScheduleResult g teams orig assigned)
    (image : GroupWeights.PhysicalImage g orig blocks b K h D label recv incoming)
    (team : Fin (teams.r+1)) (X w description : ℕ) (positive : 1 ≤ description)
    (pass : TeamNative.unscale (assigned (teams.totals+team.val)) ≤ (X:ℚ)/256)
    (capacity : ∀ pair, load (cablePair ord (crossSrc N cell) (crossDst N cell) label)
      (crossWidth N cell ∘ ord.symm) pair ≤ blocks*(h*b))
    (portDelivery : BitDelivery (cell ∘ N.attach) bits recv incoming)
    (T : LiveWords.Template E I Site s g.cells) (site : Fin s → Fin g.cells) (arg : E → ℕ)
    (fields : Fin s → I → ℕ) (places : Fin g.cells → Placed Site) (shape : SourceShape places (T.directory site arg fields))
    (p d : ℕ) (pf : g.cells+T.atoms.length+g.cells ≤ 2^p)
    (df : g.cells+(Schema.coords T.chunkLabels.length).length+g.cells ≤ 2^d)
    (l : ReportLayout) (r : Fin g.cells → ReportCell l) (cursor : Fin g.cells → LocalReportCursor)
    (bundleBase : Fin g.cells → ℕ) (memory : Fin g.cells → ℕ → ℕ)
    (rc : ∀ c, (places c).reports.length=l.gadgets)
    (digits : ∀ c, ∀ v ∈ (places c).reports, v.length=l.countWidth)
    (exterior : ∀ c, (places c).external.length=suppliedSize N cell c+(r c).tailWidth)
    (hidden : BitDelivery (fun j : (c : Fin g.cells) × Fin ((places c).boxes.filterMap Sum.getRight?).length => j.1)
      (fun _ => description) recv incoming)
    (bundles : BitDelivery (fun j : (c : Fin g.cells) × Fin (r c).bundles.length => j.1) (fun _ => description) recv incoming)
    (R H B : ℕ) :
    let owner := fun c : Fin g.cells => assigned (teams.owners+(label c D.1).val)
    (∀ c, owner c=team.val → bundleInputs w l description (r c).bundles (cursor c) (bundleBase c) (memory c)) →
    (((c : {c : Fin g.cells // owner c=team.val}) × UsePositions (r c.val).bundles) ↪
      Diagonal.CellEntries.PowerSlot (Fin R) (Fin H) B) →
    assignedSum owner team.val (fun c => Supplement.units (places c) (bindingRows (r c).bundles (cursor c)) w description) ≤
      2*(w+1)*(2^p+2^d) + 18*(w+1)*X + 3*X + 2*(1000000*X/256) + R*(H*B) := by
  intro owner bundleInput original
  have supplied := supplied_le N cell ord schedule image team X pass capacity portDelivery
  have paid := prepared_by_width schedule image team X w description positive pass places p d
    (geometry_counts T site arg fields places shape pf df) l r cursor bundleBase memory rc digits (fun c => suppliedSize N cell c) (2*(1000000*X/256)+X)
    (fun c _ => exterior c) hidden bundles R H B supplied bundleInput original
  dsimp only [owner]
  omega

end RoutingISA.TypedBatch

end BorderVNP
end Computability
end OAI
