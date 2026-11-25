import OAI.Computability.BorderVNP.DiagonalPositiveCoreReceived
import OAI.Computability.BorderVNP.PackedFinalAssignedRetained

/-! # Passing native reports of every genuinely guarded original routed core -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeAssignments

open Filter Crossing Packing Packing.CellAddresses Packing.BottomReports Packing.Inherited
open Site.Programs CellSparse DiagonalTallyCellReports TeamScales
open scoped Classical

set_option maxHeartbeats 2000000
set_option maxRecDepth 12000

/-- Source and size hypotheses for the actual retained, owner-numbered
directories and the genuine bottom bundles in each frozen received row. -/
structure ReceivedBounds {T C D ns : ℕ} {P J : Type} [Fintype P] [Fintype J] {bits : P → ℕ}
    {layout : Fin T → ReportLayout} (R : ReceivedRows layout C) (N : Network D P bits)
    (cell : N.Site → Fin C) (siteID : N.Site ↪ Fin ns) (owner : Fin ns → ℕ) (state : Site.Programs N)
    (host : J ↪ N.Site) (bundle : J → Bundle) (origins : Fin C → List J)
    (M E Z high table rows digitBound : ℕ) : Prop where
  ownerID : ∀ v,owner (siteID v)=(cell v).val
  incoming : ∀ v,(state v).program.incoming=Packing.Inherited.incoming N v
  schema : ∀ v,(state v).program.Schema
  locality : ∀ v,(state v).program.Local
  relative : ∀ v,(state v).program.RelativeBoxes
  unsigned : ∀ v,(state v).program.SignFree
  publicLoad : ∀ c : Fin C,Shortening.localRecords N false (fun v => (state v).program.staticNodes)
    (fun v => (state v).program.expandedLoad) (fun v => (cell v).val=c.val) ≤ M
  expandedLoad : ∀ c : Fin C,Shortening.localRecords N true (fun v => (state v).program.staticNodes)
    (fun v => (state v).program.expandedLoad) (fun v => (cell v).val=c.val) ≤ M
  gadgetCount : ∀ u,(layout u).gadgets ≤ M+1
  countWidth : ∀ u,(layout u).countWidth ≤ M+1
  widthBound : ∀ u,(layout u).countWidth ≤ digitBound
  digitFit : ∀ u,M < 2^(layout u).countWidth
  space : ∀ u,3*M+(layout u).gadgets*(layout u).countWidth ≤ E
  scalars : ∀ v,(state v).program.ScalarBound Z
  rowSize : ∀ v,(state v).program.RowBound rows
  tableSize : ∀ v,(state v).program.TableBound table
  split : ∀ v,(state v).program.SplitFields (4*(M+E+1)^3) high
  ids : ∀ u i v, v ∈ FinalCell.sites siteID owner (R.order ⟨u,i⟩).val →
    ∀ fs∈(state v).program.boxes,∀ f∈fs,f.IDRange (layout u).gadgets
  retained : RetainedBirths N (fun v => (cell v).val) (fun v => (state v).program) siteID host bundle
  unique : ∀ c,(origins c).Nodup
  belongs : ∀ c j,j ∈ origins c → (cell (host j)).val=c.val
  copies : ∀ c j,j ∈ origins c → 0<(bundle j).header.copies ∧ 0<(bundle j).header.stride
  uses : ∀ u i,(((R.cells u).get i).bundles.map ReportBundle.useCount).sum =
    (((origins (R.order ⟨u,i⟩)).map bundle).map Bundle.useBits).sum

/-- After the true native core guards pass, every real cell in its owner's
native report batch is passing. The private time bound applies to all
proposed report spellings and the radius and word-width schedule is uniform
over the core, the padding, and the choice of route. -/
theorem eventually_guarded_reports (table rows B j coeff k : ℕ) (enough : 9≤rows) :
    ∃ ω : ℝ,0<ω ∧ ∀ᶠ order : ℕ in atTop, ∀ r M E w Z high : ℕ,
      1≤r → (r:ℝ)≤2^((order:ℝ)^ω) → M≤TeamScales.width order (1/5) → E≤TeamScales.width order (1/4) →
      0<w → w≤order → high.size+1≤B*(logWidth r order+1)^j → 3*M+Z≤4*(M+E+1)^3 →
      ∀ {T C D ns ne np n d blocks b h K s : ℕ} {P J Team : Type} [Fintype P] [Fintype J]
        {bits : P → ℕ} {layout : Fin T → ReportLayout} (R : ReceivedRows layout C)
        (N : Network D P bits) (cell : N.Site → Fin C) (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin ne)
        (portID : P ↪ Fin np) (state : Site.Programs N) (owners : (Packet n d blocks → Selector n K h) → Fin d → Team)
        (slot : LiveBit N cell ↪ Slot n d blocks (h*b)) (ports : Ports bits) (owner : Fin ns → ℕ)
        (host : J ↪ N.Site) (bundle : J → Bundle) (origins : Fin C → List J),
      ReceivedBounds R N cell siteID owner state host bundle origins M E Z high table rows (coeff*(logWidth r order+1)^k) →
      ∀ (q : Routed (b:=b) (s:=s) owners) (raw : (c : Fin C) → Fin (externalBase N cell c (placedSize N state)) → Bool),
      GuardedCores N cell siteID edgeID portID state owners slot ports owner (R.countReports N cell state) q raw →
      ∀ u A, A ∈ R.assigned N cell siteID edgeID portID state owners slot ports owner (fun c => (origins c).map bundle)
        q raw u → A.Passing w order := by
  obtain ⟨ω,pos,event⟩ := FinalCell.eventually_retained_passing table rows B j coeff k enough
  refine ⟨ω,pos,?_⟩
  filter_upwards [event] with order valid
  intro r M E w Z high hr hω hM hE hw hwn bound size T C D ns ne np n d blocks b h K s P J Team instP instJ
    bits layout R N cell siteID edgeID portID state owners slot ports owner host bundle origins good q raw guard u A inList
  let bottom := fun c => (origins c).map bundle
  let key := fun v => (cell v).val
  let progs := fun v => (state v).program
  let row := R.assignedAt N cell siteID edgeID portID state owners slot ports owner bottom q raw
  change A ∈ List.ofFn (row u) at inList
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp inList
  let c := R.order ⟨u,i⟩
  let widths := FinalReports.bank_sizes N cell progs c
  let g := privateWires N cell (placedSize N state) c (raw c) ∘ Fin.cast widths.1
  let a := privateStaging N cell (placedSize N state) c (raw c) ∘ Fin.cast widths.2.1
  let x := pathSupply N cell edgeID portID owners slot ports q c ∘ Fin.cast widths.2.2
  have sg := sortedDirectory_signFree N key siteID edgeID portID owner progs c.val
    (countFields (FinalCell.countBase N key progs c.val) (layout u).gadgets (layout u).countWidth) good.unsigned
  have observed := R.assignedAt_observed N cell siteID edgeID portID state owners slot ports owner bottom q raw u i (guard.2 c)
  have pre : CellAddresses.bank N key c.val (fun v => (progs v).size) g a x = (row u i).pre := by
    change List.ofFn g ++ (List.ofFn a ++ List.ofFn x)=List.ofFn (Fin.append g a)++List.ofFn x
    rw [List.ofFn_fin_append,List.append_assoc]
  exact valid r M E w Z high hr hω hM hE hw hwn bound size N key siteID edgeID portID owner progs c.val
    ((R.cells u).get i) host bundle (origins c) good.ownerID good.incoming good.schema good.locality good.relative
    (good.publicLoad c) (good.expandedLoad c) (good.gadgetCount u) (good.countWidth u) (good.widthBound u)
    (good.digitFit u) (good.space u) (fun v _ => good.scalars v) (fun v _ => good.rowSize v) good.tableSize good.split
    (good.ids u i) good.retained (good.unique c) (good.belongs c) (good.copies c) (good.uses u i)
    g a x (row u i).observations sg (pre.symm ▸ observed)

end Cube.Physical.NativeAssignments

end BorderVNP
end Computability
end OAI
