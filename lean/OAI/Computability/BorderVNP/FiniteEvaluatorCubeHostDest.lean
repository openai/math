import OAI.Computability.BorderVNP.CubeRouteDirectoryPass
import OAI.Computability.BorderVNP.CubeHostScatterSetup
import OAI.Computability.BorderVNP.PackedRoutingHeaders

/-! # Owned host scatter destinations in the allocated receiving-cell banks -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.CubeAllocation

open BorderVNP.Cube RoutingISA Packing Crossing

variable (a : CubeArena.Layout) (frame : ℕ) (mem : ℕ → ℕ)

local notation "H" => HostScatter.Layout.fromFrame frame mem

/-- Every owned endpoint interval stays in the receiving allocation when its decoded
cell and relative interval fit the physical two-word cell directory. -/
theorem host_dest (ptr : mem (frame+72) = a.hostDirectory)
    (bank : ∀ c < a.cells, mem (a.hostDirectory+2*c+1) = a.cellBank+c*a.cellStride)
    (ends : ∀ i < (H).count, ∀ side, (H).Owned mem i side →
      (H).cell mem i side < a.cells ∧ mem ((H).relative+2*i+side.toNat)+(H).width mem i ≤ a.cellStride) :
    ∀ i < (H).count, ∀ side, (H).Owned mem i side →
      a.cellBank ≤ (H).dest mem i side ∧ (H).dest mem i side+(H).width mem i ≤ a.stop := by
  intro i hi side owned
  obtain ⟨hc, hr⟩ := ends i hi side owned
  let c := (H).cell mem i side
  have step := Nat.mul_le_mul_right a.cellStride (Nat.succ_le_of_lt hc)
  change (c+1)*a.cellStride ≤ a.cells*a.cellStride at step
  rw [Nat.succ_mul] at step
  change a.cellBank ≤ mem (mem (frame+72)+2*c+1) + mem ((H).relative+2*i+side.toNat) ∧
    mem (mem (frame+72)+2*c+1) + mem ((H).relative+2*i+side.toNat) + (H).width mem i ≤
      a.cellBank+a.cells*a.cellStride
  rw [ptr,bank c hc]
  omega

/-- A preserved bank-pointer column of the actual cell writer gives all absolute
destination bases consumed by the host scatter. -/
theorem host_banks_written (controls : ℕ) (axis : Fin (a.n+1)) (old : ℕ → ℕ)
    (keep : ∀ c < a.cells, mem (a.hostDirectory+2*c+1) =
      (a.cellWriter frame controls axis).written old a.cells (a.hostDirectory+2*c+1)) :
    ∀ c < a.cells, mem (a.hostDirectory+2*c+1) = a.cellBank+c*a.cellStride := by
  intro c hc
  exact (keep c hc).trans ((a.cellWriter frame controls axis).written_at old hc).2

open CellAddresses CellAddressCircuit CellAddressPhysical RoutingOutputs

/-- On the published sparse geometry, every positive-width row comes from a true crossing edge.
Its actual endpoint and last lane lie in that cell's supplied input prefix. -/
theorem host_ends_supplied {D s m n d k w J A origin : ℕ} {P σ : Type*} [Fintype P] [Fintype σ]
    {bits : P → ℕ} (N : Network D P bits) (cell : N.Site → Fin a.cells) (aux : N.Site → ℕ)
    (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n)
    (F : Fields s m n a.cells d k w σ) {x : σ → Bool} {old : Fin J → Fin s} {ports : Fin A → Fin n}
    (rep : Represents N cell aux siteID edgeID portID F x) (codes : ∀ c, (F.cells c).val = c.val)
    (fit : ∀ c, guessedSize N cell c + siteSize N cell c aux + suppliedSize N cell c < 2^w)
    {geo : ℕ → ℕ}
    (hdr : RoutingOutputs.Header frame origin m a.cells J mem) (img : RoutingOutputs.Image F old ports x origin geo)
    (keep : ∀ z, origin ≤ z → z < origin+5*m → mem z = geo z) :
    ∀ i < (H).count, ∀ side, (H).width mem i ≠ 0 →
      ∃ c : Fin a.cells, (H).cell mem i side=c.val ∧
        mem ((H).relative+2*i+side.toNat)+(H).width mem i ≤ suppliedSize N cell c := by
  intro i hi side nz
  have count : (H).count = m := hdr.edges
  let j : Fin m := ⟨i, count ▸ hi⟩
  have cable : (H).cables = origin := hdr.cables
  have relative : (H).relative = (bases origin m a.cells J).ends := hdr.ends
  have col (u : Fin 3) : mem ((H).cables+3*i+u.val) = CableTriples.get (CableTriples.row F x j) u := by
    rw [cable,Nat.mul_comm 3 i]
    have him : i < m := j.isLt
    have hu := u.isLt
    rw [keep _ (by omega) (by omega)]
    exact img.cable j u
  have wid : (H).width mem i = (CableTriples.row F x j).width := col 2
  rw [wid] at nz
  have found : j ∈ Set.range (CableTriples.wireOrd N cell edgeID) := by
    by_contra missing
    exact nz (congrArg Cube.LabelIndex.Cable.width (CableTriples.row_unused N cell aux siteID edgeID portID F rep codes j missing))
  obtain ⟨e, he⟩ := found
  have row := CableTriples.row_crossing N cell aux siteID edgeID portID F rep codes e
  rw [he] at row
  have positive : N.width e.val ≠ 0 := by
    intro zero
    rw [ite_eq_left zero] at row
    exact nz (congrArg Cube.LabelIndex.Cable.width row)
  rw [ite_eq_right positive] at row
  have actual := wid.trans (congrArg Cube.LabelIndex.Cable.width row)
  let last : Fin (N.width e.val) := ⟨N.width e.val-1,by omega⟩
  have offset (u : Fin 2) : mem ((H).relative+2*i+u.val) =
      ParseBatchSort.value (fun b => (SuppliedOffsets.frame F).eval x (.inl (endpoint (edgeID e.val) u),b)) := by
    rw [relative,Nat.mul_comm 2 i]
    have him : i < m := j.isLt
    have hu := u.isLt
    rw [keep _ (by dsimp [bases]; omega) (by dsimp [bases]; omega)]
    have eq : edgeID e.val = j := he
    rw [eq]
    exact img.endAt j u
  have lastEnd (off : ℕ) (c : Fin a.cells) (small : off+last.val < suppliedSize N cell c) :
      off+(H).width mem i ≤ suppliedSize N cell c := by
    change (H).width mem i = N.width e.val at actual
    dsimp only [last] at small
    omega
  cases side with
  | false =>
    have src : (H).cell mem i false = (cell (N.src e.val)).val :=
      (col 0).trans (congrArg (fun z => CableTriples.get z 0) row)
    refine ⟨cell (N.src e.val),src, lastEnd _ (cell (N.src e.val)) ?_⟩
    change mem ((H).relative+2*i+(0 : Fin 2).val)+last.val < _
    rw [offset 0]
    have lane := SuppliedOffsets.source_lane N cell aux siteID edgeID portID F rep fit e last
    exact lane.trans_lt (suppliedOrdinal N cell _ edgeID portID (.inl ⟨e,.inl rfl⟩) last).isLt
  | true =>
    have dst : (H).cell mem i true = (cell (N.dst e.val)).val :=
      (col 1).trans (congrArg (fun z => CableTriples.get z 1) row)
    refine ⟨cell (N.dst e.val),dst, lastEnd _ (cell (N.dst e.val)) ?_⟩
    change mem ((H).relative+2*i+(1 : Fin 2).val)+last.val < _
    rw [offset 1]
    have lane := SuppliedOffsets.dest_lane N cell aux siteID edgeID portID F rep fit e last
    exact lane.trans_lt (suppliedOrdinal N cell _ edgeID portID (.inl ⟨e,.inr rfl⟩) last).isLt

/-- On the published sparse geometry, every positive-width row comes from a true crossing edge.
Its last supplied lane fits the stride of the physical endpoint's cell. -/
theorem host_ends_positive {D s m n d k w J A origin : ℕ} {P σ : Type*} [Fintype P] [Fintype σ]
    {bits : P → ℕ} (N : Network D P bits) (cell : N.Site → Fin a.cells) (aux : N.Site → ℕ)
    (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n)
    (F : Fields s m n a.cells d k w σ) {x : σ → Bool} {old : Fin J → Fin s} {ports : Fin A → Fin n}
    (rep : Represents N cell aux siteID edgeID portID F x) (codes : ∀ c, (F.cells c).val = c.val)
    (fit : ∀ c, guessedSize N cell c + siteSize N cell c aux + suppliedSize N cell c < 2^w)
    (room : ∀ c, suppliedSize N cell c ≤ a.cellStride) {geo : ℕ → ℕ}
    (hdr : RoutingOutputs.Header frame origin m a.cells J mem) (img : RoutingOutputs.Image F old ports x origin geo)
    (keep : ∀ z, origin ≤ z → z < origin+5*m → mem z = geo z) :
    ∀ i < (H).count, ∀ side, (H).width mem i ≠ 0 →
      (H).cell mem i side < a.cells ∧ mem ((H).relative+2*i+side.toNat)+(H).width mem i ≤ a.cellStride := by
  intro i hi side nz
  obtain ⟨c,hc,bound⟩ := host_ends_supplied a frame mem N cell aux siteID edgeID portID F
    rep codes fit hdr img keep i hi side nz
  exact ⟨hc ▸ c.isLt,bound.trans (room c)⟩

/-- On the published sparse geometry, every owned row comes from a true crossing edge.
Its last supplied lane fits the stride of the physical endpoint's cell. -/
theorem host_ends_geometry {D s m n d k w J A origin : ℕ} {P σ : Type*} [Fintype P] [Fintype σ]
    {bits : P → ℕ} (N : Network D P bits) (cell : N.Site → Fin a.cells) (aux : N.Site → ℕ)
    (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n)
    (F : Fields s m n a.cells d k w σ) {x : σ → Bool} {old : Fin J → Fin s} {ports : Fin A → Fin n}
    (rep : Represents N cell aux siteID edgeID portID F x) (codes : ∀ c, (F.cells c).val = c.val)
    (fit : ∀ c, guessedSize N cell c + siteSize N cell c aux + suppliedSize N cell c < 2^w)
    (room : ∀ c, suppliedSize N cell c ≤ a.cellStride) {geo : ℕ → ℕ}
    (hdr : RoutingOutputs.Header frame origin m a.cells J mem) (img : RoutingOutputs.Image F old ports x origin geo)
    (keep : ∀ z, origin ≤ z → z < origin+5*m → mem z = geo z) :
    ∀ i < (H).count, ∀ side, (H).Owned mem i side →
      (H).cell mem i side < a.cells ∧ mem ((H).relative+2*i+side.toNat)+(H).width mem i ≤ a.cellStride :=
  fun i hi side owned => host_ends_positive a frame mem N cell aux siteID edgeID portID F rep codes fit room hdr img keep i hi side owned.1

/-- Containment for the real post-directory host pass. Later stages need only retain
the emitted geometry's cable and offset columns and the writer's bank-pointer column. -/
theorem host_dest_of_publication {D s m n d k w J A origin controls R : ℕ} {P σ : Type*}
    [Fintype P] [Fintype σ] {bits : P → ℕ} (N : Network D P bits) (cell : N.Site → Fin a.cells)
    (aux : N.Site → ℕ) (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n)
    (F : Fields s m n a.cells d k w σ) {x : σ → Bool} {old : Fin J → Fin s} {ports : Fin A → Fin n}
    (rep : Represents N cell aux siteID edgeID portID F x) (codes : ∀ c, (F.cells c).val = c.val)
    (fit : ∀ c, guessedSize N cell c + siteSize N cell c aux + suppliedSize N cell c < 2^w)
    (room : ∀ c, suppliedSize N cell c ≤ a.cellStride) {geo input scheduled written : ℕ → ℕ}
    (hdr : RoutingOutputs.Header frame origin m a.cells J mem) (img : RoutingOutputs.Image F old ports x origin geo)
    (keepGeo : ∀ z, origin ≤ z → z < origin+5*m → mem z = geo z) (axis : Fin (a.n+1))
    (pub : CubeArena.DirectoryImage a frame controls axis R input scheduled written)
    (ptr : mem (frame+72) = a.hostDirectory)
    (keepBank : ∀ c < a.cells, mem (a.hostDirectory+c*2+1) = written (a.hostDirectory+c*2+1)) :
    ∀ i < (H).count, ∀ side, (H).Owned mem i side →
      a.cellBank ≤ (H).dest mem i side ∧ (H).dest mem i side+(H).width mem i ≤ a.stop := by
  apply host_dest a frame mem ptr _ (host_ends_geometry a frame mem N cell aux siteID edgeID portID
    F rep codes fit room hdr img keepGeo)
  intro c hc
  rw [Nat.mul_comm 2 c,keepBank c hc]
  exact (pub.hostRows c hc).2

end FiniteEvaluator.CubeAllocation

end BorderVNP
end Computability
end OAI
