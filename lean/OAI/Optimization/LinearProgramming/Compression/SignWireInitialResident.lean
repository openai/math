import OAI.Optimization.LinearProgramming.Compression.SignWireInitialResidentTerms
import OAI.Optimization.LinearProgramming.Compression.SignWireResidentData
import OAI.Optimization.LinearProgramming.Compression.SymbolicWorkspaceAllocator
import OAI.Optimization.LinearProgramming.Compression.ProxyDriverMetadata
import OAI.Optimization.LinearProgramming.Compression.BlockFootprint

/-! First entry into the cached numerical comparison service. The ordinary
caller allocates its own row and both work tapes before the physical scatter. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace SignWire

open RAM RAM.Callable MinorProxyCache

def initialResidentZero : Memory ℚ := ⟨fun _ => 0,fun _ => 0⟩

private theorem afterHeaderCache {m t : Memory ℚ} {L : Buffers} {d fuel prec : ℕ}
    {mag : ℕ → ℚ} (h : InitialResidentHeader m t L d fuel) (cache : StableCache m L d fuel prec mag) :
    StableCache t L d fuel prec mag := by
  have flagHigh := cache.separated.flagHigh
  refine ⟨cache.header.transfer (fun i lo hi => h.high i (by omega) (by omega) (by omega) (by omega)),
    cache.separated,?_,cache.positive,?_,?_,
    (h.high 61 (by decide) (by decide) (by decide) (by decide)).trans cache.any,
    (h.high 62 (by decide) (by decide) (by decide) (by decide)).trans cache.zero,
    by rw [h.data];exact cache.scale⟩
  · intro i hi
    rw [h.data];exact cache.magnitude i hi
  · intro i hi
    rw [h.data];exact cache.numerator i hi
  · intro i hi
    exact (h.high _ (by omega) (by omega) (by omega) (by omega)).trans (cache.symbolic i hi)

theorem initialResidentRow_apart (L : Buffers) (d : ℕ) :
    RowAwayFromCache L d (initialResidentRow L d) := by
  unfold initialResidentRow
  exact ⟨Or.inr (by omega),Or.inr (by omega),Or.inl (by omega)⟩

private theorem initialResidentFloor_valid {m t : Memory ℚ} {L : Buffers} {d fuel : ℕ}
    (h : InitialResidentHeader m t L d fuel) :
    SymbolicWorkspaceFloor t L d (initialResidentRow L d+d+1) := by
  have r := h.row
  dsimp [initialResidentRow] at r ⊢
  exact ⟨by omega,by omega,by omega,by omega,by omega,by omega,by omega⟩

private theorem initialNative_footprint (C : ℕ) : Footprint C (initialResidentZero.atPC 0) :=
  ⟨fun _ => Nat.zero_le _,fun _ _ => rfl,fun _ _ => rfl⟩

theorem initialResidentBlock_spec {d fuel prec H N g member rank : ℕ} {L : Buffers} {mag : ℕ → ℚ}
    (m : Memory ℚ) {P : ℚ → Prop} (cache : StableCache m L d fuel prec mag)
    (metadata : ProxyDriverMetadata N g member rank m) (hm : m.AllData P) (fin : Footprint H (m.atPC 0)) :
    ∃ k t, Block.Eval (Memory.AllData P) initialResidentBlock m k t ∧ k ≤ initialResidentClock H d fuel ∧
      ResidentNumeric (n:=d) mag L fuel prec (symbolicQueryCap d fuel) (initialResidentBound H d fuel)
        (initialResidentRow L d) P initialResidentZero t ∧
      Footprint (initialResidentBound H d fuel) (t.atPC 0) ∧ ProxyDriverMetadata N g member rank t ∧
      (∀ i, 98 ≤ i → t.index i=m.index i) ∧ t.data=m.data ∧
      t.index 97=initialResidentRow L d+d+1 ∧ initialResidentRow L d+d ≤ initialResidentBound H d fuel := by
  obtain ⟨j,s,header,hj,h⟩ := initialResidentHeader_spec m cache hm fin.address
  have cs := afterHeaderCache h cache
  obtain ⟨t,allocate,layout,ct,work,res⟩ := initializeSymbolicWorkspace cs
    (initialResidentFloor_valid h) header.safe_end h.floor
  let k := j+symbolicWorkspaceSteps d fuel
  have run : Block.Eval (Memory.AllData P) initialResidentBlock m k t := header.seq allocate
  have hk : k ≤ initialResidentClock H d fuel := Nat.add_le_add_right hj _
  have finalFoot : Footprint (initialResidentBound H d fuel) (t.atPC 0) :=
    (powerPackingStage_footprint run fin).mono (Nat.add_le_add_left hk _)
  have P0 : P 0 := by
    have zero : m.data (H+1)=0 := fin.data_zero (H+1) (by omega)
    exact zero ▸ hm (H+1)
  have high (i : ℕ) (hi : 98 ≤ i) : t.index i=m.index i :=
    (layout.kept i (by omega) (by omega)).trans (h.high i (by omega) (by omega) (by omega) (by omega))
  have endRow := (layout.kept 97 (by decide) (by decide)).trans h.floor
  have room : t.index 97 ≤ initialResidentBound H d fuel := finalFoot.address 97
  refine ⟨k,t,run,hk,?_,finalFoot,?_,high,layout.data.trans h.data,endRow,by omega⟩
  · exact ⟨ct,work,res,(layout.kept 67 (by decide) (by decide)).trans h.row,initialResidentRow_apart L d,
      allocate.safe_end,fun _ => P0,initialNative_footprint _,
      (layout.kept 60 (by decide) (by decide)).trans h.capacity,finalFoot.address⟩
  · exact ⟨(high 102 (by decide)).trans metadata.dimension,(high 103 (by decide)).trans metadata.generators,
      (high 104 (by decide)).trans metadata.membership,(high 105 (by decide)).trans metadata.position⟩

/-- Changing the upper bound used by the controller changes only the certified
address inequality. The allocated pointers stay available to the scatter. -/
theorem ResidentNumeric.mono_bound {n fuel prec C R R' base : ℕ} {mag : ℕ → ℚ} {L : Buffers}
    {P : ℚ → Prop} {old t : Memory ℚ} (h : ResidentNumeric (n:=n) mag L fuel prec C R base P old t)
    (le : R ≤ R') : ResidentNumeric (n:=n) mag L fuel prec C R' base P old t :=
  { h with callerBound := fun i => (h.callerBound i).trans le }

end SignWire
end Compression
end LinearProgramming
end Optimization
end OAI
