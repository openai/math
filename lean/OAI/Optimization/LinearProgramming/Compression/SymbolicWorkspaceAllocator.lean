import OAI.Optimization.LinearProgramming.Compression.SymbolicWorkspaceAddress
import OAI.Optimization.LinearProgramming.Compression.SymbolicResidentLayout

/-! A counted allocator places all mixed-query work above a caller-selected
floor. The cache, complete query row, and any older high register below that
floor survive repeated use of these pages. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM RAM.Callable MinorProxyCache FieldTransfer

structure SymbolicWorkspaceFloor (m : Memory ℚ) (L : Buffers) (n floor : ℕ) : Prop where
  high : 128 ≤ floor
  rowHigh : 128 ≤ m.index 67
  rowEnd : m.index 67+n < floor
  magEnd : L.magBase+n ≤ floor
  gridEnd : L.gridBase+n ≤ floor
  flagEnd : L.flagBase+n ≤ floor
  scaleEnd : L.scalePtr < floor

/-- The first free address can be chosen by taking the maximum of resident
end pointers; the caller can include any separately reserved pages. -/
def canonicalSymbolicFloor (m : Memory ℚ) (L : Buffers) (n reservedEnd : ℕ) : ℕ :=
  max (max 128 reservedEnd) (max (m.index 67+n+1) (max (L.magBase+n)
    (max (L.gridBase+n) (max (L.flagBase+n) (L.scalePtr+1)))))

theorem canonicalSymbolicFloor_valid (m : Memory ℚ) (L : Buffers) (n reservedEnd : ℕ)
    (highRow : 128 ≤ m.index 67) : SymbolicWorkspaceFloor m L n (canonicalSymbolicFloor m L n reservedEnd) ∧
      reservedEnd ≤ canonicalSymbolicFloor m L n reservedEnd := by
  unfold canonicalSymbolicFloor
  constructor
  · exact ⟨by omega,highRow,by omega,by omega,by omega,by omega,by omega⟩
  · omega

theorem SymbolicWorkspaceAt.stableCache {m t : Memory ℚ} {L : Buffers} {n fuel prec floor : ℕ}
    {mag : ℕ → ℚ} (run : SymbolicWorkspaceAt m t n fuel floor) (cache : StableCache m L n fuel prec mag) :
    StableCache t L n fuel prec mag := by
  have high := cache.separated.flagHigh
  refine ⟨cache.header.transfer (fun i a b => run.kept i (by omega) (by omega)),
    cache.separated,?_,cache.positive,?_,?_,(run.kept 61 (by decide) (by decide)).trans cache.any,
    (run.kept 62 (by decide) (by decide)).trans cache.zero,by rw [run.data]; exact cache.scale⟩
  · intro j hj
    rw [run.data]
    exact cache.magnitude j hj
  · intro j hj
    rw [run.data]
    exact cache.numerator j hj
  · intro j hj
    exact (run.kept _ (by omega) (by omega)).trans (cache.symbolic j hj)

theorem SymbolicWorkspaceAt.protectData {m t : Memory ℚ} {n fuel floor : ℕ}
    (r : SymbolicWorkspaceAt m t n fuel floor) {i : ℕ} (hi : i < floor) : outsideSymbolicData t n fuel i := by
  unfold outsideSymbolicData
  rw [r.scalarTape,r.bases,r.exponents,r.digits]
  exact ⟨Or.inl (by omega),Or.inl hi,Or.inl (by omega),Or.inl (by omega)⟩

theorem SymbolicWorkspaceAt.protectTokens {m t : Memory ℚ} {n fuel floor : ℕ}
    (r : SymbolicWorkspaceAt m t n fuel floor) {i : ℕ} (hi : i < floor) : outsideSymbolicTokens t n fuel i := by
  apply Or.inl
  change i < t.index 90-(2*symbolicTokenBudget (n+1) (2*fuel+3)+8)
  rw [r.tokens]
  omega

theorem SymbolicWorkspaceAt.workspace {m t : Memory ℚ} {L : Buffers} {n fuel prec floor : ℕ} {mag : ℕ → ℚ}
    (r : SymbolicWorkspaceAt m t n fuel floor) (cache : StableCache m L n fuel prec mag)
    (f : SymbolicWorkspaceFloor m L n floor) : SymbolicQueryLayout t n fuel := by
  have stay := r.stableCache cache
  have q67 := r.kept 67 (by decide) (by decide)
  have high := f.high
  have rowEnd := f.rowEnd
  have magEnd := f.magEnd
  have gridEnd := f.gridEnd
  have flagEnd := f.flagEnd
  have scaleEnd := f.scaleEnd
  have layout : symbolicScanLayout t n =
      ⟨n,L.magBase,L.flagBase,m.index 67,floor,floor+(n+1)⟩ := by
    simp only [symbolicScanLayout,stay.header.magnitudes,stay.header.flags,q67,r.bases,r.exponents]
  have scan : (symbolicScanLayout t n).Valid := by
    rw [layout]
    refine ⟨(le_max_left ..).trans cache.separated.magHigh,cache.separated.flagHigh,f.rowHigh,
      high,?_,Or.inl ?_,Or.inl ?_,Or.inl ?_,Or.inl ?_,Or.inl ?_⟩ <;> dsimp <;> omega
  have areas : symbolicPairAreas t =
      ⟨floor,floor+(n+1),floor+2*(n+1),floor+2*(n+1)+2*n+5,
      floor+9+2*symbolicTokenBudget (n+1) (2*fuel+3)⟩ := by
    simp only [symbolicPairAreas,r.bases,r.exponents,r.scalarTape,r.digits,r.tokens]
  have enc : (symbolicPairAreas t).Valid (n+1) (symbolicDigitWidth fuel) := by
    rw [areas]
    refine ⟨high,?_,?_,?_,?_,Or.inl ?_,Or.inl ?_,Or.inl ?_⟩ <;> dsimp [symbolicDigitWidth] <;> omega
  refine ⟨scan,enc,by rw [r.dimSlot];exact high,Or.inl ?_,Or.inl ?_,Or.inl ?_,Or.inl ?_,Or.inl ?_⟩
  · rw [q67,r.scalarTape]; omega
  · rw [stay.header.numerators,r.scalarTape]; omega
  · rw [stay.header.magnitudes,r.scalarTape]; omega
  · rw [stay.header.scalePtr,r.scalarTape]; omega
  · rw [stay.header.flags,r.dimSlot]; exact flagEnd

theorem SymbolicWorkspaceAt.reservation {m t : Memory ℚ} {L : Buffers} {n fuel floor : ℕ}
    (r : SymbolicWorkspaceAt m t n fuel floor) (f : SymbolicWorkspaceFloor m L n floor) :
    SymbolicCacheReservation t L n fuel := by
  have q67 := r.kept 67 (by decide) (by decide)
  refine ⟨fun j hj => r.protectData (by have := f.magEnd;omega),
    fun j hj => r.protectData (by have := f.gridEnd;omega),r.protectData f.scaleEnd,
    fun j hj => r.protectData (by rw [q67];have := f.rowEnd;omega),
    fun j hj => r.protectTokens (by have := f.flagEnd;omega)⟩

/-- Entry register 97 holds the floor. Only the fixed header registers are
updated by the allocator. The six pointers are computed from the live length
and fuel rather than supplied as additional advice. -/
theorem initializeSymbolicWorkspace {m : Memory ℚ} {L : Buffers} {n fuel prec floor : ℕ}
    {mag : ℕ → ℚ} {P : ℚ → Prop} (cache : StableCache m L n fuel prec mag)
    (f : SymbolicWorkspaceFloor m L n floor) (hm : m.AllData P) (hfloor : m.index 97=floor) :
    ∃ t, Block.Eval (Memory.AllData P) symbolicWorkspaceBlock m (symbolicWorkspaceSteps n fuel) t ∧
      SymbolicWorkspaceAt m t n fuel floor ∧ StableCache t L n fuel prec mag ∧
      SymbolicQueryLayout t n fuel ∧ SymbolicCacheReservation t L n fuel := by
  obtain ⟨t,ev,out⟩ := symbolicWorkspaceBlock_eval m n fuel floor hm cache.header.size cache.header.fuelReg hfloor
  exact ⟨t,ev,out,out.stableCache cache,out.workspace cache f,out.reservation f⟩

/-- All earlier data and address pages survive the call. Fixed controller
registers below 128 have their more precise frame in `SymbolicQueryFrame`. -/
theorem SymbolicQueryFrame.older {m s u : Memory ℚ} {n fuel floor : ℕ}
    (fr : SymbolicQueryFrame n fuel s u) (r : SymbolicWorkspaceAt m s n fuel floor)
    (i : ℕ) (high : 128 ≤ i) (before : i < floor) :
    u.data i=m.data i ∧ u.index i=m.index i := by
  refine ⟨(fr.high_data i high (r.protectData before)).trans (congrFun r.data i),?_⟩
  have dim := r.dimSlot
  exact (fr.index i (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (r.protectTokens before)).trans
    (r.kept i (by omega) (by omega))

end Compression
end LinearProgramming
end Optimization
end OAI
