import OAI.Optimization.LinearProgramming.Compression.SymbolicAreas
import OAI.Optimization.LinearProgramming.Compression.MinorProxyCacheLayout
import OAI.Optimization.LinearProgramming.FieldTransfer.ProxyPackingLayout

/-! Static caller addresses, memory bounds and protected intervals of the
resident symbolic comparator. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM FieldTransfer MinorProxyCache

def symbolicPairAreas (m : Memory ℚ) : SymbolicPairAreas :=
  ⟨m.index 68,m.index 69,m.index 87,m.index 89,m.index 90⟩

def symbolicScanLayout (m : Memory ℚ) (n : ℕ) : ProxyPacking.Layout :=
  ⟨n,m.index 80,m.index 82,m.index 67,m.index 68,m.index 69⟩

def symbolicDigitWidth (fuel : ℕ) := 2*fuel+3

/-- The two staging phases may share the scalar-tape workspace. Read-only
cache cells and the singleton address slot are separated where their phases overlap. -/
structure SymbolicQueryLayout (m : Memory ℚ) (n fuel : ℕ) : Prop where
  scan : (symbolicScanLayout m n).Valid
  encode : (symbolicPairAreas m).Valid (n+1) (symbolicDigitWidth fuel)
  dimHigh : 128 ≤ m.index 88
  rowTape : m.index 67+n < m.index 87 ∨ m.index 87+2*n+5 ≤ m.index 67
  gridTape : m.index 81+n ≤ m.index 87 ∨ m.index 87+2*n+5 ≤ m.index 81
  magTape : m.index 80+n ≤ m.index 87 ∨ m.index 87+2*n+5 ≤ m.index 80
  scaleTape : m.index 86 < m.index 87 ∨ m.index 87+2*n+5 ≤ m.index 86
  flagDim : m.index 82+n ≤ m.index 88 ∨ m.index 88 < m.index 82

/-- External storage surviving both staging passes, the compactor and the power-tape
encoder. This relation describes the memory immediately before the return-tag write. -/
structure SymbolicQueryFrame (n fuel : ℕ) (m t : Memory ℚ) : Prop where
  data : ∀ i, 6 ≤ i → i ≠ 8 → (i < 20 ∨ 23 < i) → i ≠ 40 → i ≠ 41 → i ≠ 45 →
    (i < m.index 87 ∨ m.index 87+2*n+5 ≤ i) →
    (i < m.index 68 ∨ m.index 68+(n+1) ≤ i) →
    (i < m.index 69 ∨ m.index 69+(n+1) ≤ i) →
    (i < m.index 89 ∨ m.index 89+symbolicDigitWidth fuel ≤ i) → t.data i=m.data i
  index : ∀ i, 43 ≤ i → (i < 50 ∨ 52 < i) → i ≠ 54 → i ≠ 55 → i ≠ 56 → i ≠ 57 → i ≠ 58 → i ≠ 59 →
    (i < 70 ∨ 75 < i) → i ≠ m.index 88 →
    (i < m.index 90-(2*symbolicTokenBudget (n+1) (symbolicDigitWidth fuel)+8) ∨
      m.index 90+symbolicTokenBudget (n+1) (symbolicDigitWidth fuel) ≤ i) → t.index i=m.index i

theorem SymbolicQueryFrame.header {n fuel : ℕ} {m t : Memory ℚ} (h : SymbolicQueryFrame n fuel m t)
    (space : SymbolicQueryLayout m n fuel) (i : ℕ) (hi : 60 ≤ i) (hi' : i < 128)
    (hs : i < 70 ∨ 75 < i) : t.index i=m.index i := by
  have below := space.encode.tokenRoom
  change 128+2*symbolicTokenBudget (n+1) (symbolicDigitWidth fuel)+8 ≤ m.index 90 at below
  have dim := space.dimHigh
  exact h.index i (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) hs (by omega) (Or.inl (by omega))

/-- This includes the two scalar return-frame backup slots 100 and 101. -/
theorem SymbolicQueryFrame.localScalar {n fuel : ℕ} {m t : Memory ℚ}
    (h : SymbolicQueryFrame n fuel m t) (space : SymbolicQueryLayout m n fuel)
    (i : ℕ) (lo : 45 < i) (hi : i < 128) : t.data i=m.data i := by
  have bases : 128 ≤ m.index 68 := space.encode.basesHigh
  have exps : 128 ≤ m.index 69 := space.encode.exponentsHigh
  have tape : 128 ≤ m.index 87 := space.encode.scalarHigh
  have digits : 128 ≤ m.index 89 := space.encode.digitsHigh
  exact h.data i (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))

def outsideSymbolicData (m : Memory ℚ) (n fuel i : ℕ) : Prop :=
  (i < m.index 87 ∨ m.index 87+2*n+5 ≤ i) ∧ (i < m.index 68 ∨ m.index 68+(n+1) ≤ i) ∧
  (i < m.index 69 ∨ m.index 69+(n+1) ≤ i) ∧ (i < m.index 89 ∨ m.index 89+symbolicDigitWidth fuel ≤ i)

def outsideSymbolicTokens (m : Memory ℚ) (n fuel i : ℕ) : Prop :=
  i < m.index 90-(2*symbolicTokenBudget (n+1) (symbolicDigitWidth fuel)+8) ∨
    m.index 90+symbolicTokenBudget (n+1) (symbolicDigitWidth fuel) ≤ i

/-- These inequalities can be checked using the static buffer allocation before
the sign search starts. They cover the complete query row, including its constant. -/
structure SymbolicCacheReservation (m : Memory ℚ) (L : Buffers) (n fuel : ℕ) : Prop where
  magnitudes : ∀ j < n, outsideSymbolicData m n fuel (L.magBase+j)
  numerators : ∀ j < n, outsideSymbolicData m n fuel (L.gridBase+j)
  scale : outsideSymbolicData m n fuel L.scalePtr
  row : ∀ j ≤ n, outsideSymbolicData m n fuel (m.index 67+j)
  flags : ∀ j < n, outsideSymbolicTokens m n fuel (L.flagBase+j)

theorem SymbolicQueryFrame.high_data {m t : Memory ℚ} {n fuel : ℕ} (fr : SymbolicQueryFrame n fuel m t)
    (i : ℕ) (hi : 128 ≤ i) (avoid : outsideSymbolicData m n fuel i) : t.data i=m.data i :=
  fr.data i (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    avoid.1 avoid.2.1 avoid.2.2.1 avoid.2.2.2

theorem SymbolicQueryLayout.transfer_headers {m t : Memory ℚ} {n fuel : ℕ}
    (space : SymbolicQueryLayout m n fuel)
    (keep : ∀ i, 60 ≤ i → i < 91 → (i < 70 ∨ 75 < i) → t.index i=m.index i) :
    SymbolicQueryLayout t n fuel := by
  have hi (j) (hj : 80 ≤ j ∧ j ≤ 90) : t.index j=m.index j :=
    keep j (by omega) (by omega) (by omega)
  have h67 := keep 67 (by decide) (by decide) (by decide)
  have h68 := keep 68 (by decide) (by decide) (by decide)
  have h69 := keep 69 (by decide) (by decide) (by decide)
  have h80 := hi 80 (by decide)
  have h81 := hi 81 (by decide)
  have h82 := hi 82 (by decide)
  have h86 := hi 86 (by decide)
  have h87 := hi 87 (by decide)
  have h88 := hi 88 (by decide)
  have h89 := hi 89 (by decide)
  have h90 := hi 90 (by decide)
  have sl : symbolicScanLayout t n = symbolicScanLayout m n := by
    simp only [symbolicScanLayout,h67,h68,h69,h80,h82]
  have pa : symbolicPairAreas t = symbolicPairAreas m := by
    simp only [symbolicPairAreas,h68,h69,h87,h89,h90]
  exact ⟨by rw [sl]; exact space.scan,by rw [pa]; exact space.encode,by rw [h88]; exact space.dimHigh,
    by simpa only [h67,h87] using space.rowTape,
    by simpa only [h81,h87] using space.gridTape,by simpa only [h80,h87] using space.magTape,
    by simpa only [h86,h87] using space.scaleTape,by simpa only [h82,h88] using space.flagDim⟩

theorem SymbolicCacheReservation.transfer_headers {m t : Memory ℚ} {L : Buffers} {n fuel : ℕ}
    (res : SymbolicCacheReservation m L n fuel)
    (keep : ∀ i, 60 ≤ i → i < 91 → (i < 70 ∨ 75 < i) → t.index i=m.index i) :
    SymbolicCacheReservation t L n fuel := by
  have h67 := keep 67 (by decide) (by decide) (by decide)
  have h68 := keep 68 (by decide) (by decide) (by decide)
  have h69 := keep 69 (by decide) (by decide) (by decide)
  have h87 := keep 87 (by decide) (by decide) (by decide)
  have h89 := keep 89 (by decide) (by decide) (by decide)
  have h90 := keep 90 (by decide) (by decide) (by decide)
  have d (i) : outsideSymbolicData t n fuel i ↔ outsideSymbolicData m n fuel i := by
    simp only [outsideSymbolicData,h68,h69,h87,h89]
  have adr (i) : outsideSymbolicTokens t n fuel i ↔ outsideSymbolicTokens m n fuel i := by
    simp only [outsideSymbolicTokens,h90]
  exact ⟨fun j hj => (d _).mpr (res.magnitudes j hj),fun j hj => (d _).mpr (res.numerators j hj),
    (d _).mpr res.scale,fun j hj => by rw [h67]; exact (d _).mpr (res.row j hj),
    fun j hj => (adr _).mpr (res.flags j hj)⟩

end Compression
end LinearProgramming
end Optimization
end OAI
