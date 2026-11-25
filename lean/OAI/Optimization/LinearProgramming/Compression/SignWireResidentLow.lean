import OAI.Optimization.LinearProgramming.Compression.SignWireOuterJob
import OAI.Optimization.LinearProgramming.Compression.SignWireResidentHigh

/-! Re-enter the nested numeric comparison after arbitrary changes to the low
registers of the outer bit controller. Only the high physical even bank is
part of the persistent numeric representation. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace SignWire

open RAM RAM.Callable MinorProxyCache

/-- An initialized nested window supplies the persistent part of its layout
before the outer controller uses any low register. -/
theorem HighShell.ofWindow {K : Type*} {raw old caller : Memory K} {cap base p : ℕ}
    (w : WindowImage raw cap (Odd.memory old caller)) (parity : EvenParity raw) :
    HighShell raw old caller cap base p :=
  ⟨fun i _ hi _ => (w i hi).1,fun i _ hi => (w i hi).2,fun i _ => parity i⟩

theorem ResidentHigh.ofWindow {n fuel prec C R cap base : ℕ} {mag : ℕ → ℚ} {L : Buffers}
    {P : ℚ → Prop} {raw old caller : Memory ℚ}
    (seed : ResidentNumeric (n:=n) mag L fuel prec C R base P old caller)
    (w : WindowImage raw cap (Odd.memory old caller)) (parity : EvenParity raw) :
    ResidentHigh (n:=n) mag L fuel prec C R cap base P raw :=
  ⟨old,caller,seed,HighShell.ofWindow w parity⟩

theorem ResidentHigh.ofPacked {n fuel prec C R cap base : ℕ} {mag : ℕ → ℚ} {L : Buffers}
    {P : ℚ → Prop} {old caller : Memory ℚ}
    (seed : ResidentNumeric (n:=n) mag L fuel prec C R base P old caller) (frame : Memory ℚ) :
    ResidentHigh (n:=n) mag L fuel prec C R cap base P (Call.pack (Odd.memory old caller) frame) := by
  apply ResidentHigh.ofWindow seed
  · intro i _
    exact ⟨Call.data_even ..,Call.index_even ..⟩
  · intro i; rw [Call.index_even]; omega

theorem ResidentHigh.ofPackedWindow {n fuel prec C R cap base : ℕ} {mag : ℕ → ℚ} {L : Buffers}
    {P : ℚ → Prop} {old caller : Memory ℚ}
    (seed : ResidentNumeric (n:=n) mag L fuel prec C R base P old caller) (tail frame : Memory ℚ) :
    ResidentHigh (n:=n) mag L fuel prec C R cap base P
      (Call.pack (windowMemory cap tail (Odd.memory old caller)) frame) := by
  apply ResidentHigh.ofWindow seed
  · intro i hi
    simp [windowMemory,hi]
  · intro i; rw [Call.index_even]; omega

/-- View the current field scalars as the low sixteen words of either logical
register bank. The nested caller uses physical offset two and the native bank
uses offset zero. Each address cell in that low prefix represents a logical zero. -/
def refreshLow {K : Type*} (raw old : Memory K) (offset : ℕ) : Memory K where
  data i := if i<16 then raw.data (4*i+offset) else old.data i
  index i := if i<16 then 0 else old.index i

theorem refreshLow_data_lo {K : Type*} (r m : Memory K) (o i : ℕ) (hi : i<16) :
    (refreshLow r m o).data i=r.data (4*i+o) := by simp [refreshLow,hi]
theorem refreshLow_index_lo {K : Type*} (r m : Memory K) (o i : ℕ) (hi : i<16) :
    (refreshLow r m o).index i=0 := by simp [refreshLow,hi]
theorem refreshLow_data_hi {K : Type*} (r m : Memory K) (o i : ℕ) (hi : 16≤ i) :
    (refreshLow r m o).data i=m.data i := by simp [refreshLow,Nat.not_lt.mpr hi]
theorem refreshLow_index_hi {K : Type*} (r m : Memory K) (o i : ℕ) (hi : 16≤ i) :
    (refreshLow r m o).index i=m.index i := by simp [refreshLow,Nat.not_lt.mpr hi]

theorem refreshLow_safe {K : Type*} {P : K → Prop} {raw m : Memory K} (o : ℕ)
    (hs : raw.AllData P) (hm : m.AllData P) : (refreshLow raw m o).AllData P := by
  intro i
  by_cases hi : i<16
  · rw [refreshLow_data_lo raw m o i hi]; exact hs _
  · rw [refreshLow_data_hi raw m o i (by omega)]; exact hm _

theorem refreshLow_footprint {K : Type*} [Zero K] {C : ℕ} (raw m : Memory K) (o : ℕ)
    (hC : 16≤C) (h : Footprint C (m.atPC 0)) : Footprint C ((refreshLow raw m o).atPC 0) := by
  refine ⟨?_,?_,?_⟩
  · intro i
    change (refreshLow raw m o).index i≤C
    by_cases hi : i<16
    · rw [refreshLow_index_lo _ _ _ _ hi]; omega
    · rw [refreshLow_index_hi _ _ _ _ (by omega)]; exact h.address i
  · intro i hi
    exact (refreshLow_data_hi raw m o i (by omega)).trans (h.data_zero i hi)
  · intro i hi
    exact (refreshLow_index_hi raw m o i (by omega)).trans (h.index_zero i hi)

theorem refreshLow_nested_data_hi {K : Type*} (raw old caller : Memory K) (i : ℕ) (hi : 32≤ i) :
    (Odd.memory (refreshLow raw old 0) (refreshLow raw caller 2)).data i =
      (Odd.memory old caller).data i := by
  obtain ⟨j,rfl|rfl⟩ : ∃ j, i=2*j ∨ i=Odd.slot j := Nat.even_or_odd' i
  · simpa only [Odd.data_even] using refreshLow_data_hi raw old 0 j (by omega)
  · have h : 16≤j := by unfold Odd.slot at hi; omega
    simpa only [Odd.data_slot] using refreshLow_data_hi raw caller 2 j h

theorem refreshLow_nested_index_hi {K : Type*} (raw old caller : Memory K) (i : ℕ) (hi : 32≤ i) :
    (Odd.memory (refreshLow raw old 0) (refreshLow raw caller 2)).index i =
      (Odd.memory old caller).index i := by
  obtain ⟨j,rfl|rfl⟩ : ∃ j, i=2*j ∨ i=Odd.slot j := Nat.even_or_odd' i
  · rw [Odd.index_even,Odd.index_even,refreshLow_index_hi _ _ _ _ (by omega)]
  · have h : 16≤j := by unfold Odd.slot at hi; omega
    rw [Odd.index_slot,Odd.index_slot,refreshLow_index_hi _ _ _ _ h]

theorem refreshLow_nested_data_lo {K : Type*} (raw old caller : Memory K) (i : ℕ) (hi : i<32) :
    (Odd.memory (refreshLow raw old 0) (refreshLow raw caller 2)).data i=raw.data (2*i) := by
  obtain ⟨j,rfl|rfl⟩ : ∃ j, i=2*j ∨ i=Odd.slot j := Nat.even_or_odd' i
  · rw [Odd.data_even,refreshLow_data_lo _ _ _ _ (by omega)]
    congr 1; omega
  · have h : j<16 := by unfold Odd.slot at hi; omega
    rw [Odd.data_slot,refreshLow_data_lo _ _ _ _ h]
    congr 1; unfold Odd.slot; omega

theorem HighShell.window {K : Type*} {raw old caller : Memory K} {cap base p : ℕ}
    (h : HighShell raw old caller cap base p) :
    RowWindowSetup raw (refreshLow raw old 0) (refreshLow raw caller 2) cap base p := by
  refine ⟨?_,?_,fun j hj => refreshLow_index_lo raw old 0 j hj,
    fun j hj => refreshLow_index_lo raw caller 2 j hj,h.highParity⟩
  · intro i ic _ exc
    by_cases hi : 32≤ i
    · exact (h.data i hi ic exc).trans (refreshLow_nested_data_hi raw old caller i hi).symm
    · exact (refreshLow_nested_data_lo raw old caller i (by omega)).symm
  · intro i ic hi
    rw [refreshLow_nested_index_hi raw old caller i hi]
    exact h.index i hi ic

theorem stableCache_refreshLow {n fuel prec : ℕ} {mag : ℕ → ℚ} {L : Buffers} {old : Memory ℚ}
    (cache : StableCache old L n fuel prec mag) (raw : Memory ℚ) (o : ℕ) :
    StableCache (refreshLow raw old o) L n fuel prec mag := by
  have magBase : 128≤L.magBase := (le_max_left ..).trans cache.separated.magHigh
  have gridBase : 128≤L.gridBase := (le_max_left ..).trans cache.separated.gridHigh
  have scaleBase : 128≤L.scalePtr := (le_max_left ..).trans cache.separated.scaleHigh
  have flagBase := cache.separated.flagHigh
  refine ⟨cache.header.transfer (fun i hi _ => refreshLow_index_hi _ _ _ _ (by omega)),
    cache.separated,?_,cache.positive,?_,?_,?_,?_,?_⟩
  · intro j hj; exact (refreshLow_data_hi raw old o (L.magBase+j) (by omega)).trans (cache.magnitude j hj)
  · intro j hj; exact (refreshLow_data_hi raw old o (L.gridBase+j) (by omega)).trans (cache.numerator j hj)
  · intro j hj; exact (refreshLow_index_hi raw old o (L.flagBase+j) (by omega)).trans (cache.symbolic j hj)
  · exact (refreshLow_index_hi raw old o 61 (by decide)).trans cache.any
  · exact (refreshLow_index_hi raw old o 62 (by decide)).trans cache.zero
  · exact (refreshLow_data_hi raw old o L.scalePtr (by omega)).trans cache.scale

theorem ResidentNumeric.refresh {n fuel prec C R base : ℕ} {mag : ℕ → ℚ} {L : Buffers}
    {P : ℚ → Prop} {old caller : Memory ℚ} (seed : ResidentNumeric (n:=n) mag L fuel prec C R base P old caller)
    (raw : Memory ℚ) (rawSafe : raw.AllData P) (hC : 16≤C) :
    ResidentNumeric (n:=n) mag L fuel prec C R base P (refreshLow raw old 0) (refreshLow raw caller 2) := by
  have keep : ∀ i, 60≤ i → i<91 → (i<70 ∨ 75< i) →
      (refreshLow raw caller 2).index i=caller.index i :=
    fun i hi _ _ => refreshLow_index_hi _ _ _ _ (by omega)
  refine ⟨stableCache_refreshLow seed.cache raw 2,seed.workspace.transfer_headers keep,
    seed.reservation.transfer_headers keep,(refreshLow_index_hi _ _ _ 67 (by decide)).trans seed.rowPtr,
    seed.apart,refreshLow_safe 2 rawSafe seed.callerSafe,refreshLow_safe 0 rawSafe seed.nativeSafe,
    refreshLow_footprint raw old 0 hC seed.nativeBound,
    (refreshLow_index_hi _ _ _ 60 (by decide)).trans seed.capacity,?_⟩
  intro i
  by_cases hi : i<16
  · rw [refreshLow_index_lo _ _ _ _ hi]; omega
  · rw [refreshLow_index_hi _ _ _ _ (by omega)]; exact seed.callerBound i

/-- Each new row sees a physically accurate virtual input despite arbitrary
intervening use of the outer controller's low scalar and address cells. -/
theorem outerJobData_of_high_shell {n : ℕ} (mag : ℕ → ℚ) (L : Buffers) (fuel prec C R cap src base : ℕ)
    (P : ℚ → Prop) (raw : Memory ℚ) (env : ResidentHigh (n:=n) mag L fuel prec C R cap base P raw)
    (rawSafe : raw.AllData P) (hC : 16≤C)
    (dimension : raw.index 51=n+1) (destination : raw.index 55=4*base+2)
    (reply : 3≤raw.index 47) (positive : 0<src)
    (safeRead : ∀ i j, i<j → j<n+1 → 4*(base+i)+2≠src+j) :
    OuterJobData (n:=n) mag L fuel prec C R cap src base P raw := by
  obtain ⟨old,caller,seed,shell⟩ := env
  exact outerJobData_of_window mag L fuel prec C R cap src base P raw _ _
    (seed.refresh raw rawSafe hC) shell.window dimension destination reply positive safeRead

end SignWire
end Compression
end LinearProgramming
end Optimization
end OAI
