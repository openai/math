import OAI.Optimization.LinearProgramming.Compression.SignWireResidentHigh

/-! Normalize unused caller address words, then recognize the physically scattered resident cache. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace SignWire

variable {K : Type*}

open RAM RAM.Callable MinorProxyCache

/-- The numerical cache only needs addresses from slot 60 upward. Its scalar
bank is kept in full for the subsequent reverse scatter. -/
def normalizeResidentCaller (caller : Memory K) : Memory K :=
  {caller with index := fun i => if i < 60 then 0 else caller.index i}

@[simp] theorem normalizeResidentCaller_data (m : Memory K) :
    (normalizeResidentCaller m).data = m.data := rfl

theorem normalizeResidentCaller_index_low (m : Memory K) (i : ℕ) (hi : i < 60) :
    (normalizeResidentCaller m).index i = 0 := by simp [normalizeResidentCaller,hi]

theorem normalizeResidentCaller_index_high (m : Memory K) (i : ℕ) (hi : 60 ≤ i) :
    (normalizeResidentCaller m).index i = m.index i := by
  simp [normalizeResidentCaller,Nat.not_lt.mpr hi]

theorem normalizeResidentCaller_index_le (m : Memory K) (i : ℕ) :
    (normalizeResidentCaller m).index i ≤ m.index i := by
  by_cases h : i < 60 <;> simp [normalizeResidentCaller,h]

theorem normalizeResidentCache {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {n fuel prec : ℕ} {L : Buffers} {m : Memory K} {mag : ℕ → K}
    (cache : StableCache m L n fuel prec mag) : StableCache (normalizeResidentCaller m) L n fuel prec mag := by
  refine ⟨cache.header.transfer (fun j hj _ => normalizeResidentCaller_index_high m j (by omega)),
    cache.separated, cache.magnitude, cache.positive, cache.numerator, ?_,
    (normalizeResidentCaller_index_high m 61 (by decide)).trans cache.any,
    (normalizeResidentCaller_index_high m 62 (by decide)).trans cache.zero, cache.scale⟩
  intro j hj
  have high := cache.separated.flagHigh
  exact (normalizeResidentCaller_index_high m (L.flagBase+j) (by omega)).trans (cache.symbolic j hj)

/-- Normalization keeps the same original caller bound, including for a fresh
resident prior to the first numerical comparison. -/
theorem ResidentNumeric.normalize {n fuel prec C R base : ℕ} {mag : ℕ → ℚ} {L : Buffers}
    {P : ℚ → Prop} {old caller : Memory ℚ} (seed : ResidentNumeric (n:=n) mag L fuel prec C R base P old caller) :
    ResidentNumeric (n:=n) mag L fuel prec C R base P old (normalizeResidentCaller caller) := by
  have keep : ∀ i, 60 ≤ i → i < 91 → (i < 70 ∨ 75 < i) →
      (normalizeResidentCaller caller).index i = caller.index i :=
    fun i hi _ _ => normalizeResidentCaller_index_high caller i hi
  exact ⟨normalizeResidentCache seed.cache, seed.workspace.transfer_headers keep,
    seed.reservation.transfer_headers keep,
    (normalizeResidentCaller_index_high caller 67 (by decide)).trans seed.rowPtr,
    seed.apart, seed.callerSafe, seed.nativeSafe, seed.nativeBound,
    (normalizeResidentCaller_index_high caller 60 (by decide)).trans seed.capacity,
    fun i => (normalizeResidentCaller_index_le caller i).trans (seed.callerBound i)⟩

def zeroResidentNative [Zero K] : Memory K := ⟨fun _ => 0, fun _ => 0⟩

/-- The four physical words at offsets 0 and 2 are exactly the two field and
two address words of the double embedding. Their integer coefficients include
both address-encoding factors. -/
theorem HighShell.of_scatteredWords {K : Type*} (raw old caller : Memory K) (cap base p : ℕ)
    (nativeData : ∀ j, 16 ≤ j → j ≤ cap → raw.data (4*j) = old.data j)
    (nativeIndex : ∀ j, 16 ≤ j → j ≤ cap → raw.index (4*j) = 4*old.index j)
    (callerData : ∀ j, 16 ≤ j → j ≤ cap → raw.data (4*j+2) = caller.data j)
    (callerIndex : ∀ j, 16 ≤ j → j ≤ cap →
      raw.index (4*j+2) = 4*(normalizeResidentCaller caller).index j+2)
    (exterior : ∀ i, 2*cap+1 < i → raw.index (2*i)%2 = 0) :
    HighShell raw old (normalizeResidentCaller caller) (2*cap+1) base p := by
  have words (i : ℕ) (hi : 32 ≤ i) (hc : i ≤ 2*cap+1) :
      raw.data (2*i) = (Odd.memory old (normalizeResidentCaller caller)).data i ∧
      raw.index (2*i) = 2*(Odd.memory old (normalizeResidentCaller caller)).index i := by
    obtain ⟨j,rfl|rfl⟩ : ∃ j, i=2*j ∨ i=Odd.slot j := Nat.even_or_odd' i
    · rw [Odd.data_even,Odd.index_even,show 2*(2*j)=4*j by omega]
      exact ⟨nativeData j (by omega) (by omega),
        (nativeIndex j (by omega) (by omega)).trans (by omega)⟩
    · have jlo : 16 ≤ j := by unfold Odd.slot at hi; omega
      have jhi : j ≤ cap := by unfold Odd.slot at hc; omega
      rw [Odd.data_slot,Odd.index_slot,show 2*Odd.slot j=4*j+2 by unfold Odd.slot; omega]
      exact ⟨callerData j jlo jhi, (callerIndex j jlo jhi).trans (by unfold Odd.slot; omega)⟩
  refine ⟨fun i hi hc _ => (words i hi hc).1, fun i hi hc => (words i hi hc).2, ?_⟩
  intro i hi
  by_cases hc : i ≤ 2*cap+1
  · rw [(words i hi hc).2]; omega
  · exact exterior i (by omega)

/-- The zero native bank and normalized numeric caller satisfy the full
resident interface once the physically scattered words have been checked. -/
theorem highShell_from_scatter {n fuel prec C R cap base : ℕ} {mag : ℕ → ℚ} {L : Buffers}
    {P : ℚ → Prop} {raw caller : Memory ℚ}
    (seed : ResidentNumeric (n:=n) mag L fuel prec C R base P zeroResidentNative caller)
    (nativeData : ∀ j, 16 ≤ j → j ≤ cap → raw.data (4*j) = 0)
    (nativeIndex : ∀ j, 16 ≤ j → j ≤ cap → raw.index (4*j) = 0)
    (callerData : ∀ j, 16 ≤ j → j ≤ cap → raw.data (4*j+2) = caller.data j)
    (callerIndex : ∀ j, 16 ≤ j → j ≤ cap →
      raw.index (4*j+2) = 4*(normalizeResidentCaller caller).index j+2)
    (exterior : ∀ i, 2*cap+1 < i → raw.index (2*i)%2 = 0) :
    ResidentHigh (n:=n) mag L fuel prec C R (2*cap+1) base P raw := by
  refine ⟨zeroResidentNative,normalizeResidentCaller caller,seed.normalize,?_⟩
  exact HighShell.of_scatteredWords raw zeroResidentNative caller cap base (n+1) nativeData
    (by simpa [zeroResidentNative] using nativeIndex) callerData callerIndex exterior

theorem HighShell.weakenCap {K : Type*} {raw old caller : Memory K} {small big base p : ℕ}
    (h : HighShell raw old caller big base p) (hcap : small ≤ big) : HighShell raw old caller small base p :=
  ⟨fun i hi hc except => h.data i hi (hc.trans hcap) except,
   fun i hi hc => h.index i hi (hc.trans hcap), h.highParity⟩

theorem ResidentHigh.restrict {n fuel prec C R small big base : ℕ} {mag : ℕ → ℚ} {L : Buffers}
    {P : ℚ → Prop} {raw : Memory ℚ}
    (resident : ResidentHigh (n:=n) mag L fuel prec C R big base P raw) (hcap : small ≤ big) :
    ResidentHigh (n:=n) mag L fuel prec C R small base P raw := by
  obtain ⟨old,caller,seed,shell⟩ := resident
  exact ⟨old,caller,seed,shell.weakenCap hcap⟩

end SignWire
end Compression
end LinearProgramming
end Optimization
end OAI
