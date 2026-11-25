import OAI.Optimization.LinearProgramming.Compression.SignWireInitialResident
import OAI.Optimization.LinearProgramming.Compression.SignWireNumericFootprint
import OAI.Optimization.LinearProgramming.Compression.SignWireTagProgram
import OAI.Optimization.LinearProgramming.Compression.CachedSign

/-! Initialize the full resident numerical state from its ordinary request. All
scalar and address cells, including scratch left by the native log computation,
fit in a single dimension-only polynomial window before physical scattering. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace SignWire

open RAM RAM.Callable MinorProxyCache Polynomial

noncomputable def initialResidentClockPolynomial : Polynomial ℕ :=
  let d := (X+1)^6+1
  let f := manuscriptProxyFuelPolynomial
  initialResidentTermsCost.comp cacheSeedPolynomial + (16*d+34+(d+1)*(7*f+15))

noncomputable def firstResidentPolynomial : Polynomial ℕ :=
  cacheSeedPolynomial + C (addressBudget (initialResidentBlock.compile 0)) + initialResidentClockPolynomial +
    C (addressBudget (tagReturningProgram (cachedProxySignFragment (.index 14))))

noncomputable def firstR (N : ℕ) : ℕ := firstResidentPolynomial.eval N

noncomputable def normalResidentClockPolynomial : Polynomial ℕ :=
  numericCacheClockPolynomial+initialResidentClockPolynomial

def normalResidentPrefix : Fragment := .seq numericProxyCache (.ofBlock initialResidentBlock)

/-- The initialization clock depends on the problem dimension after bounding
the generator count by its admissible width. -/
theorem initialResidentClock_le_polynomial (N g : ℕ) (width : g≤paperWidth N) :
    initialResidentClock (cacheSeedPolynomial.eval N) (g+1) (manuscriptProxyFuel N) ≤
      initialResidentClockPolynomial.eval N := by
  let d := (N+1)^6+1
  let f := manuscriptProxyFuel N
  have hg : g+1≤d := Nat.add_le_add_right (show g≤(N+1)^6 from width) 1
  have evalClock : initialResidentClockPolynomial.eval N =
      initialResidentTermsCost.eval (cacheSeedPolynomial.eval N)+symbolicWorkspaceSteps d f := by
    simp [initialResidentClockPolynomial,symbolicWorkspaceSteps,d,f,manuscriptProxyFuelPolynomial_eval]
  rw [evalClock]
  apply Nat.add_le_add_left
  unfold symbolicWorkspaceSteps
  exact Nat.add_le_add (Nat.add_le_add_right (Nat.mul_le_mul_left 16 hg) 34)
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right hg 1))

private theorem firstR_value (N : ℕ) :
    firstR N = cacheSeedPolynomial.eval N + addressBudget (initialResidentBlock.compile 0) +
      initialResidentClockPolynomial.eval N + addressBudget (tagReturningProgram (cachedProxySignFragment (.index 14))) := by
  unfold firstR firstResidentPolynomial
  simp only [Polynomial.eval_add, Polynomial.eval_C]

theorem initialResidentBound_le_firstR (N g : ℕ) (width : g≤paperWidth N) :
    initialResidentBound (cacheSeedPolynomial.eval N) (g+1) (manuscriptProxyFuel N) ≤ firstR N := by
  rw [firstR_value]
  unfold initialResidentBound
  have h := initialResidentClock_le_polynomial N g width
  omega

theorem firstR_tagBudget (N : ℕ) :
    addressBudget (tagReturningProgram (cachedProxySignFragment (.index 14))) ≤ firstR N := by
  rw [firstR_value]
  omega

/-- The initial virtual native bank is empty. The actual ordinary RAM output
already holds the complete padded query workspace, cached magnitudes and
offset numerators, and immutable source metadata needed by the driver. -/
theorem normalInitialResident_run_window (N g rank B : ℕ) (member : Bool) (mag : Fin (g+1) → ℚ)
    (width : g≤paperWidth N) (rank_le : rank≤g) (positive : ∀ i, 0<mag i)
    (words : ∀ i, ratBits (mag i)≤B) :
    let d := g+1
    let f := manuscriptProxyFuel N
    let prec := numericCachePrecision N
    let L := numericProxyCacheBuffers N g
    let P := fun q => ratBits q≤numericProxyCacheBits N B
    ∃ t : Memory ℚ,
      normalResidentPrefix.Run P (start [N,g,member.toNat,rank] (List.ofFn mag)).memory
        (normalResidentClockPolynomial.eval N) t ∧
      ResidentNumeric (n:=d) (tapeMagnitude mag) L f prec (symbolicQueryCap d f) (firstR N)
        (initialResidentRow L d) P initialResidentZero t ∧
      Footprint (firstR N) (t.atPC 0) ∧
      ProxyDriverMetadata N g member.toNat rank t ∧
      symbolicQueryCap d f ≤ firstR N ∧
      addressBudget (tagReturningProgram (cachedProxySignFragment (.index 14))) ≤ firstR N ∧
      initialResidentRow L d+d ≤ firstR N := by
  let P (q : ℚ) := ratBits q≤numericProxyCacheBits N B
  obtain ⟨mid,cacheRun,cache,_,_,_,_,_,metadata⟩ :=
    numericProxyCache_framed N g rank B member mag positive words
  have initialFoot := numericCacheSeed_footprint N g rank member mag P width rank_le cacheRun
  obtain ⟨k,t,init,steps,seed,ft,headers,_,_,_,rowEnd⟩ :=
    initialResidentBlock_spec mid (P := P) cache metadata cacheRun.safe_end initialFoot
  have window := initialResidentBound_le_firstR N g width
  have wide := seed.mono_bound window
  have clock : numericProxyCacheSteps N g+k≤normalResidentClockPolynomial.eval N := by
    rw [normalResidentClockPolynomial,eval_add]
    exact Nat.add_le_add ((Nat.le_succ _).trans (numericProxyCacheSteps_le N g width))
      (steps.trans (initialResidentClock_le_polynomial N g width))
  have capbound := wide.callerBound 60
  rw [wide.capacity] at capbound
  exact ⟨t,(cacheRun.seq (Fragment.Run.ofBlock (P := P) init)).mono clock,wide,ft.mono window,headers,
    (Nat.le_succ _).trans capbound,firstR_tagBudget N,rowEnd.trans window⟩

/-- The ordinary allocator and cache run as one numerical prefix in every larger program. -/
theorem normalInitialResident_run (N g rank B : ℕ) (member : Bool) (mag : Fin (g+1) → ℚ)
    (width : g≤paperWidth N) (rank_le : rank≤g) (positive : ∀ i, 0<mag i)
    (words : ∀ i, ratBits (mag i)≤B) :
    let d := g+1
    let f := manuscriptProxyFuel N
    let prec := numericCachePrecision N
    let L := numericProxyCacheBuffers N g
    let P := fun q => ratBits q≤numericProxyCacheBits N B
    ∃ t : Memory ℚ,
      normalResidentPrefix.Run P (start [N,g,member.toNat,rank] (List.ofFn mag)).memory
        (normalResidentClockPolynomial.eval N) t ∧
      ResidentNumeric (n:=d) (tapeMagnitude mag) L f prec (symbolicQueryCap d f) (firstR N)
        (initialResidentRow L d) P initialResidentZero t ∧
      Footprint (firstR N) (t.atPC 0) ∧
      ProxyDriverMetadata N g member.toNat rank t ∧
      symbolicQueryCap d f ≤ firstR N ∧
      addressBudget (tagReturningProgram (cachedProxySignFragment (.index 14))) ≤ firstR N := by
  obtain ⟨t,run,seed,foot,metadata,capacity,budget,_⟩ :=
    normalInitialResident_run_window N g rank B member mag width rank_le positive words
  exact ⟨t,run,seed,foot,metadata,capacity,budget⟩

/-- The full virtual row lies inside the fixed polynomial window. Its layout depends
only on the dimension and the number of retained generators. -/
theorem firstR_row_end (N g : ℕ) (width : g≤paperWidth N) :
    initialResidentRow (numericProxyCacheBuffers N g) (g+1)+(g+1)≤firstR N := by
  obtain ⟨_,_,_,_,_,_,_,endRow⟩ :=
    normalInitialResident_run_window N g 0 (ratBits 1) false (fun _ => 1) width (Nat.zero_le _)
      (fun _ => by norm_num) (fun _ => le_rfl)
  exact endRow

end SignWire
end Compression
end LinearProgramming
end Optimization
end OAI
