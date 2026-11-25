import OAI.Optimization.LinearProgramming.Compression.NumericROMBounds
import OAI.Optimization.LinearProgramming.Compression.NumericROMPorts
import OAI.Optimization.LinearProgramming.Compression.SignWireInitialResidentBound
import OAI.Optimization.LinearProgramming.PrimalDual.InputSize
import OAI.Optimization.LinearProgramming.RAM.SafeRun

/-! Ordinary magnitude tape to the logical resident numerical cache and all five
external physical address ports. The register bound is independent of input heights. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace NumericROM

open RAM RAM.Callable MinorProxyCache SignWire OracleSpec Polynomial

noncomputable def physicalWindowPolynomial (schedule : Polynomial ℕ) : Polynomial ℕ := window firstResidentPolynomial schedule
noncomputable def capCoefficient (schedule : Polynomial ℕ) : ℕ := (physicalWindowPolynomial schedule).eval 1
noncomputable def capExponent (schedule : Polynomial ℕ) : ℕ := (physicalWindowPolynomial schedule).natDegree
noncomputable def physicalCap (schedule : Polynomial ℕ) (n : ℕ) : ℕ := polyBound (capCoefficient schedule) (capExponent schedule) n
noncomputable def physicalCapBound (schedule : Polynomial ℕ) : Polynomial ℕ := C (capCoefficient schedule)*(X+1)^(capExponent schedule)

@[simp] theorem physicalCapBound_eval (schedule : Polynomial ℕ) (n : ℕ) : (physicalCapBound schedule).eval n=physicalCap schedule n := by
  simp [physicalCapBound,physicalCap,polyBound]

def inputHeight {g : ℕ} (mag : Fin (g+1)→ℚ) : ℕ := totalBits (List.ofFn mag)

noncomputable def queryHeight (schedule : Polynomial ℕ) {g : ℕ} (n : ℕ) (mag : Fin (g+1)→ℚ) : ℕ :=
  effectiveB n (inputHeight mag) (schedule.eval n)

noncomputable def workingHeight (schedule : Polynomial ℕ) {g : ℕ} (n : ℕ) (mag : Fin (g+1)→ℚ) : ℕ :=
  wordComparatorBits (g+1) (manuscriptProxyFuel n) (numericCachePrecision n) (queryHeight schedule n mag)

noncomputable def budgetC (n g : ℕ) : ℕ := symbolicQueryCap (g+1) (manuscriptProxyFuel n)
noncomputable def rowBase (n g : ℕ) : ℕ := initialResidentRow (numericProxyCacheBuffers n g) (g+1)

noncomputable def residentAndPorts (schedule : Polynomial ℕ) : Fragment := .seq normalResidentPrefix (.ofBlock (numericPortBlock (capCoefficient schedule) (capExponent schedule)))
noncomputable def residentPortTime (schedule : Polynomial ℕ) : Polynomial ℕ := normalResidentClockPolynomial+
  numericPortPolynomial (capCoefficient schedule) (capExponent schedule) firstResidentPolynomial

theorem inputHeight_bound {g : ℕ} (mag : Fin (g+1)→ℚ) (i : Fin (g+1)) : ratBits (mag i) ≤ inputHeight mag :=
  PrimalDual.ratBits_le_totalBits_of_mem (List.mem_ofFn.mpr ⟨i,rfl⟩)

theorem queryHeight_bound (schedule : Polynomial ℕ) {g : ℕ} (n : ℕ) (mag : Fin (g+1)→ℚ) (i : Fin (g+1)) :
    ratBits (tapeMagnitude mag i)≤queryHeight schedule n mag := by
  rw [tapeMagnitude_fin]
  exact (inputHeight_bound mag i).trans (le_max_left ..)

/-- The single finite allocation covers the complete numerical oracle schedule, its
initial high register file, and the full numerical query row. -/
theorem physicalCap_room (schedule : Polynomial ℕ) {n g : ℕ} (hg : g≤paperWidth n) (base : ℕ) (hb : base≤firstR n) :
    2*(firstR n+(schedule.eval n+1)*(cachedProxySignSteps (g+1) (manuscriptProxyFuel n) (budgetC n g)+5))+135+2*(base+g+2)≤physicalCap schedule n :=
  (window_le firstResidentPolynomial schedule n g base hg hb).trans
    (polynomial_eval_le_polyBound (physicalWindowPolynomial schedule) n)

/-- The scalar, footprint and metadata frames required by the physical 4j+2 installer
hold simultaneously, on a single native execution of the whole prefix. -/
theorem residentAndPorts_run (schedule : Polynomial ℕ) {n g : ℕ} (rank : ℕ) (member : Bool) (mag : Fin (g+1)→ℚ)
    (width : g≤paperWidth n) (rank_le : rank≤g) (hp : ∀ i,0<mag i) :
    let d := g+1
    let f := manuscriptProxyFuel n
    let P := fun q => ratBits q≤workingHeight schedule n mag
    let ordinary := (start [n,g,member.toNat,rank] (List.ofFn mag)).memory
    ∃ logical raw : Memory ℚ, (residentAndPorts schedule).Run P ordinary ((residentPortTime schedule).eval n) raw ∧
      ResidentNumeric (n:=d) (tapeMagnitude mag) (numericProxyCacheBuffers n g) f (numericCachePrecision n)
        (budgetC n g) (firstR n) (rowBase n g) P initialResidentZero logical ∧
      Footprint (firstR n) (logical.atPC 0) ∧ ProxyDriverMetadata n g member.toNat rank logical ∧
      NormalPorts (physicalCap schedule n) d f (rowBase n g) raw ∧ raw.data=logical.data ∧
      (∀ i,60≤ i → raw.index i=logical.index i) ∧ budgetC n g≤firstR n ∧
      addressBudget (tagReturningProgram (cachedProxySignFragment (.index 14)))≤firstR n := by
  let B := inputHeight mag
  let P := fun q : ℚ => ratBits q≤workingHeight schedule n mag
  obtain ⟨mid,body,seed,foot,metadata,boundC,code⟩ := normalInitialResident_run n g rank B member mag width rank_le hp (inputHeight_bound mag)
  have hw : numericProxyCacheBits n B≤workingHeight schedule n mag := (height_dominates n B (schedule.eval n)
    (g+1) (manuscriptProxyFuel n) (numericCachePrecision n)).2.1
  have run := Fragment.Run.weakenData (P := fun q : ℚ => ratBits q ≤ numericProxyCacheBits n B)
    (Q := P) body (fun _ h => Nat.le_trans h hw)
  have seed' : ResidentNumeric (n:=g+1) (tapeMagnitude mag) (numericProxyCacheBuffers n g)
      (manuscriptProxyFuel n) (numericCachePrecision n) (budgetC n g) (firstR n) (rowBase n g) P initialResidentZero mid :=
    ⟨seed.cache,seed.workspace,seed.reservation,seed.rowPtr,seed.apart,fun j => (seed.callerSafe j).trans hw,
      fun j => (seed.nativeSafe j).trans hw,seed.nativeBound,seed.capacity,seed.callerBound⟩
  obtain ⟨raw,k,prep,clock,ports,ds,idx⟩ := numericPortBlock_correct (P := P) (capCoefficient schedule) (capExponent schedule)
    firstResidentPolynomial n (g+1) (manuscriptProxyFuel n) (rowBase n g) mid run.safe_end seed.callerBound
    metadata.dimension seed.cache.header.size seed.cache.header.fuelReg seed.rowPtr
  have both := (run.seq (Fragment.Run.ofBlock (P := P) prep)).mono (Nat.add_le_add_left clock _)
  refine ⟨mid,raw,?_,seed',foot,metadata,ports,ds,idx,boundC,code⟩
  simpa only [residentAndPorts, residentPortTime, eval_add, P] using both

end NumericROM
end Compression
end LinearProgramming
end Optimization
end OAI
