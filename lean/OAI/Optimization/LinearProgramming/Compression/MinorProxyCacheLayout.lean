import OAI.Optimization.LinearProgramming.Compression.ProxyFieldNumerator
import OAI.Optimization.LinearProgramming.Compression.MinorProxyInputsStep

/-! Physical reading convention of the finite cache shared by all subsequent signed queries. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace MinorProxyCache
open RAM

def cap (fuel prec : ℕ) : ℕ := fuel+prec+20

def flag : Option ℤ → ℕ | none => 1 | some _ => 0

def numeratorWord {K : Type*} [Ring K] (x : Option ℤ) : K := ((x.getD 0 : ℤ) : K)

def anySymbolic (answer : ℕ → Option ℤ) : ℕ → ℕ
  | 0 => 0
  | k+1 => if flag (answer k)=0 then anySymbolic answer k else 1

theorem anySymbolic_zero_iff (answer : ℕ → Option ℤ) (n : ℕ) :
    anySymbolic answer n=0 ↔ ∀ i<n, (answer i).isSome=true := by
  induction n with
  | zero => simp [anySymbolic]
  | succ n ih =>
    constructor
    · intro h i hi
      cases e : answer n with
      | none => simp [anySymbolic,e,flag] at h
      | some x =>
        have prev : anySymbolic answer n=0 := by simpa [anySymbolic,e,flag] using h
        by_cases eq : i=n
        · simp [eq,e]
        · exact ih.mp prev i (by omega)
    · intro all
      have last := all n (by omega)
      cases e : answer n with
      | none => simp [e] at last
      | some x =>
        have prev := ih.mpr (fun i hi => all i (by omega))
        simp [anySymbolic,e,flag,prev]

structure Buffers where
  magBase : ℕ
  gridBase : ℕ
  flagBase : ℕ
  scalePtr : ℕ

/-- Logical 80 through 86 are readable after the cache initializer returns. -/
structure Header {K : Type*} (s : Memory K) (L : Buffers) (n fuel prec : ℕ) : Prop where
  magnitudes : s.index 80=L.magBase
  numerators : s.index 81=L.gridBase
  flags : s.index 82=L.flagBase
  size : s.index 83=n
  fuelReg : s.index 84=fuel
  precision : s.index 85=prec
  scalePtr : s.index 86=L.scalePtr

theorem Header.transfer {K : Type*} {a b : Memory K} {L : Buffers} {n f p : ℕ}
    (h : Header a L n f p) (keep : ∀ j,80≤j → j≤86 → b.index j=a.index j) : Header b L n f p :=
  ⟨(keep 80 (by decide) (by decide)).trans h.magnitudes,(keep 81 (by decide) (by decide)).trans h.numerators,
   (keep 82 (by decide) (by decide)).trans h.flags,(keep 83 (by decide) (by decide)).trans h.size,
   (keep 84 (by decide) (by decide)).trans h.fuelReg,(keep 85 (by decide) (by decide)).trans h.precision,
   (keep 86 (by decide) (by decide)).trans h.scalePtr⟩

/-- The output cells avoid live scalar inputs, all fixed headers, and the entire
native logarithm workspace. The flag tape belongs to the other RAM bank. -/
structure Separated (L : Buffers) (N limit : ℕ) : Prop where
  magHigh : max 128 limit≤L.magBase
  gridHigh : max 128 limit≤L.gridBase
  flagHigh : 128≤L.flagBase
  scaleHigh : max 128 limit≤L.scalePtr
  magGrid : L.magBase+N≤L.gridBase ∨ L.gridBase+N≤L.magBase
  scaleGrid : L.scalePtr<L.gridBase ∨ L.gridBase+N≤L.scalePtr

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- All constants supplied to the signed-query reader are actual contiguous RAM
cells. Their stable headers coexist with the native capacity register at address 60. -/
structure StableCache (s : Memory K) (L : Buffers) (n fuel prec : ℕ) (mag : ℕ → K) : Prop where
  header : Header s L n fuel prec
  separated : Separated L n (cap fuel prec)
  magnitude : ∀ i<n, s.data (L.magBase+i)=mag i
  positive : ∀ i<n, 0<mag i
  numerator : ∀ i<n, s.data (L.gridBase+i)=numeratorWord (fieldProxyNumerator fuel prec (mag i))
  symbolic : ∀ i<n, s.index (L.flagBase+i)=flag (fieldProxyNumerator fuel prec (mag i))
  any : s.index 61=anySymbolic (fun i => fieldProxyNumerator fuel prec (mag i)) n
  zero : s.index 62=0
  scale : s.data L.scalePtr=(2:K)^(prec+2)

theorem StableCache.allSmall_of_noSymbolic {s : Memory K} {L : Buffers} {n fuel prec : ℕ} {mag : ℕ → K}
    (h : StableCache s L n fuel prec mag) (no : s.index 61=0) :
    ∀ i<n, (fieldProxyNumerator fuel prec (mag i)).isSome=true :=
  (anySymbolic_zero_iff _ _).mp (h.any.symm.trans no)

end MinorProxyCache
end Compression
end LinearProgramming
end Optimization
end OAI
