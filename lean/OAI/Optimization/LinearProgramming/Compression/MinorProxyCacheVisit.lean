import OAI.Optimization.LinearProgramming.Compression.MinorProxyCacheCall
import OAI.Optimization.LinearProgramming.Compression.MinorProxyCachePrepare
import OAI.Optimization.LinearProgramming.Compression.MinorProxyCacheStore
import OAI.Optimization.LinearProgramming.Compression.MinorProxyCacheLayout
import OAI.Optimization.LinearProgramming.Compression.ProxySpliceFrame

/-! One native logarithm call, with its real input load, return tag, scaled integer,
preserved high buffers and counted scalar/flag stores. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace MinorProxyCache
open RAM RAM.Callable FieldTransfer

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def visit : Fragment := Fragment.seq (.ofBlock prepare)
  (Fragment.seq (directCall logProxyProgram 2 (.index 63)) (.ofBlock finish))

def visitCost (fuel prec : ℕ) := 4*cap fuel prec+16*fuel+27*prec+228

/-- The bit analysis of the native logarithm can use the freshly zeroed low bank.
The count, output and native high frame are proved independently of this predicate. -/
def NativeSafe (P allowed : K → Prop) (fuel prec : ℕ) : Prop :=
  ∀ (s : Memory K), s.AllData P → allowed (s.data 0) → 0<s.data 0 →
    s.index 0=fuel → s.index 1=prec → (∀ j, 0<j → j<cap fuel prec → s.data j=0) →
    ∀ l v, runExactly logProxyProgram (s.atPC 0) l=some v → ∀ j,P (v.data j)

structure VisitResult (s t : Memory K) (bound : ℕ) (candidate : Option ℤ) : Prop where
  grid : t.data (s.index 58)=numeratorWord candidate
  flag : t.index (s.index 59)=MinorProxyCache.flag candidate
  any : t.index 61=if MinorProxyCache.flag candidate=0 then s.index 61 else 1
  zero : t.index 62=s.index 62
  readPtr : t.index 57=s.index 57+1
  gridPtr : t.index 58=s.index 58+1
  flagPtr : t.index 59=s.index 59+1
  counter : t.index 60=s.index 60+1
  scalarFrame : ∀ j, bound≤j → j≠s.index 58 → t.data j=s.data j
  indexFrame : ∀ j, 11≤j → (j<57 ∨ 64≤j) → j≠s.index 59 → t.index j=s.index j

theorem visit_run {fuel prec : ℕ} (P allowed : K → Prop) (native : NativeSafe P allowed fuel prec)
    (s : Memory K) (safe : s.AllData P) (hz : P 0) (hmag : 0<s.data (s.index 57))
    (hallowed : allowed (s.data (s.index 57))) (hf : s.index 84=fuel) (hk : s.index 85=prec)
    (hc : s.index 79=cap fuel prec) (guardMag : cap fuel prec≤s.index 57)
    (guardScale : cap fuel prec≤s.index 86) (hflags : 128≤s.index 59) (zero : s.index 62=0)
    (scale : s.data (s.index 86)=(2:K)^(prec+2))
    (hword : P (numeratorWord (fieldProxyNumerator fuel prec (s.data (s.index 57))))) :
    ∃ t, visit.Run P s (visitCost fuel prec) t ∧
      VisitResult s t (cap fuel prec) (fieldProxyNumerator fuel prec (s.data (s.index 57))) := by
  let mag := s.data (s.index 57)
  let ans := fieldProxyNumerator fuel prec mag
  let tag := flag ans
  have capBound : 2≤cap fuel prec := by dsimp [cap]; omega
  obtain ⟨a,init,a0,af,ak,alo,ahi,ai⟩ := prepare_eval P s safe hz (by omega) (by omega)
  have f := af.trans hf
  have k := ak.trans hk
  obtain ⟨n,hn,tr,run,result⟩ := logProxyProgram_field_exec_from fuel prec hmag (a.atPC 0) rfl rfl a0 f k
  let last := tr (Fin.last n)
  change (match ans with | none => last.output=some 1 | some u => last.output=some 0 ∧ last.data 0=(u:K)/2^(prec+2)) at result
  have output : last.output=some tag := by
    cases eq : ans with
    | none => rw [eq] at result; simpa only [tag,eq,flag] using result
    | some u => rw [eq] at result; simpa only [tag,eq,flag] using result.1
  have good (i : Fin (n+1)) : ∀ j,P ((tr i).data j) :=
    native a init.safe_end (a0 ▸ hallowed) (a0 ▸ hmag) f k
      (fun j hj hb => alo j hj (hc ▸ hb)) i.val (tr i) (runExactly_of_trace run i)
  have frame := logProxyProgram_frame_halted fuel prec hmag (a.atPC 0) rfl rfl a0 f k
    (runExactly_of_trace run (Fin.last n)) (by change last.output≠none; rw [output]; simp)
  let v := last.memory.putIndex 63 tag
  have short : tag<2 := by cases e : ans <;> simp [tag,e,flag]
  have invoke : (directCall logProxyProgram 2 (.index 63)).Run P a (n+2) v :=
    directCall_run _ _ _ P a short run good output (good _)
  have keepI (j : ℕ) (h : 11≤j) (ne : j≠63) : v.index j=s.index j := by
    change (last.memory.putIndex 63 tag).index j=s.index j
    rw [Memory.putIndex_ne _ ne]
    exact (frame.2 j (by omega)).trans (ai j h ne)
  have keepD (j : ℕ) (h : cap fuel prec≤j) : v.data j=s.data j := by
    have hscope : max (8+fuel) (prec+14)≤j := by dsimp [cap] at h; omega
    exact (frame.1 j hscope).trans (ahi j (hc ▸ h))
  have scale' : v.data (v.index 86)=(2:K)^(prec+2) := by
    rw [keepI 86 (by decide) (by decide),keepD _ guardScale,scale]
  have nword : (if tag=0 then v.data 0*v.data (v.index 86) else 0)=numeratorWord ans := by
    rw [scale']
    cases eq : ans with
    | none => simp [tag,eq,flag,numeratorWord]
    | some u =>
      rw [eq] at result
      change (if tag=0 then last.data 0*2^(prec+2) else 0)=_
      simp only [tag,eq,flag,ite_true,result.2,numeratorWord,Option.getD_some]
      exact div_mul_cancel₀ _ (pow_ne_zero _ (by norm_num))
  have v63 : v.index 63=tag := by simp [v]
  have v59 := keepI 59 (by decide) (by decide)
  have v62 := keepI 62 (by decide) (by decide)
  obtain ⟨t,j,hj,post,fields⟩ := finish_eval P v invoke.safe_end tag v63 (v62.trans zero)
    (by omega) (nword ▸ hword)
  refine ⟨t,((Fragment.Run.ofBlock init).seq (invoke.seq (Fragment.Run.ofBlock post))).mono ?_,?_⟩
  · unfold visitCost; rw [hc]; omega
  have v57 := keepI 57 (by decide) (by decide)
  have v58 := keepI 58 (by decide) (by decide)
  have v60 := keepI 60 (by decide) (by decide)
  have v61 := keepI 61 (by decide) (by decide)
  refine ⟨by simpa only [v58,nword] using fields.grid,by simpa only [v59] using fields.flag,
    by simpa only [v61] using fields.any,?_,by simpa only [v57] using fields.readPtr,
    by simpa only [v58] using fields.gridPtr,by simpa only [v59] using fields.flagPtr,
    by simpa only [v60] using fields.counter,?_,?_⟩
  · exact (fields.indexFrame 62 (by omega) (by omega)).trans v62
  · intro p hp he
    exact (fields.scalarFrame p (by omega) (v58 ▸ he)).trans (keepD p hp)
  · intro p hp he ne
    exact (fields.indexFrame p (by omega) (v59 ▸ ne)).trans (keepI p hp (by omega))

end MinorProxyCache
end Compression
end LinearProgramming
end Optimization
end OAI
