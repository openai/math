import OAI.Optimization.LinearProgramming.Compression.MinorProxyCacheVisit
import OAI.Optimization.LinearProgramming.PrimalDual.OutputSetup

/-! Uniform batched logarithm calls on the retained positive minors, producing the
stable physical cache consumed by signed-form queries. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace MinorProxyCache
open RAM RAM.Callable PrimalDual

private def bindings : List CursorBind := [.reg 78 60,.reg 57 80,.reg 58 81,.reg 59 82,
  .literal 60 0,.literal 61 0,.literal 62 0]

def materialize : Fragment := Fragment.seq (.ofBlock (CursorBind.script bindings))
  (Fragment.seq (Fragment.loop (.addrLT 60 83) visit) (.ofBlock (.op (.addrCopy 60 78))))

def cacheCost (n fuel prec : ℕ) := n*(visitCost fuel prec+2)+9

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private structure Invariant (P : K→Prop) (m : Memory K) (L : Buffers) (n fuel prec : ℕ)
    (mag : ℕ → K) (k : ℕ) (s : Memory K) : Prop where
  safe : s.AllData P
  counter : s.index 60=k
  readPtr : s.index 57=L.magBase+k
  gridPtr : s.index 58=L.gridBase+k
  flagPtr : s.index 59=L.flagBase+k
  saved : s.index 78=m.index 60
  limit : s.index 79=cap fuel prec
  any : s.index 61=anySymbolic (fun i => fieldProxyNumerator fuel prec (mag i)) k
  zero : s.index 62=0
  stored : ∀ i<k, s.data (L.gridBase+i)=numeratorWord (fieldProxyNumerator fuel prec (mag i)) ∧
    s.index (L.flagBase+i)=flag (fieldProxyNumerator fuel prec (mag i))
  dataFrame : ∀ j, cap fuel prec≤j → (j<L.gridBase ∨ L.gridBase+n≤j) → s.data j=m.data j
  indexFrame : ∀ j, 80≤j → (j<L.flagBase ∨ L.flagBase+n≤j) → s.index j=m.index j

private theorem cursorHeader {P : K→Prop} {m s : Memory K} {L : Buffers} {n fuel prec k : ℕ}
    {mag : ℕ→K} (h : Invariant P m L n fuel prec mag k s) (hh : Header m L n fuel prec)
    (bound : 128≤L.flagBase) : Header s L n fuel prec :=
  hh.transfer fun j lo hi => h.indexFrame j lo (.inl (by omega))

private theorem cursorMagnitude {P : K→Prop} {m s : Memory K} {L : Buffers} {n fuel prec k : ℕ}
    {mag : ℕ→K} (h : Invariant P m L n fuel prec mag k s) (sep : Separated L n (cap fuel prec))
    (input : ∀ i<n, m.data (L.magBase+i)=mag i) (i : ℕ) (hi : i<n) : s.data (L.magBase+i)=mag i := by
  have high := (le_max_right 128 (cap fuel prec)).trans sep.magHigh
  rw [h.dataFrame _ (by omega) (by rcases sep.magGrid with hl|hr; exact .inl (by omega); exact .inr (by omega))]
  exact input i hi

private theorem cursorScale {P : K→Prop} {m s : Memory K} {L : Buffers} {n fuel prec k : ℕ} {mag : ℕ→K}
    (h : Invariant P m L n fuel prec mag k s) (sep : Separated L n (cap fuel prec))
    (scale : m.data L.scalePtr=(2:K)^(prec+2)) : s.data L.scalePtr=(2:K)^(prec+2) :=
  (h.dataFrame _ ((le_max_right 128 _).trans sep.scaleHigh) sep.scaleGrid).trans scale

private theorem advance {P : K→Prop} {m s t : Memory K} {L : Buffers} {n fuel prec k : ℕ} {mag : ℕ→K}
    (hk : k<n) (sep : Separated L n (cap fuel prec)) (h : Invariant P m L n fuel prec mag k s)
    (safe : t.AllData P) (one : VisitResult s t (cap fuel prec) (fieldProxyNumerator fuel prec (mag k))) :
    Invariant P m L n fuel prec mag (k+1) t := by
  have flagHigh := sep.flagHigh
  have gridHigh := (le_max_right 128 _).trans sep.gridHigh
  have high (j : ℕ) (lo : 64≤j) (less : j<128) : t.index j=s.index j :=
    one.indexFrame _ (by omega) (.inr lo) (by rw [h.flagPtr]; omega)
  refine ⟨safe,by simpa only [h.counter] using one.counter,by simpa only [h.readPtr,Nat.add_assoc] using one.readPtr,
    by simpa only [h.gridPtr,Nat.add_assoc] using one.gridPtr,by simpa only [h.flagPtr,Nat.add_assoc] using one.flagPtr,
    (high 78 (by decide) (by decide)).trans h.saved,(high 79 (by decide) (by decide)).trans h.limit,
    by simpa only [anySymbolic,h.any] using one.any,one.zero.trans h.zero,?_,?_,?_⟩
  · intro i hi
    by_cases endp : i=k
    · subst i; exact ⟨h.gridPtr ▸ one.grid,h.flagPtr ▸ one.flag⟩
    · have old := h.stored i (by omega)
      have d := one.scalarFrame (L.gridBase+i) (by omega) (by rw [h.gridPtr]; omega)
      have a := one.indexFrame (L.flagBase+i) (by omega) (.inr (by omega)) (by rw [h.flagPtr]; omega)
      exact ⟨d.trans old.1,a.trans old.2⟩
  · intro j hj outside
    exact (one.scalarFrame j hj (by rw [h.gridPtr]; omega)).trans (h.dataFrame j hj outside)
  · intro j hj outside
    exact (one.indexFrame j (by omega) (.inr (by omega)) (by rw [h.flagPtr]; omega)).trans
      (h.indexFrame j hj outside)

/-- The actual fixed caller loops over a runtime length, embeds the full logarithm
program for every positive magnitude, and restores the consumer's native capacity.
The scalar policy only specifies the bound checked along that already fixed code. -/
theorem materialize_framed (P allowed : K→Prop) (fuel prec n : ℕ) (L : Buffers) (mag : ℕ→K)
    (m : Memory K) (hs : m.AllData P) (hz : P 0) (head : Header m L n fuel prec)
    (sep : Separated L n (cap fuel prec)) (limit : m.index 79=cap fuel prec)
    (scale : m.data L.scalePtr=(2:K)^(prec+2)) (input : ∀i<n,m.data (L.magBase+i)=mag i)
    (positive : ∀i<n,0<mag i) (eligible : ∀i<n,allowed (mag i)) (native : NativeSafe P allowed fuel prec)
    (codes : ∀i<n,P (numeratorWord (fieldProxyNumerator fuel prec (mag i)))) :
    ∃ t, materialize.Run P m (cacheCost n fuel prec) t ∧ StableCache t L n fuel prec mag ∧
      t.index 60=m.index 60 ∧
      (∀ j, 80≤j → (j<L.flagBase ∨ L.flagBase+n≤j) → t.index j=m.index j) ∧
      (∀ j, cap fuel prec≤j → (j<L.gridBase ∨ L.gridBase+n≤j) → t.data j=m.data j) := by
  let u := CursorBind.install bindings m
  have pre : Block.Eval (Memory.AllData P) (CursorBind.script bindings) m 7 u := CursorBind.run bindings m hs
  let I := Invariant P m L n fuel prec mag
  have init : I 0 u := by
    refine ⟨pre.safe_end,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simp [u,bindings,CursorBind.install,CursorBind.apply]
    · simp [u,bindings,CursorBind.install,CursorBind.apply,head.magnitudes]
    · simp [u,bindings,CursorBind.install,CursorBind.apply,head.numerators]
    · simp [u,bindings,CursorBind.install,CursorBind.apply,head.flags]
    · simp [u,bindings,CursorBind.install,CursorBind.apply]
    · simp [u,bindings,CursorBind.install,CursorBind.apply,limit]
    · simp [u,bindings,CursorBind.install,CursorBind.apply,anySymbolic]
    · simp [u,bindings,CursorBind.install,CursorBind.apply]
    · intro i hi; omega
    · intro j _ _; rfl
    · intro j hj _
      simp [u,bindings,CursorBind.install,CursorBind.apply,show j≠78 by omega,show j≠57 by omega,
        show j≠58 by omega,show j≠59 by omega,show j≠60 by omega,show j≠61 by omega,show j≠62 by omega]
  obtain ⟨v,run,fin⟩ := Fragment.Run.loop_invariant (P := P) (.addrLT 60 83) visit I n
    (visitCost fuel prec) u init (by
      intro k hk s h
      have header := cursorHeader h head sep.flagHigh
      have magWord : s.data (s.index 57)=mag k := h.readPtr ▸ cursorMagnitude h sep input k hk
      have d : s.data (s.index 86)=(2:K)^(prec+2) := header.scalePtr ▸ cursorScale h sep scale
      have high := (le_max_right 128 _).trans sep.magHigh
      have flagsH := sep.flagHigh
      obtain ⟨t,ev,hit⟩ := visit_run P allowed native s h.safe hz (magWord ▸ positive k hk)
        (magWord ▸ eligible k hk) header.fuelReg header.precision h.limit (by rw [h.readPtr]; omega)
        (header.scalePtr ▸ (le_max_right 128 _).trans sep.scaleHigh) (by rw [h.flagPtr]; omega) h.zero d
        (magWord ▸ codes k hk)
      rw [magWord] at hit
      exact ⟨by simp [Cond.test,h.counter,header.size,hk],t,ev,advance hk sep h ev.safe_end hit⟩) (by
      intro s h
      exact ⟨by simp [Cond.test,h.counter,(cursorHeader h head sep.flagHigh).size],h.safe⟩)
  let t := v.putIndex 60 (m.index 60)
  have restore : Block.Eval (Memory.AllData P) (.op (.addrCopy 60 78)) v 1 t := by
    simpa only [fin.saved] using Block.Eval.op_addrCopy (safe := Memory.AllData P) v 60 78 fin.safe fin.safe
  have tail (j : ℕ) (hj : 80≤j) (out : j<L.flagBase ∨ L.flagBase+n≤j) : t.index j=m.index j := by
    simpa [t,show j≠60 by omega] using fin.indexFrame j hj out
  refine ⟨t,((Fragment.Run.ofBlock pre).seq (run.seq (Fragment.Run.ofBlock restore))).mono ?_,?_,by simp [t],tail,fin.dataFrame⟩
  · unfold cacheCost; omega
  have fHigh := sep.flagHigh
  have finalScale := cursorScale fin sep scale
  have finalMag := cursorMagnitude fin sep input
  refine ⟨head.transfer (fun j hj hb => tail j hj (.inl (by omega))),sep,finalMag,
    positive,fun i hi => (fin.stored i hi).1,?_,?_,?_,finalScale⟩
  · intro i hi; simpa [t,show L.flagBase+i≠60 by omega] using (fin.stored i hi).2
  · simpa [t] using fin.any
  · simpa [t] using fin.zero

theorem materialize_run (P allowed : K→Prop) (fuel prec n : ℕ) (L : Buffers) (mag : ℕ→K)
    (m : Memory K) (hs : m.AllData P) (hz : P 0) (head : Header m L n fuel prec)
    (sep : Separated L n (cap fuel prec)) (limit : m.index 79=cap fuel prec)
    (scale : m.data L.scalePtr=(2:K)^(prec+2)) (input : ∀i<n,m.data (L.magBase+i)=mag i)
    (positive : ∀i<n,0<mag i) (eligible : ∀i<n,allowed (mag i)) (native : NativeSafe P allowed fuel prec)
    (codes : ∀i<n,P (numeratorWord (fieldProxyNumerator fuel prec (mag i)))) :
    ∃ t, materialize.Run P m (cacheCost n fuel prec) t ∧ StableCache t L n fuel prec mag ∧
      t.index 60=m.index 60 ∧ ∀ j, 80≤j → (j<L.flagBase ∨ L.flagBase+n≤j) → t.index j=m.index j := by
  obtain ⟨t,e,h,h60,hi,_⟩ := materialize_framed P allowed fuel prec n L mag m hs hz head sep limit scale
    input positive eligible native codes
  exact ⟨t,e,h,h60,hi⟩

/-- One fixed ordinary program computes the same integer-valued cache over every ordered field. -/
theorem materialize_field (fuel prec n : ℕ) (L : Buffers) (mag : ℕ→K) (m : Memory K)
    (head : Header m L n fuel prec) (sep : Separated L n (cap fuel prec)) (limit : m.index 79=cap fuel prec)
    (scale : m.data L.scalePtr=(2:K)^(prec+2)) (input : ∀i<n,m.data (L.magBase+i)=mag i)
    (positive : ∀i<n,0<mag i) :
    ∃ k≤cacheCost n fuel prec+1, ∃ tr : Fin (k+1)→State K,
      Trace (materialize.program 0) (m.atPC 0) k tr ∧ (tr (Fin.last k)).output=some 0 ∧
      StableCache (tr (Fin.last k)).memory L n fuel prec mag ∧ (tr (Fin.last k)).index 60=m.index 60 := by
  obtain ⟨t,run,out,capacity,_⟩ := materialize_run (fun _ => True) (fun _ => True) fuel prec n L mag m
    (fun _ => True.intro) True.intro head sep limit scale input positive (fun _ _ => True.intro)
    (by intro; intros; trivial) (fun _ _ => True.intro)
  obtain ⟨k,hk,tr,trace,tag,mem,_⟩ := Fragment.run_halt run 0
  have actual : (tr (Fin.last k)).memory.index 60=m.index 60 := by rw [mem]; exact capacity
  exact ⟨k,hk,tr,trace,tag,mem ▸ out,actual⟩

end MinorProxyCache
end Compression
end LinearProgramming
end Optimization
end OAI
