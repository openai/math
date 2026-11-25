import OAI.Optimization.LinearProgramming.Compression.MinorProxyCacheLayout
import OAI.Optimization.LinearProgramming.Compression.MinorProxyCacheScale
import OAI.Optimization.LinearProgramming.Compression.MinorProxyCachePlan
import OAI.Optimization.LinearProgramming.PrimalDual.DecoderHeader
import OAI.Optimization.LinearProgramming.PrimalDual.OutputSetup
import OAI.Optimization.LinearProgramming.RAM.RAMFrame

/-! Allocate the live logarithm buffers from five ordinary runtime addresses. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace MinorProxyCache
open RAM RAM.Block RAM.Tape PrimalDual

/-- The magnitude copy lies above both its original source and the native scratch
area. Flags start beyond the caller's high address range, in the separate address bank. -/
def buffers (n fuel prec src addressEnd : ℕ) : Buffers :=
  let M := 128+cap fuel prec+src+n
  ⟨M,M+n,128+addressEnd,M+n+n⟩

theorem buffers_separated (n fuel prec src addressEnd : ℕ) :
    Separated (buffers n fuel prec src addressEnd) n (cap fuel prec) := by
  refine ⟨max_le ?_ ?_,max_le ?_ ?_,?_,max_le ?_ ?_,.inl le_rfl,.inr le_rfl⟩ <;>
    dsimp [buffers] <;> omega

private def bodyCost (n fuel prec src addressEnd : ℕ) :=
  headerCost n fuel prec src addressEnd+7*n+4*prec+9

private def allocateBody : Block := .seq (PrimalDual.Header.write 76 allocationTerms)
  (.seq (copyFromRegs false 76 80 83) writeScale)

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem body_eval (P : K→Prop) (m : Memory K) (safe : m.AllData P) (n fuel prec src addressEnd : ℕ)
    (h0 : m.index 0=n) (h1 : m.index 1=fuel) (h2 : m.index 2=prec) (h3 : m.index 3=src)
    (h4 : m.index 4=addressEnd) (powers : ∀ j≤prec,P ((2:K)^(j+2))) :
    let L := buffers n fuel prec src addressEnd
    ∃ t k, k≤bodyCost n fuel prec src addressEnd ∧ Block.Eval (Memory.AllData P) allocateBody m k t ∧
      Header t L n fuel prec ∧ t.index 79=cap fuel prec ∧ t.data L.scalePtr=(2:K)^(prec+2) ∧
      (∀i<n,t.data (L.magBase+i)=m.data (src+i)) ∧
      (∀ j,6≤j → j<76 → j≠63 → t.index j=m.index j) ∧
      (∀ j,cap fuel prec≤j → (j<L.magBase ∨ L.scalePtr<j) → t.data j=m.data j) := by
  let L := buffers n fuel prec src addressEnd
  let env : Fin 5→ℕ := ![n,fuel,prec,src,addressEnd]
  have read (i : Fin 5) : m.index i.val=env i := by fin_cases i <;> simp [env,h0,h1,h2,h3,h4]
  obtain ⟨u,j,first,hj,data,before,w⟩ := PrimalDual.Header.write_correct (P := P) allocationTerms env
    76 m (by decide) read safe
  have cost : j≤headerCost n fuel prec src addressEnd := calc
    j ≤ (allocationTerms.map (·.cost env)).sum := hj
    _ = headerCost n fuel prec src addressEnd := allocationTerms_cost n fuel prec src addressEnd
  have base : u.index 76=src := w ⟨0,by decide⟩
  have limit : u.index 79=cap fuel prec := w ⟨3,by decide⟩
  have head : Header u L n fuel prec := ⟨w ⟨4,by decide⟩,w ⟨5,by decide⟩,w ⟨6,by decide⟩,
    w ⟨7,by decide⟩,w ⟨8,by decide⟩,w ⟨9,by decide⟩,w ⟨10,by decide⟩⟩
  have big : src+n≤L.magBase := by dsimp [L,buffers]; omega
  have pos : 0<L.magBase := by dsimp [L,buffers]; omega
  obtain ⟨v,copy,words,cframe,keep⟩ := copyFromRegs_correct (P := P) false n src L.magBase 76 80 83 u
    first.safe_end (by decide) (by decide) (by decide) base head.magnitudes head.size (.inl big) pos
  have vh := head.transfer (fun a lo _ => keep a (by omega))
  obtain ⟨t,scale,wrote,frame,indices⟩ := writeScale_eval P v copy.safe_end prec vh.precision powers
  refine ⟨t,_,?_,first.seq (copy.seq scale),vh.transfer (fun a lo _ => indices a (by omega)),?_,?_,?_,?_,?_⟩
  · unfold bodyCost; omega
  · exact (indices 79 (by decide)).trans ((keep 79 (by decide)).trans limit)
  · simpa only [vh.scalePtr] using wrote
  · intro i hi
    have ne : L.magBase+i≠v.index 86 := by rw [vh.scalePtr]; dsimp [L,buffers]; omega
    exact (frame _ (by omega) ne).trans ((words i hi).trans (congrFun data _))
  · intro a ha lo ne
    exact (indices a ne).trans ((keep a ha).trans (before a lo))
  · intro a ha outside
    have hz : a≠0 := by dsimp [cap] at ha; omega
    have ne : a≠v.index 86 := by rw [vh.scalePtr]; dsimp [L,buffers] at outside ⊢; omega
    have off : a<L.magBase ∨ L.magBase+n≤a := by dsimp [L,buffers] at outside ⊢; omega
    exact (frame a hz ne).trans ((cframe a hz off).trans (congrFun data a))

private def saveStaging : List CursorBind := [.reg 74 87,.reg 75 88]
private def restoreStaging : List CursorBind := [.reg 87 74,.reg 88 75]

/-- Address-expression temporaries may reach 87 and 88. Park both caller staging
pointers below the allocation block, then restore them before exposing the cache. -/
def allocate : Block := .seq (CursorBind.script saveStaging)
  (.seq allocateBody (CursorBind.script restoreStaging))

def allocationCost (n fuel prec src addressEnd : ℕ) :=
  bodyCost n fuel prec src addressEnd+4

theorem allocationCost_eq (n fuel prec src addressEnd : ℕ) :
    allocationCost n fuel prec src addressEnd =
      headerCost n fuel prec src addressEnd+7*n+4*prec+13 := by
  unfold allocationCost bodyCost; omega

structure HighFrame (m t : Memory K) (L : Buffers) (bound : ℕ) : Prop where
  scalar : ∀ j,bound≤j → (j<L.magBase ∨ L.scalePtr<j) → t.data j=m.data j
  address : ∀ j,128≤j → t.index j=m.index j
  scalarStaging : t.index 87=m.index 87
  addressStaging : t.index 88=m.index 88
  driver : ∀j,90≤j → j<128 → t.index j=m.index j

theorem allocate_framed (P : K→Prop) (m : Memory K) (safe : m.AllData P) (n fuel prec src addressEnd : ℕ)
    (h0 : m.index 0=n) (h1 : m.index 1=fuel) (h2 : m.index 2=prec) (h3 : m.index 3=src)
    (h4 : m.index 4=addressEnd) (powers : ∀ j≤prec,P ((2:K)^(j+2))) :
    let L := buffers n fuel prec src addressEnd
    ∃ t k, k≤allocationCost n fuel prec src addressEnd ∧ Block.Eval (Memory.AllData P) allocate m k t ∧
      Header t L n fuel prec ∧ t.index 79=cap fuel prec ∧ t.data L.scalePtr=(2:K)^(prec+2) ∧
      (∀i<n,t.data (L.magBase+i)=m.data (src+i)) ∧ t.index 60=m.index 60 ∧
      HighFrame m t L (cap fuel prec) := by
  let a := CursorBind.install saveStaging m
  have pre : Block.Eval (Memory.AllData P) (CursorBind.script saveStaging) m 2 a := CursorBind.run _ _ safe
  have alo (j : ℕ) (hj : j<74) : a.index j=m.index j := by
    simp [a,saveStaging,CursorBind.install,CursorBind.apply,show j≠74 by omega, show j≠75 by omega]
  obtain ⟨w,k,hk,middle,head,limit,scale,words,keep,frame⟩ := body_eval P a pre.safe_end n fuel prec src addressEnd
    ((alo 0 (by decide)).trans h0) ((alo 1 (by decide)).trans h1) ((alo 2 (by decide)).trans h2)
    ((alo 3 (by decide)).trans h3) ((alo 4 (by decide)).trans h4) powers
  let t := CursorBind.install restoreStaging w
  have post : Block.Eval (Memory.AllData P) (CursorBind.script restoreStaging) w 2 t := CursorBind.run _ _ middle.safe_end
  have ti (j : ℕ) (e : j≠87) (f : j≠88) : t.index j=w.index j := by
    simp [t,restoreStaging,CursorBind.install,CursorBind.apply,e,f]
  refine ⟨t,_,by unfold allocationCost; omega,pre.seq (middle.seq post),
    head.transfer (fun j _ hi => ti j (by omega) (by omega)),(ti 79 (by decide) (by decide)).trans limit,
    scale,words,(ti 60 (by decide) (by decide)).trans ((keep 60 (by decide) (by decide) (by decide)).trans (alo 60 (by decide))),?_⟩
  have static : allocateBody.indexWritesBelow 90=true := by decide
  have w74 := keep 74 (by decide) (by decide) (by decide)
  have w75 := keep 75 (by decide) (by decide) (by decide)
  have highIndex (j : ℕ) (hj : 90≤j) : t.index j=m.index j := by
    rw [ti j (by omega) (by omega),middle.index_frame static hj]
    simp [a,saveStaging,CursorBind.install,CursorBind.apply,show j≠74 by omega,show j≠75 by omega]
  refine ⟨frame,fun j hj => highIndex j (by omega),?_,?_,fun j hj _ => highIndex j hj⟩
  · simp [t,restoreStaging,CursorBind.install,CursorBind.apply,w74,a,saveStaging]
  · simp [t,restoreStaging,CursorBind.install,CursorBind.apply,w75,a,saveStaging]

theorem allocate_eval (P : K→Prop) (m : Memory K) (safe : m.AllData P) (n fuel prec src addressEnd : ℕ)
    (h0 : m.index 0=n) (h1 : m.index 1=fuel) (h2 : m.index 2=prec) (h3 : m.index 3=src)
    (h4 : m.index 4=addressEnd) (powers : ∀ j≤prec,P ((2:K)^(j+2))) :
    let L := buffers n fuel prec src addressEnd
    ∃ t k, k≤allocationCost n fuel prec src addressEnd ∧ Block.Eval (Memory.AllData P) allocate m k t ∧
      Header t L n fuel prec ∧ t.index 79=cap fuel prec ∧ t.data L.scalePtr=(2:K)^(prec+2) ∧
      (∀i<n,t.data (L.magBase+i)=m.data (src+i)) ∧ t.index 60=m.index 60 := by
  obtain ⟨t,k,hk,e,h,l,d,w,keep,_⟩ := allocate_framed P m safe n fuel prec src addressEnd h0 h1 h2 h3 h4 powers
  exact ⟨t,k,hk,e,h,l,d,w,keep⟩

end MinorProxyCache
end Compression
end LinearProgramming
end Optimization
end OAI
