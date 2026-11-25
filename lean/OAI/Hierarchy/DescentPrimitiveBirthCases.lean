import OAI.Hierarchy.DescentPrimitiveBirthProgram
import OAI.Hierarchy.DescentResetActorClassIssued
import OAI.Hierarchy.DescentResetTapEmission

namespace OAI
/-! # The authentic primitive outputs at the five physical actor classes -/
namespace Hierarchy.DescentPrimitiveBirth.Layout
open DescentSIMDLookup DescentResetActorClass DescentResetMetadataInputs
open scoped Classical Fin.CommRing
noncomputable section
variable (z : DescentPrimitiveBirth.Layout) (n : Fin z.nodes)
  (cls : Cell z.classBits) (paid : Cell z.paidBits) (spans : Fin z.arguments→Cell z.spanBits) (v : Fin z.roots→Cell z.rootBits)

theorem relay_at : z.tagRelay (z.admitted n cls paid)=if n.val<paid.val ∧ cls.val=2 then 1 else 0:=by
  by_cases live:n.val<paid.val <;> simp [tagRelay,admitted,live]

theorem blank (empty : paid.val≤n.val) : z.raw n cls paid spans v=0:=by
  simp [raw,admitted,Nat.not_lt.mpr empty,rootId,tag]

theorem scalar_rotation (live : n.val<paid.val) (q : Fin z.roots) (atRoot : cls.val=6+q.val) :
    z.raw n cls paid spans v=v q:=by
  have here : z.rootId cls=some q:=by
    have h:6≤cls.val ∧ cls.val-6<z.roots:=by rw [atRoot];omega
    simp only [rootId,dite_eq_left h,Option.some.injEq]
    apply Fin.ext
    change cls.val-6=q.val
    omega
  simp [raw,admitted,live,here]

theorem primary (atOld : cls.val=1) : z.raw n cls paid spans v=0:=by
  by_cases ok:n.val<paid.val <;>simp [raw,admitted,ok,rootId,tag,atOld]
theorem relay_zero (atRelay : cls.val=2) : z.raw n cls paid spans v=0:=by
  by_cases ok:n.val<paid.val <;>simp [raw,admitted,ok,rootId,tag,atRelay]
theorem fallback (ok : n.val<paid.val) (atFall : cls.val=5) : z.raw n cls paid spans v=5:=by
  simp [raw,admitted,ok,rootId,tag,atFall]
theorem tap (ok : n.val<paid.val) (atTap : cls.val=4) :
    z.raw n cls paid spans v=if z.extra spans=0 then 3 else 5:=by
  simp [raw,admitted,ok,rootId,tag,atTap]

theorem tap_arity {A : Type} {Y p : ℕ} {width : A→ℕ} (units : A→ℕ) (multiple : ∀a,width a=units a*p)
    (hp : 0<p) (prg : DescentLaneGates.Program Y p width) (u : prg.Node)
    (arity : (prg.op u).arity=1 ∨ (prg.op u).arity=2)
    (bound : ((DescentBundleHistory.ofProgram units multiple hp prg).recipe hp).arity u≤z.arguments)
    (read : ∀j,(spans j).val=argumentSpan (DescentBundleHistory.ofProgram units multiple hp prg) u j.val)
    (ok : n.val<paid.val) (atTap : cls.val=4) :
    z.raw n cls paid spans v=if (prg.op u).arity=2 then 5 else 3:=by
  have truth:=(z.another_span (rec:=prg.recipe) (DescentBundleHistory.ofProgram units multiple hp prg) u hp spans bound read).trans (ofProgram_two units multiple hp prg u arity)
  rw [z.tap n cls paid spans v ok atTap]
  by_cases eq:z.extra spans=0
  · simp [eq,show (prg.op u).arity≠2 from fun h=>(truth.mpr h) eq]
  · simp [eq,truth.mp eq]
theorem root_actual {U : ℕ} (depth : z.Population) (words : z.Original) (name : Fin U→Fin z.placement.sparse)
    (x : Fin z.placement.blocks) (h : Fin z.placement.newHosts) (g : Fin z.placement.groups) (present : h.val<U)
    (q : Fin z.roots) (l : Fin (z.residual+1))
    (whereFrom : depth (z.placement.previous (name ⟨_,present⟩)) (finProdFinEquiv (g,x))=some l) :
    z.rootActual depth words name n x q h g=z.digit n
      (words q l (z.placement.previous (name ⟨_,present⟩)) (finProdFinEquiv (g,x))):=by
  simp [rootActual,DescentResetRetainedPlacement.Chart.compact,DescentResetDenseOperand.dense,present,
    DescentResetRetainedPlacement.Chart.selected,whereFrom]
  rfl

theorem root_pad {U : ℕ} (depth : z.Population) (words : z.Original) (name : Fin U→Fin z.placement.sparse)
    (x : Fin z.placement.blocks) (h : Fin z.placement.newHosts) (g : Fin z.placement.groups)
    (absent : U≤h.val) (q : Fin z.roots) : z.rootActual depth words name n x q h g=0:=by
  simp [rootActual,DescentResetRetainedPlacement.Chart.compact,DescentResetDenseOperand.dense,Nat.not_lt.mpr absent]

theorem digit_value (b : Cell (z.rootBits*z.stop)) (live : n.val<z.stop) :
    (z.digit n b).val=DescentSIMDLookup.digit z.rootBits n.val b.val:=by
  let digits := (encode z.rootBits z.stop).symm b
  have h:=digit_encode digits (⟨n.val,live⟩ : Fin z.stop)
  simpa [digit,live,digits] using h.symm

end
end Hierarchy.DescentPrimitiveBirth.Layout

end OAI
