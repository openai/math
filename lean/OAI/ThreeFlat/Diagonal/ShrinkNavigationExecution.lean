import OAI.ThreeFlat.Diagonal.NavigationPass
import OAI.ThreeFlat.RAM.AdmissionPost
import OAI.ThreeFlat.RAM.HeaderScanState

namespace OAI
/-! # Computing the installed shrinking-stage memory transform and its exact cost -/
namespace ThreeFlat.Diagonal.NavigationPass
open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.PhysicalProcedure RAM.DescriptorScan
open CompressorPacking.Native
open scoped Fin.NatCast
variable {w : ℕ}

structure Execution (w : ℕ) where
  code : Procedure w
  run : Memory w → ℕ × Memory w
  fits : Memory w → Prop
  correct : ∀ m, fits m →
    code.Spec (fun z=>z=m) (fun _ out=>out=(run m).2) (run m).1

namespace Execution

noncomputable def seq (A B : Execution w) : Execution w where
  code := A.code.seq B.code
  run m := let a:=A.run m; let b:=B.run a.2; (a.1+b.1,b.2)
  fits m := A.fits m ∧ B.fits (A.run m).2
  correct m h := by
    exact Procedure.Spec.mono
      (Procedure.Spec.seq (A.correct m h.1) (B.correct _ h.2) (fun _ _ same=>same))
      (fun _ same=>same) (fun _ _ result=>result.choose_spec.2) le_rfl

noncomputable def pass (current : Word w) (p : ShrinkStage.Pass w) : Execution w where
  code := scan current p
  run := p.execute current (fun _=>0)
  fits := p.fits current (fun _=>0)
  correct m h := by
    intro n r k M pc reg pub exit inst data c old entry same
    subst old
    change Fin 1 → Fin k at pub
    have params : M.publicData ∘ pub = fun _=>0 := funext data
    have valid : p.fits current (M.publicData ∘ pub) m := params.symm ▸ h
    obtain ⟨endConf,atEnd,run⟩ := p.run current M pc reg pub exit inst c m entry valid
    rw [params] at run
    exact ⟨_,le_rfl,endConf,_,run,atEnd,rfl⟩

noncomputable def header (current : Word w) (start count : ℕ) (f : PhysicalPinsExpr.Formula 1) : Execution w :=
  let e := HeaderScan.closed (w:=w) f
  let low := fun m=>ShrinkStage.headerRead m current start
  let len := fun m=>(ShrinkStage.headerRead m current count).val
  { code := HeaderScan.procedure current start count e
    run m := (11+len m*(2*e.binds+4),sweep (fun a z=>e.eval Fin.elim0 z (fun _=>a)) (len m) (low m) m)
    fits m := (low m).val+len m<2^w
    correct m h := by
      intro n r k M pc reg pub exit inst data c old entry same
      subst old
      change Fin 0 → Fin k at pub
      have cast (v : Word w) : (v.val:Word w)=v := Fin.cast_val_eq_self _
      have pubEq : M.publicData ∘ pub = (Fin.elim0 : Fin 0 → Word w) := funext fun i=>i.elim0
      obtain ⟨out,atEnd,run⟩ := HeaderScan.block_sweep e current start count (low m).val (len m) h
        pc reg pub exit M inst c m entry (cast _).symm (cast _).symm
      rw [pubEq,cast] at run
      exact ⟨_,le_rfl,out,_,run,atEnd,rfl⟩ }

noncomputable def next (current : Word w) : Execution w where
  code := NextStage.procedure current
  run m := (6,NextStage.memory current m)
  fits _ := True
  correct m _ := NextStage.spec current m


end Execution
end ThreeFlat.Diagonal.NavigationPass

end OAI
