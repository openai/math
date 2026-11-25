import OAI.Hierarchy.HistorySelectedReceiverLoop
import OAI.ThreeFlat.RAM.HistorySelectedFrame
import OAI.ThreeFlat.RAM.HistoryStageResources

namespace OAI
/-! # Retaining physical receiver cache records at the actual election cursor -/

namespace Hierarchy.HistorySelectedReceiverLoop
open ThreeFlat RAM RAM.PhysicalProcedure RAM.HistoryNodeDirectory
open RAM.HistoryNodeDirectory.Selected RAM.HistoryStageBody.Physical Diagonal.TickWorkspace
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped BigOperators Fin.CommRing
noncomputable section

variable {F : Type*} {W n u : ℕ}

/-- One native stage or leaf run and its exact private writes, before advancing the ledger. -/
structure Emitted (bank : Archive) (leafProc : Procedure W) (fs : List Family)
    (D : Directory W n) (values : Fin n→NodeValue F) (tag : ((Fin 3→Bool)→F)→ℕ)
    (price : ℕ→ℕ) (seed : Fin n→ℕ) (arm : Fin n→Family→ℕ) (j : Fin n)
    (before : Memory W) : Prop where
  header : nodeAddress u before+5<2^W
  stageRoom : ∀ f∈fs,(before (nodeAddress u before)).val=kind f.mode →
    stageAddress u before+48<2^W ∧ f.oldPorts<2^W
  paid : bodyCost u before (seed j) (arm j) fs≤price j.val
  output : ∃ out,
    (∀ f,fs.find? (matchesFamily u before)=some f →
      (HistoryStageBody.procedure (layout u bank f) f.childBound W).Exec before out (arm j f)) ∧
    (fs.find? (matchesFamily u before)=none → leafProc.Exec before out (seed j)) ∧
    (values j).Cached tag u j.val out ∧ ∀ a,OutsideNode u j.val a→ out a=before a

variable {bank : Archive} {leaf : Procedure W} {fs : List Family}
  {D : Directory W n} {values : Fin n→NodeValue F} {tag : ((Fin 3→Bool)→F)→ℕ}
  {price : ℕ→ℕ} {seed : Fin n→ℕ} {arm : Fin n→Family→ℕ}

private theorem no_stage_on_seed {w : ℕ} (u : ℕ) (m : Memory w)
    (seed : (m (nodeAddress u m)).val=0) (f : Family) : matchesFamily u m f=false := by
  cases h : matchesFamily u m f with
  | false => rfl
  | true =>
    have tag := (of_decide_eq_true h).1
    rw [seed] at tag
    cases hm : f.mode <;> simp [hm,kind] at tag

/-- On the physical tag zero all guards run and the billed time is exactly
their total charge plus the leaf's own steps. -/
theorem bodyCost_seed_at {w : ℕ} (u : ℕ) (m : Memory w) (seed : (m (nodeAddress u m)).val=0)
    (leaf : ℕ) (arm : Family→ℕ) (fs : List Family) :
    bodyCost u m leaf arm fs=leaf+guardFee fs := by
  induction fs with
  | nil => simp [bodyCost,guardFee]
  | cons f fs ih =>
    simp only [bodyCost,no_stage_on_seed u m seed,Bool.false_eq_true,ite_false,
      guardFee,List.map_cons,List.sum_cons] at *
    rw [ih,enabled_work u 0 f f]
    omega

theorem Emitted.ofSeed {j : Fin n} {before out : Memory W}
    (zero : (before (nodeAddress u before)).val=0) (header : nodeAddress u before+5<2^W)
    (budget : seed j+guardFee fs≤price j.val) (run : leaf.Exec before out (seed j))
    (saved : (values j).Cached tag u j.val out) (frame : ∀a,OutsideNode u j.val a→ out a=before a) :
    Emitted (u:=u) bank leaf fs D values tag price seed arm j before := by
  have miss : fs.find? (matchesFamily u before)=none := by
    apply List.find?_eq_none.mpr
    intro f _
    simp [no_stage_on_seed u before zero f]
  refine ⟨header,?_,?_,out,?_,fun _=>run,saved,frame⟩
  · intro f _ h
    rw [zero] at h
    cases eqn : f.mode <;> simp [eqn,kind] at h
  · rw [bodyCost_seed_at u before zero]
    exact budget
  · intro f h
    rw [miss] at h
    contradiction

theorem Emitted.ofStage {j : Fin n} {before out : Memory W} (f : Family)
    (selected : fs.find? (matchesFamily u before)=some f) (header : nodeAddress u before+5<2^W)
    (fitted : ∀ g∈fs,(before (nodeAddress u before)).val=kind g.mode →
      stageAddress u before+48<2^W ∧ g.oldPorts<2^W)
    (budget : bodyCost u before (seed j) (arm j) fs≤price j.val)
    (run : (HistoryStageBody.procedure (layout u bank f) f.childBound W).Exec before out (arm j f))
    (saved : (values j).Cached tag u j.val out) (frame : ∀a,OutsideNode u j.val a→ out a=before a) :
    Emitted (u:=u) bank leaf fs D values tag price seed arm j before := by
  refine ⟨header,fitted,budget,out,?_,?_,saved,frame⟩
  · intro g hit
    rw [selected] at hit
    cases hit
    exact run
  · intro miss
    rw [selected] at miss
    contradiction

/-- The action leaves the sole ownership counter and all earlier caches readable.
The owner bank is the chronological directory that was mounted before this sweep. -/
theorem emitted_step {keep : ℕ→Prop} {input m : Memory W} (j : Fin n)
    (reached : Ledger u D tag values keep input j.val m)
    (node : Emitted (u:=u) bank leaf fs D values tag price seed arm j (bump (ownerData W u) m))
    (room : n<2^W) (wide : 2<2^W) (space : base u 19<2^W)
    (arena : base u 12+(j.val+1)*(volume u)^2≤base u 13)
    (cache : base u 13+8*j.val+8≤base u 14)
    (owners : ∀ i col, let x:=(addresses (ownerData W u) D i col).val
      OutsideNode u j.val x ∧ x≠base u 18)
    (persistent : ∀x,keep x→OutsideNode u j.val x ∧ x≠base u 18)
    (prior : ∀ k : Fin n,k.val<j.val→picked D k.val=true→
      (values k).stream+4*(values k).net.cells≤base u 12+(k.val+1)*(volume u)^2 ∧
      (values k).ext+(values k).external≤base u 12+(k.val+1)*(volume u)^2) :
    (body u bank leaf fs).Spec (·=bump (ownerData W u) m)
      (fun _ o=>Ledger u D tag values keep input (j.val+1) o) (price j.val) := by
  obtain ⟨out,stage,seedRun,saved,frame⟩ := node.output
  have ctrl : base u 18<2^W := by
    have sep := apart (u:=u) (by decide : 18<19)
    omega
  have advanced : Ledger u D tag values keep input (j.val+1) out :=
    Ledger.emitted u j.val tag reached j.isLt room space arena cache
      owners persistent prior frame saved
  let before := bump (ownerData W u) m
  have executed : (body u bank leaf fs).Exec before out (bodyCost u before (seed j) (arm j) fs) :=
    body_spec W u bank leaf fs before (fun _ o=>o=out) (seed j) (arm j) wide ctrl
      node.header node.stageRoom stage seedRun
  intro labels regs slots machine pc reg pub exit installed table cfg memory start initial
  obtain ⟨ticks,paid,last,result,run,halted,same⟩ :=
    executed machine pc reg pub exit installed table cfg memory start initial
  exact ⟨ticks,paid.trans node.paid,last,result,run,halted,same.symm ▸ advanced⟩

/-- All successful visits are charged exactly once to their true physical root. -/
theorem run {keep : ℕ→Prop} {input : Memory W} {cap : ℕ}
    (owner : Recorded (ownerData W u) D input)
    (len : (input ((ownerData W u) 4).val).val+(input ((ownerData W u) 5).val).val=n)
    (room : n<2^W) (different : ((ownerData W u) 0+1).val≠((ownerData W u) 0).val)
    (counts : ∀ j : Fin 2,((ownerData W u) ⟨4+j.val,by omega⟩).val≠((ownerData W u) 0).val)
    (dirs : ∀ i j,(addresses (ownerData W u) D i j).val≠((ownerData W u) 0).val ∧
      (addresses (ownerData W u) D i j).val≠((ownerData W u) 0+1).val)
    (immutable : ∀ a,keep a → a≠((ownerData W u) 0).val ∧ a≠((ownerData W u) 0+1).val)
    (aside : ∀ j : Fin n,∀ a,(values j).uses u j.val a → a≠((ownerData W u) 0).val)
    (wide : 2<2^W) (space : base u 19<2^W)
    (arena : ∀ j : Fin n,base u 12+(j.val+1)*(volume u)^2≤base u 13)
    (cache : ∀ j : Fin n,base u 13+8*j.val+8≤base u 14)
    (owners : ∀ j : Fin n,∀ i col, let x:=(addresses (ownerData W u) D i col).val
      OutsideNode u j.val x ∧ x≠base u 18)
    (persistent : ∀ j : Fin n,∀x,keep x→OutsideNode u j.val x ∧ x≠base u 18)
    (sizes : ∀ i : Fin n,picked D i.val=true →
      (values i).stream+4*(values i).net.cells≤base u 12+(i.val+1)*(volume u)^2 ∧
      (values i).ext+(values i).external≤base u 12+(i.val+1)*(volume u)^2)
    (visits : ∀ (j : Fin n) m,Ledger u D tag values keep input j.val m → picked D j.val=true →
      Emitted (u:=u) bank leaf fs D values tag price seed arm j (bump (ownerData W u) m))
    (budget : 17+24*n+∑ root : Word W, (if D.owner root=(D.group,D.slot) then
      ∑ j : {i : Fin n // D.root i=root},price j.val.val else 0) ≤ cap) :
    (selected u bank leaf fs).Spec (·=input) (fun _ out=>Ledger u D tag values keep input n out) cap := by
  classical
  let d := ownerData W u
  let inv := fun (_ : Memory W) i m=>Ledger u D tag values keep input i m
  have apart (i : Fin n) (j : Fin 5) : addresses d D i j≠d 0 :=
    fun eq=>(dirs i j).1 (congrArg Fin.val eq)
  have sim := procedure_owners d (body u bank leaf fs) D price (·=input) inv
  intro labelCount registerCount slotCount machine
  refine Procedure.Spec.mono (A:=procedure d (body u bank leaf fs))
    (sim ?_ ?_ ?_ apart ?_ ?_) (fun _ h=>h) (fun _ _ h=>h) budget machine
  · intro a eq; subst a
    exact Ledger.start d rfl owner len room different (counts 0) (counts 1) dirs immutable
  · intro _ i m L; exact ⟨L.cursor,L.stop⟩
  · intro _ i m L; exact L.directory
  · intro _ i m L h off
    exact L.skip h off room different apart (fun a h=>(immutable a h).1)
      (fun j _ _ a h=>aside j a h)
  · intro _ i _ hi on P R K M pc reg kd exit inst slots cfg bumped start live
    obtain ⟨m,L,rfl⟩:=live
    let j : Fin n:=⟨i,hi⟩
    exact (emitted_step j L (visits j m L on) room wide space (arena j) (cache j)
      (owners j) (persistent j) (fun k _ hk=> sizes k hk)) M pc reg kd exit inst slots cfg _ start rfl

end
end Hierarchy.HistorySelectedReceiverLoop

end OAI
