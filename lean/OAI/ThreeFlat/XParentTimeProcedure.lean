import OAI.ThreeFlat.XParentTimeLoop
import OAI.ThreeFlat.RAM.PhysicalProcedure
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.BigOperators

namespace OAI
/-! # A fixed program for a chronological sweep with per-time charges -/

namespace ThreeFlat.XParentTimeLoop
open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.PhysicalProcedure RAM.ContinuationLink
open scoped Fin.CommRing
variable {w : ℕ}

/-- Reset the mutable cursor and visit every time below the length read from memory. -/
def traversal (cursor limit : ℕ) (body : Procedure w) : Procedure w where
  labels := 13+body.labels
  registers := 3+body.registers
  slots := 2+body.slots
  block := XParentTimeLoop.block (Fin.castAddEmb _) (Fin.castAdd _)
    (body.block.reindex (Fin.natAddEmb 3) (Fin.natAdd 2))
  publicData := Fin.addCases (![(cursor:Word w),(limit:Word w)]) body.publicData

open scoped BigOperators
theorem traverse_run (cursor limit N : ℕ) (body : Procedure w) (price : ℕ→ℕ) (state : ℕ→Memory w→Prop)
    (cursorFit : cursor<2^w) (limitFit : limit<2^w) (bound : N<2^w)
    (counter : ∀ j m,state j m → m cursor=(j:Word w))
    (limitAt : ∀ j m,state j m → m limit=(N:Word w))
    (each : ∀ j,j<N → body.Spec (state j)
       (fun _ o=>o cursor=(j:Word w) ∧ state (j+1) (Function.update o cursor ((j+1:ℕ):Word w))) (price j)) :
    (traversal cursor limit body).Spec (fun m=>state 0 (Function.update m cursor (0:Word w))) (fun _ o=>state N o)
      (8+10*N+∑ j∈Finset.range N,price j) := by
  intro P R k M pc reg pub exit placed data st m entry base
  let shell := body.block.reindex (Fin.natAddEmb 3) (Fin.natAdd 2)
  obtain ⟨L,inside⟩ := XParentTimeLoop.installed (Fin.castAddEmb _) (Fin.castAdd _) shell M pc reg pub exit placed
  have low (j : Fin 2) : M.publicData (pub (j.castAdd body.slots))=(![(cursor:Word w),(limit:Word w)]:Fin 2→Word w) j := by
    simpa [traversal] using data (j.castAdd body.slots)
  have cur : (M.publicData (pub ((0:Fin 2).castAdd body.slots))).val=cursor := by
    rw [low];exact Fin.val_cast_of_lt cursorFit
  have stop : (M.publicData (pub ((1:Fin 2).castAdd body.slots))).val=limit := by
    rw [low];exact Fin.val_cast_of_lt limitFit
  have params (j : Fin body.slots) : M.publicData (pub (Fin.natAdd 2 j))=body.publicData j := by
    simpa [traversal] using data (Fin.natAdd 2 j)
  have prefix_run (j : ℕ) (small : j≤N) :
      ∃ n≤3+10*j+∑i∈Finset.range j,price i, ∃ (z : Config w P R) (o : Memory w),
        z.pc=XParentTimeLoop.ctlPC pc XParentTimeLoop.guardPC ∧
        advance M.program n st m=some (z,o) ∧ state j o := by
    induction j with
    | zero =>
      obtain ⟨z,act,atPC⟩ := L.start st m entry
      refine ⟨3,by simp,z,_,atPC,act,?_⟩
      change state 0 (Function.update m (M.publicData (pub ((0:Fin 2).castAdd body.slots))).val 0)
      rwa [cur]
    | succ j ih =>
      obtain ⟨ticks,time,z,o,zpc,run,live⟩ := ih (by omega)
      obtain ⟨u,enter,bodyPC⟩ := L.enter z o j N zpc (by
        change o (M.publicData (pub ((0 : Fin 2).castAdd body.slots))).val = (j : Word w)
        rw [cur,counter j o live]) (by
        change o (M.publicData (pub ((1 : Fin 2).castAdd body.slots))).val = (N : Word w)
        rw [stop,limitAt j o live]) (by omega) bound
      obtain ⟨t,spent,q,returned,insideRun,done,same,rest⟩ := each j (by omega) M
        (XParentTimeLoop.bodyPC pc) ((Fin.natAddEmb 3).trans reg) (pub ∘ Fin.natAdd 2) _
        inside params u o bodyPC live
      obtain ⟨v,step,again⟩ := L.next q returned j done (by
        change returned (M.publicData (pub ((0 : Fin 2).castAdd body.slots))).val = (j : Word w)
        rwa [cur])
      refine ⟨ticks+5+t+5,?_,v,_,again,advance_trans (advance_trans (advance_trans run enter) insideRun) step,?_⟩
      · rw [Finset.sum_range_succ];omega
      · change state (j+1) (Function.update returned (M.publicData (pub ((0:Fin 2).castAdd body.slots))).val _)
        rwa [cur]
  obtain ⟨n,time,z,o,zpc,run,live⟩ := prefix_run N le_rfl
  obtain ⟨v,finish,done⟩ := L.finish z o zpc (by
    change o (M.publicData (pub ((0:Fin 2).castAdd body.slots))).val =
      o (M.publicData (pub ((1:Fin 2).castAdd body.slots))).val
    rw [cur,stop,counter N o live,limitAt N o live])
  exact ⟨n+5,by omega,v,o,advance_trans run finish,done,live⟩

theorem traverse_fin {N : ℕ} (cursor limit : ℕ) (body : Procedure w) (price : Fin N→ℕ)
    (state : ℕ→Memory w→Prop) (cursorFit : cursor<2^w) (limitFit : limit<2^w) (bound : N<2^w)
    (counter : ∀j m,state j m→m cursor=(j:Word w)) (limitAt : ∀j m,state j m→m limit=(N:Word w))
    (each : ∀t : Fin N,body.Spec (state t.val)
      (fun _ o=>o cursor=(t.val:Word w) ∧ state (t.val+1) (Function.update o cursor ((t.val+1:ℕ):Word w)))
      (price t)) :
    (traversal cursor limit body).Spec (fun m=>state 0 (Function.update m cursor (0:Word w)))
      (fun _ o=>state N o) (loopCost N+∑t,price t) := by
  let rate (i : ℕ) := if h : i<N then price ⟨i,h⟩ else 0
  have total : (∑i∈Finset.range N,rate i)=∑t,price t := by
    rw [←Fin.sum_univ_eq_sum_range]
    simp [rate]
  unfold loopCost
  rw [←total]
  apply traverse_run cursor limit N body rate state cursorFit limitFit bound counter limitAt
  intro i hi P R K machine
  simpa only [rate,dite_eq_left hi] using each ⟨i,hi⟩ machine

end ThreeFlat.XParentTimeLoop

end OAI
