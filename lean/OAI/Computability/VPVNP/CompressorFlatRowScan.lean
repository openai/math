import OAI.Computability.VPVNP.CompressorFlatRowWorker
import OAI.Computability.VPVNP.CompressorSourceWalk

/-!
# Visiting every bundle in one online calendar stage

The persistent cursor of a calendar visit is the bundle ordinal. Its report
updates that bundle's bank and advances the cursor. A finite stage list may
therefore transpose the fixed per-bundle operations while retaining the
input columns and every previously completed bank.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.FlatRows

open BurstRAM

variable {w R : ℕ} {C J : Type*}

theorem scan (P : BurstRAM.Program w C) (fuel : ℕ) (R : ℕ)
    (shared : Memory w → Prop) (bank : Fin R → ℕ → Prop)
    (apart : ∀ {i j : Fin R}, i ≠ j → ∀ x, bank i x → ¬ bank j x)
    (before done : Fin R → Memory w → Prop)
    (keepBefore : ∀ i m out, before i m → (∀ x, bank i x → out x = m x) → before i out)
    (keepDone : ∀ i m out, done i m → (∀ x, bank i x → out x = m x) → done i out)
    (one : ∀ i : Fin R, ∀ m, shared m → before i m →
      ∃ r, execute P fuel (P.start (Fin.ofNat _ i.val)) m [] = some r ∧
        r.result = some (Fin.ofNat _ (i.val+1)) ∧ shared (after m r.events) ∧ done i (after m r.events) ∧
        ∀ x, ¬ bank i x → after m r.events x = m x)
    (m : Memory w) (hshared : shared m) (ready : ∀ i, before i m) :
    ∃ rs, runSegment P fuel (some 0) m (List.replicate R []) = some rs ∧
      endState (some 0) rs = some (Fin.ofNat _ R) ∧ rs.length = R ∧
      shared (after m (eventLog rs)) ∧ (∀ i, done i (after m (eventLog rs))) ∧
      ∀ x, (∀ i, ¬ bank i x) → after m (eventLog rs) x = m x := by
  have sweep (k len : ℕ) (room : k+len ≤ R) (mem : Memory w)
      (hs : shared mem) (rows : ∀ i : Fin R, (if i.val < k then done i mem else before i mem)) :
      ∃ rs, runSegment P fuel (some (Fin.ofNat _ k)) mem (List.replicate len []) = some rs ∧
        endState (some (Fin.ofNat _ k)) rs = some (Fin.ofNat _ (k+len)) ∧ rs.length = len ∧
        shared (after mem (eventLog rs)) ∧
        (∀ i : Fin R, if i.val < k+len then done i (after mem (eventLog rs)) else before i (after mem (eventLog rs))) ∧
        ∀ x, (∀ i, ¬ bank i x) → after mem (eventLog rs) x = mem x := by
    induction len generalizing k mem with
    | zero => exact ⟨[],rfl,rfl,rfl,hs,rows,fun _ _ => rfl⟩
    | succ len ih =>
      let i : Fin R := ⟨k,by omega⟩
      obtain ⟨r,exec,ret,shared',row,frame⟩ := one i mem hs (by simpa [i] using rows i)
      let post := after mem r.events
      have status (j : Fin R) : if j.val < k+1 then done j post else before j post := by
        by_cases eq : j = i
        · subst j; simpa [i,post] using row
        · have hv : j.val ≠ k := fun e => eq (Fin.ext e)
          have preserve (x) (hx : bank j x) : post x = mem x := frame x (apart eq x hx)
          by_cases lt : j.val < k
          · rw [ite_eq_left (by omega)]
            exact keepDone _ _ _ (by simpa only [ite_eq_left lt] using rows j) preserve
          · rw [ite_eq_right (by omega)]
            exact keepBefore _ _ _ (by simpa only [ite_eq_right lt] using rows j) preserve
      obtain ⟨tail,run,end',size,hs',rows',outside⟩ := ih (k+1) (by omega) post shared' status
      have replay : after mem (eventLog (r::tail)) = after post (eventLog tail) := by
        change List.foldl update mem (r.events ++ eventLog tail) = _
        rw [List.foldl_append]; rfl
      refine ⟨r::tail,?_,?_,by simp [size],replay ▸ hs',?_,?_⟩
      · rw [List.replicate_succ,runSegment,exec]
        simp only [ret,i,run,Option.map_some,post] at *
      · change endState r.result tail = _
        rw [ret,end',show k+1+len = k+(len+1) by omega]
      · intro j; rw [replay,show k+(len+1) = k+1+len by omega]; exact rows' j
      · intro x hx; exact (congrFun replay x).trans ((outside x hx).trans (frame x (hx i)))
  obtain ⟨rs,run,hend,hlen,hs,rows,frame⟩ := sweep 0 R (by omega) m hshared (by simpa using ready)
  exact ⟨rs,run,by simpa using hend,hlen,hs,fun i => by simpa using rows i,frame⟩

/-- Compose the calendar visits in their actual list order, retaining the
post-memory for all stages. -/
theorem walk {source : J → Memory w → List (Report w) → Prop}
    (js : List J) (inv : ℕ → Memory w → Prop) (start : ℕ) (m : Memory w) (hm : inv start m)
    (step : ∀ i : Fin js.length, ∀ m, inv (start+i.val) m →
      ∃ rs, source js[i.val] m rs ∧ inv (start+i.val+1) (after m (eventLog rs))) :
    ∃ rs, SourceWalk source js m rs ∧ inv (start+js.length) (after m (eventLog rs)) := by
  induction js generalizing m start with
  | nil => exact ⟨[],.done _,hm⟩
  | cons j js ih =>
    obtain ⟨head,hh,hn⟩ := step 0 m (by simpa using hm)
    obtain ⟨tail,ht,hf⟩ := ih (start+1) _ hn (fun i m h => by
      simpa only [List.getElem_cons_succ,Fin.val_succ,show start+(i.val+1) = start+1+i.val by omega] using
        step i.succ m (by simpa only [Fin.val_succ,show start+(i.val+1) = start+1+i.val by omega] using h))
    refine ⟨head++tail,.next hh ht,?_⟩
    rw [SourceWalk.after_append,List.length_cons,show start+(js.length+1) = start+1+js.length by omega]
    exact hf

end CompressorRecords.FlatRows

end VPVNP
end Computability
end OAI
