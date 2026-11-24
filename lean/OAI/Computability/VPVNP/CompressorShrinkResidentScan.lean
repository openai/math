import OAI.Computability.VPVNP.CompressorShrinkResidentOwners

/-!
# Executing the dense resident owner scan

The role and absolute-CD input cells lie outside the fresh output column.
A pass preserves its source cells while writing exactly one owner for each
dense history index.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ResidentOwners

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM
open scoped Fin.CommRing

variable {w : ℕ}

private def Written (maps : Bool) (p : Fin 4 → Word w) (old m : Memory w) (k : ℕ) : Prop :=
  (∀ j < k, m ((p 3).val+j) = old (roleAddr maps p old (j : Word w)).val) ∧
  ∀ a, a < (p 3).val ∨ (p 3).val+k ≤ a → m a = old a

private theorem scan_from (maps : Bool) (p : Fin 4 → Word w) (old : Memory w) (N : ℕ)
    (fits : (p 3).val+N ≤ 2^w)
    (inputs : ∀ i : Word w, i.val < N →
      ((absoluteAddr maps p i).val < (p 3).val ∨ (p 3).val+N ≤ (absoluteAddr maps p i).val) ∧
      ((roleAddr maps p old i).val < (p 3).val ∨ (p 3).val+N ≤ (roleAddr maps p old i).val))
    {k n : ℕ} {m : Memory w} (bound : k+n ≤ N) (done : Written maps p old m k) :
    let W := (worker maps).table.instantiate w p
    ∃ rs, runSegment W.program (1+(code maps).length) (some (k : Word w)) m (List.replicate n []) = some rs ∧
      Written maps p old (after m (eventLog rs)) (k+n) ∧ rs.length = n ∧
      (∀ r ∈ rs, r.events.length = (code maps).length ∧ countProbes r.events = 3 ∧ choiceBits r.events = []) ∧
      RAMBuckets.cost Report.probes rs = 4*n := by
  intro W
  induction n generalizing k m with
  | zero => exact ⟨[],rfl,done,rfl,by simp,rfl⟩
  | succ n ih =>
    let i : Word w := (k : Word w)
    have hk : k < N := by omega
    have hi : i.val = k := Nat.mod_eq_of_lt (by omega)
    have hr := inputs i (hi ▸ hk)
    have keep (addr : ℕ) (ha : addr < (p 3).val ∨ (p 3).val+N ≤ addr) : m addr = old addr :=
      done.2 addr (by omega)
    have hrole : roleAddr maps p m i = roleAddr maps p old i := by
      unfold roleAddr
      rw [keep _ hr.1]
    have hval : m (roleAddr maps p m i).val = old (roleAddr maps p old i).val := by
      rw [hrole]; exact keep _ hr.2
    have haddr : (p 3+i).val = (p 3).val+k := by
      rw [Fin.val_add,hi,Nat.mod_eq_of_lt (by omega)]
    let u := writeMemory m (p 3+i) (m (roleAddr maps p m i).val)
    have step : Written maps p old u (k+1) := by
      refine ⟨fun j hj ↦ ?_, fun a ha ↦ ?_⟩
      · by_cases eq : j = k
        · subst j; simpa only [u,writeMemory,haddr,ite_true] using hval
        · rw [show u ((p 3).val+j) = m ((p 3).val+j) by simp [u,writeMemory,haddr,eq]]
          exact done.1 j (by omega)
      · have hne : a ≠ (p 3).val+k := by omega
        simp only [u,writeMemory,haddr,ite_eq_right hne]
        exact done.2 _ (by omega)
    obtain ⟨rs,run,stored,len,work,cost⟩ := ih (k := k+1) (m := u) (by omega) step
    let head := report maps p i m
    obtain ⟨call,update,reads,ticks,choices⟩ := native maps p i m
    have next : head.result = some ((k+1 : ℕ) : Word w) := by
      change some ((k : Word w)+1) = _; simp
    have combined : after m (eventLog (head::rs)) = after u (eventLog rs) := by
      change after m (head.events++eventLog rs) = _
      exact (List.foldl_append ..).trans (congrArg (fun s ↦ after s (eventLog rs)) update)
    refine ⟨head::rs,?_,combined ▸ (by simpa only [Nat.add_assoc,Nat.add_comm 1 n] using stored),
      by simp [len],?_,?_⟩
    · rw [List.replicate_succ,runSegment]
      rw [call]
      change (runSegment W.program _ head.result (after m head.events) _).map _ = _
      rw [next,update,run]; rfl
    · intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact ⟨ticks,reads,choices⟩
      · exact work r hr
    · change 1+countProbes head.events+RAMBuckets.cost Report.probes rs = _
      rw [reads,cost]; omega

/-- Exact terminal owner table, source-frame preservation and probe count on
the real fixed instruction sequence. -/
theorem scan_separate (maps : Bool) (p : Fin 4 → Word w) (m : Memory w) (N : ℕ)
    (fits : (p 3).val+N ≤ 2^w)
    (inputs : ∀ i : Word w, i.val<N →
      ((absoluteAddr maps p i).val < (p 3).val ∨ (p 3).val+N ≤ (absoluteAddr maps p i).val) ∧
      ((roleAddr maps p m i).val < (p 3).val ∨ (p 3).val+N ≤ (roleAddr maps p m i).val)) :
    let W := (worker maps).table.instantiate w p
    ∃ rs, runSegment W.program (1+(code maps).length) (some 0) m (List.replicate N []) = some rs ∧
      (∀ i : Fin N, after m (eventLog rs) ((p 3).val+i.val) = m (roleAddr maps p m (i.val : Word w)).val) ∧
      (∀ a, a<(p 3).val ∨ (p 3).val+N≤a → after m (eventLog rs) a = m a) ∧ rs.length=N ∧
      (∀ r ∈ rs, r.events.length=(code maps).length ∧ countProbes r.events=3 ∧ choiceBits r.events=[]) ∧
      RAMBuckets.cost Report.probes rs = 4*N := by
  have start : Written maps p m m 0 := ⟨fun _ hj ↦ (Nat.not_lt_zero _ hj).elim, fun _ _ ↦ rfl⟩
  obtain ⟨rs,run,done,len,work,cost⟩ := scan_from maps p m N fits inputs (n := N) (by omega) start
  simp only [Nat.zero_add] at done
  exact ⟨rs,run,fun i ↦ done.1 _ i.isLt,done.2,len,work,cost⟩

/-- Specialization to an output column above both input tables. -/
theorem scan (maps : Bool) (p : Fin 4 → Word w) (m : Memory w) (N : ℕ)
    (fits : (p 3).val+N ≤ 2^w)
    (inputs : ∀ i : Word w, i.val<N → (absoluteAddr maps p i).val < (p 3).val ∧
      (roleAddr maps p m i).val < (p 3).val) :
    let W := (worker maps).table.instantiate w p
    ∃ rs, runSegment W.program (1+(code maps).length) (some 0) m (List.replicate N []) = some rs ∧
      (∀ i : Fin N, after m (eventLog rs) ((p 3).val+i.val) = m (roleAddr maps p m (i.val : Word w)).val) ∧
      (∀ a, a<(p 3).val ∨ (p 3).val+N≤a → after m (eventLog rs) a = m a) ∧ rs.length=N ∧
      (∀ r ∈ rs, r.events.length=(code maps).length ∧ countProbes r.events=3 ∧ choiceBits r.events=[]) ∧
      RAMBuckets.cost Report.probes rs = 4*N :=
  scan_separate maps p m N fits fun i hi ↦ ⟨Or.inl (inputs i hi).1,Or.inl (inputs i hi).2⟩

/-- The planner receives the incremented cursor after the last row. -/
theorem endState_of_run (maps : Bool) (p : Fin 4 → Word w) (start : Word w)
    (m : Memory w) (N : ℕ) (rs : List (Report w))
    (h : runSegment ((worker maps).table.instantiate w p).program (1+(code maps).length)
      (some start) m (List.replicate N []) = some rs) :
    endState (some start) rs = some (start+(N : Word w)) := by
  induction N generalizing rs m start with
  | zero =>
    change some [] = some rs at h
    rw [← Option.some.inj h]
    simp [endState]
  | succ n ih =>
    rw [List.replicate_succ,runSegment,(native maps p start m).1] at h
    cases eq : runSegment ((worker maps).table.instantiate w p).program (1+(code maps).length)
      (some (start+1)) (after m (report maps p start m).events) (List.replicate n []) with
    | none =>
      change Option.map _ (runSegment _ _ (some (start+1)) _ _) = _ at h
      rw [eq] at h; contradiction
    | some ts =>
      change Option.map _ (runSegment _ _ (some (start+1)) _ _) = _ at h
      rw [eq] at h
      rw [← Option.some.inj h]
      change endState (some (start+1)) ts = _
      simpa [Nat.cast_succ,add_assoc,add_comm,add_left_comm] using ih (start+1) _ ts eq

end CompressorRecords.ResidentOwners

end VPVNP
end Computability
end OAI
