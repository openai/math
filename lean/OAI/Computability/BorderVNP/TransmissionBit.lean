import OAI.Computability.BorderVNP.TransmissionISA
import OAI.Computability.BorderVNP.DiagonalResidueRAMSteps
import OAI.Computability.BorderVNP.RoutingISANatural

/-! # Actual word reads and writes for each transmission bit -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Transmission

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM
open DiagonalResidueRAM (effect effect_runs)

variable {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)

/-- Addressed update at the current offset within a destination interval. -/
def write (s : Bank w) (m : Memory w) (dest : Reg) (bit : Word w) : Memory w :=
  Function.update m (s dest + s 16).val bit

/-- One returning bit handler preserves all the per-range directory and loop registers. -/
def sameRange (s t : Bank w) : Prop := ∀ i : Reg, i.val ≤ 16 → t i = s i

/-- Chronological trace costs add under sequential composition. -/
theorem cost_append (es fs : List (TeamRAM.Event w)) :
    traceCost (es ++ fs) = traceCost es + traceCost fs := VPVNP.RAMBuckets.cost_append ..

/-- The local shared branch makes exactly one binary choice, and its two stores use the
same chosen word. This also handles coinciding destination addresses. -/
theorem localShared_runs (s : Bank w) (m : Memory w) (b : Bool) :
    let v := if b then s 1 else s 2
    ∃ es t, Runs pub macros localShared s m es t (write s (write s m 13 v) 14 v) ∧
      traceCost es = 6 ∧ es.flatMap TeamRAM.Event.choices = [b] ∧ sameRange s t := by
  let z := effect b s m localShared
  have run := effect_runs pub macros b s m localShared (by decide)
  refine ⟨z.trace, z.bank, ?_, ?_, ?_, ?_⟩
  · cases b <;> simpa [z, localShared, writeBit, write, Code.block, effect, BinaryOp.eval,
      Function.update] using run
  · cases b <;> rfl
  · cases b <;> rfl
  · intro i hi
    have h17 : i ≠ 17 := by intro e; subst i; omega
    have h19 : i ≠ 19 := by intro e; subst i; omega
    cases b <;> simp [z, localShared, writeBit, Code.block, effect, h17, h19]

/-- A local delivery copies the real source bit at the current offset, and consumes no
private choices. -/
theorem localData_runs (s : Bank w) (m : Memory w) :
    ∃ es t, Runs pub macros localData s m es t (write s m 14 (m (s 12 + s 16).val)) ∧
      traceCost es = 4 ∧ es.flatMap TeamRAM.Event.choices = [] ∧ sameRange s t := by
  let z := effect false s m localData
  have run := effect_runs pub macros false s m localData (by decide)
  refine ⟨z.trace, z.bank, ?_, rfl, rfl, ?_⟩
  · simpa [z, localData, sourceBit, writeBit, write, Code.block, effect, BinaryOp.eval,
      Function.update] using run
  · intro i hi
    have h17 : i ≠ 17 := by intro e; subst i; omega
    have h19 : i ≠ 19 := by intro e; subst i; omega
    simp [z, localData, sourceBit, writeBit, effect, h17, h19]

/-- Extract the native address computed by the read-only endpoint code. -/
def endpointNat (peer : Reg) (pub : Arg → Word w) (s : Bank w) (m : Memory w) : ℕ :=
  (endpoint peer).evalNat (readings pub) (readings m) (readings s) 48

/-- The recipient loads the actual physical word at the endpoint address and copies it
to the offset inside its own destination. -/
theorem receive_runs (peer dest : Reg) (hd : dest.val ≤ 16) (s : Bank w) (m : Memory w)
    (safe : (endpoint peer).safeReadOnly w (readings pub) (readings m) (readings s)) :
    ∃ es t, Runs pub macros (receive peer dest) s m es t
        (write s m dest (m (endpointNat peer pub s m))) ∧
      traceCost es ≤ (endpoint peer).slots + 3 ∧ sameRange s t := by
  obtain ⟨es,a,ra,cost,values⟩ := (endpoint peer).runReadOnly pub macros m s safe
  have low : sameRange s a := by
    intro i hi
    apply Fin.ext
    exact (congrFun values i).trans ((endpoint peer).evalNat_protected _ _ _
      (lo := 30) (by rfl) i (by omega))
  have at48 : (a 48).val = endpointNat peer pub s m := congrFun values 48
  let tail : Code := .seq (.load 19 48) (writeBit dest)
  let z := effect false a m tail
  have rr := effect_runs pub macros false a m tail (by
    simp only [tail, writeBit, DiagonalResidueRAM.straight, Bool.true_and]; rfl)
  have hm : z.mem = write s m dest (m (endpointNat peer pub s m)) := by
    have hdest : dest ≠ 19 := by intro he; subst dest; omega
    simp only [z, tail, writeBit, effect, Function.update, BinaryOp.eval, write]
    simp [hdest, at48, low dest hd, low 16 (by decide)]
  refine ⟨es ++ z.trace,z.bank,hm ▸ Runs.seq ra rr,?_,?_⟩
  · rw [cost_append]
    exact Nat.add_le_add_right cost 3
  · intro i hi
    have h17 : i ≠ 17 := by intro e; subst i; omega
    have h19 : i ≠ 19 := by intro e; subst i; omega
    simpa [z, tail, writeBit, effect, h17, h19] using low i hi

/-- A remote data origin can return exactly when the link bit equals the word at the
actual source address. No write is made by the sender. -/
theorem send_runs_iff (s : Bank w) (m : Memory w)
    (safe : (endpoint 10).safeReadOnly w (readings pub) (readings m) (readings s)) :
    (∃ es t, Runs pub macros send s m es t m) ↔
      m (s 12 + s 16).val = m (endpointNat 10 pub s m) := by
  obtain ⟨es,a,ra,_,values⟩ := (endpoint 10).runReadOnly pub macros m s safe
  have low : sameRange s a := by
    intro i hi
    apply Fin.ext
    exact (congrFun values i).trans ((endpoint 10).evalNat_protected _ _ _
      (lo := 30) (by decide) i (by omega))
  have at48 : (a 48).val = endpointNat 10 pub s m := congrFun values 48
  let l := Function.update a 20 (m (a 48).val)
  let f := effect false l m sourceBit
  have r₁ := Runs.load pub macros 20 48 a m
  have r₂ := effect_runs pub macros false l m sourceBit (by decide)
  have v₁ : f.bank 19 = m (s 12 + s 16).val := by
    simp [f,l,sourceBit,effect,BinaryOp.eval, low 12 (by decide),low 16 (by decide)]
  have v₂ : f.bank 20 = m (endpointNat 10 pub s m) := by simp [f,l,sourceBit,effect,at48]
  constructor
  · rintro ⟨_,_,h⟩
    suffices weak : ∀ {es t mt}, Runs pub macros send s m es t mt →
        m (s 12+s 16).val = m (endpointNat 10 pub s m) from weak h
    intro es t mt h
    change Runs _ _ (.seq (endpoint 10) (.seq (.load 20 48)
      (.seq sourceBit (.ifEq 19 20 .nop .reject)))) _ _ _ _ _ at h
    cases h with
    | atom hc => cases hc
    | seq raddr tail =>
      obtain ⟨_, rfl, rfl⟩ := ra.unique_of_deterministic (by decide) raddr
      cases tail with
      | atom hc => cases hc
      | seq rload tail =>
        obtain ⟨_, he, hm⟩ := r₁.unique_of_deterministic (by decide) rload
        rw [← he, ← hm] at tail
        change Runs _ _ (.seq sourceBit (.ifEq 19 20 .nop .reject)) l m _ _ _ at tail
        cases tail with
        | atom hc => cases hc
        | seq rsrc chk =>
          obtain ⟨_, hbank, hmem⟩ := r₂.unique_of_deterministic (by decide) rsrc
          rw [← hbank, ← hmem] at chk
          by_contra hd
          have hn : f.bank 19 ≠ f.bank 20 := by simpa only [v₁,v₂] using hd
          cases chk with
          | atom hc => cases hc
          | ifEq hr =>
            change Runs _ _ (if f.bank 19 = f.bank 20 then .nop else .reject) _ _ _ _ _ at hr
            rw [ite_eq_right hn] at hr
            cases hr with | atom hc => cases hc
  · intro h
    have same : f.bank 19 = f.bank 20 := v₁.trans (h.trans v₂.symm)
    have chk : Runs pub macros (.ifEq 19 20 .nop .reject) f.bank f.mem
        [tick w,tick w] f.bank f.mem :=
      .ifEq (by rw [ite_eq_left same]; exact Runs.localStep _ rfl rfl)
    exact ⟨_,_,Runs.seq ra (.seq r₁ (.seq r₂ chk))⟩

end RoutingISA.Transmission

end BorderVNP
end Computability
end OAI
