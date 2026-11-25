import OAI.Computability.BorderVNP.RoutingISALoops
import OAI.Computability.BorderVNP.RoutingISABlockAppend

/-! # Checking all incident partners in the native routing program

Each outer iteration skips the local team, runs the supplied check on any other team, and
increments the physical partner register. The forward estimate and the converse below apply to
the same instruction loop, even when a partner's check rejects. -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open VPVNP.BurstRAM

variable {w : ℕ}

/-- Completeness, time, and soundness of the check at one incident partner. -/
structure PartnerCheck (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8) (m : Memory w)
    (teams team cost : ℕ) (c : Code) (Inv : Bank w → Prop) (ok : ℕ → Prop) : Prop where
  /-- A valid block passes within the declared allowance. -/
  complete : ∀ i < teams, i ≠ team → ∀ s, Inv s → (s 11).val = i → ok i →
    ∃ es t, Runs pub macros c s m es t m ∧ traceCost es ≤ cost ∧ Inv t ∧ t 11 = s 11
  /-- A returning block has passed the test on its actual physical input. -/
  sound : ∀ i < teams, i ≠ team → ∀ s, Inv s → (s 11).val = i → ∀ {es t mt},
    Runs pub macros c s m es t mt → mt = m ∧ Inv t ∧ t 11 = s 11 ∧ ok i

/-- The partner counter is independent of the persistent setup registers. -/
structure PartnerRegs (teams team : ℕ) (Inv : Bank w → Prop) : Prop where
  /-- Increment register, local team and total team count. -/
  values : ∀ s, Inv s → (s 1).val = 1 ∧ (s 2).val = team ∧ (s 3).val = teams
  /-- Overwriting the loop counter preserves the persistent setup. -/
  counter : ∀ s, Inv s → ∀ v, Inv (Function.update s 11 v)

/-- The literal outer loop, including the branch which skips the caller. -/
def partnerLoop (other : Code) : Code :=
  .whileLt 11 3 (.seq (.ifEq 11 2 .nop other) (.binary .add 11 11 1))

/-- Recover the actual branch of a register equality test. -/
theorem Runs.splitEq {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {x y : Reg} {a b : Code} {s m es t mt} (r : Runs pub macros (.ifEq x y a b) s m es t mt) :
    ∃ fs, es = tick w :: fs ∧ Runs pub macros (if s x = s y then a else b) s m fs t mt := by
  cases r with
  | atom ha _ _ => cases ha
  | ifEq h => exact ⟨_,rfl,h⟩

variable {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8} {m : Memory w}
  {R u cost : ℕ} {Inv : Bank w → Prop} {ok : ℕ → Prop} {c : Code}

private theorem increment_partner (ctx : PartnerRegs R u Inv) {s : Bank w} (hs : Inv s)
    (hlt : (s 11).val < R) :
    ∃ t, Runs pub macros (.binary .add 11 11 1) s m [tick w] t m ∧ Inv t ∧
      (t 11).val = (s 11).val + 1 := by
  let t := Function.update s 11 (PrivateRAM.BinaryOp.eval .add (s 11) (s 1))
  have hv := ctx.values s hs
  have hR : R < 2^w := hv.2.2 ▸ (s 3).isLt
  refine ⟨t,Runs.localStep m rfl rfl,ctx.counter s hs _,?_⟩
  simp only [t, Function.update_self, PrivateRAM.BinaryOp.eval, Fin.val_add, hv.1]
  exact Nat.mod_eq_of_lt (by omega)

/-- Every valid incident block gives a returning native loop with a linear per-partner budget. -/
theorem partnerLoop_complete (ctx : PartnerRegs R u Inv)
    (check : PartnerCheck pub macros m R u cost c Inv ok)
    (good : ∀ i < R, i ≠ u → ok i) (s : Bank w) (hs : Inv s) (hle : (s 11).val ≤ R) :
    ∃ es t, Runs pub macros (partnerLoop c) s m es t m ∧
      traceCost es ≤ (R-(s 11).val)*(cost+4)+1 ∧ Inv t ∧ (t 11).val = R := by
  have hv := ctx.values s hs
  by_cases hlt : (s 11).val < R
  · have hlt' : s 11 < s 3 := show (s 11).val < (s 3).val by omega
    have branch : ∃ es t, Runs pub macros (.ifEq 11 2 .nop c) s m es t m ∧
        traceCost es ≤ cost+2 ∧ Inv t ∧ t 11 = s 11 := by
      by_cases he : s 11 = s 2
      · have hn : Runs pub macros .nop s m [tick w] s m := Runs.localStep m rfl rfl
        refine ⟨_,s,Runs.ifEq (by simpa [he] using hn),?_,hs,rfl⟩
        change 2 ≤ cost+2
        omega
      · have hu : (s 11).val ≠ u := fun h => he (Fin.ext (h.trans hv.2.1.symm))
        obtain ⟨es,t,r,hb,ht,hc⟩ := check.complete _ hlt hu s hs rfl (good _ hlt hu)
        refine ⟨_,t,Runs.ifEq (by simpa [he] using r),?_,ht,hc⟩
        change 1 + traceCost es ≤ cost+2
        omega
    obtain ⟨bs,v,b,hb,hv',hc⟩ := branch
    obtain ⟨z,r,hz,he⟩ := increment_partner (pub := pub) (macros := macros) (m := m)
      ctx hv' (hc ▸ hlt)
    rw [hc] at he
    obtain ⟨fs,t,rr,hr,ht,ho⟩ := partnerLoop_complete ctx check good z hz (by omega)
    refine ⟨_,t,Runs.whileStep hlt' (b.seq r) rr,?_,ht,ho⟩
    change 1 + traceCost ((bs ++ [tick w]) ++ fs) ≤ _
    simp only [traceCost, VPVNP.RAMBuckets.cost_append] at *
    have hn : R-(s 11).val = R-(z 11).val+1 := by omega
    rw [hn,Nat.add_mul,one_mul]
    change 1 + (_ + 1 + _) ≤ _
    omega
  · exact ⟨_,s,Runs.whileDone (show ¬ (s 11).val < (s 3).val by omega),
      by change 1 ≤ _; omega,hs,by omega⟩
termination_by R-(s 11).val
decreasing_by have := congrArg Fin.val hc; omega

/-- At normal return every incident partner was checked, including the last one. -/
theorem partnerLoop_sound (ctx : PartnerRegs R u Inv)
    (check : PartnerCheck pub macros m R u cost c Inv ok)
    {s : Bank w} (hs : Inv s) (start : (s 11).val = 0) {es t mt}
    (run : Runs pub macros (partnerLoop c) s m es t mt) :
    mt = m ∧ Inv t ∧ (t 11).val = R ∧ ∀ i < R, i ≠ u → ok i := by
  let Acc (z : Bank w) (mz : Memory w) := mz = m ∧ Inv z ∧ (z 11).val ≤ R ∧
    ∀ i < (z 11).val, i ≠ u → ok i
  have step : ∀ {z mz es z' mz'}, Acc z mz → z 11 < z 3 →
      Runs pub macros (.seq (.ifEq 11 2 .nop c) (.binary .add 11 11 1)) z mz es z' mz' →
      Acc z' mz' := by
    rintro z mz bs z' mz' ⟨hm,hi,hmax,hprev⟩ hlt body
    subst mz
    have hv := ctx.values z hi
    have hj : (z 11).val < R := hv.2.2 ▸ hlt
    obtain ⟨v,mv,a,b,_,r₁,r₂⟩ := Runs.seq_iff.mp body
    obtain ⟨fs,_,branch⟩ := r₁.splitEq
    have done : mv = m ∧ Inv v ∧ v 11 = z 11 ∧ ((z 11).val ≠ u → ok (z 11).val) := by
      by_cases he : z 11 = z 2
      · rw [ite_eq_left he] at branch
        have hn : Runs pub macros .nop z m [tick w] z m := Runs.localStep m rfl rfl
        obtain ⟨_,hv₁,hm₁⟩ := branch.unique_of_deterministic rfl hn
        subst v
        subst mv
        exact ⟨rfl,hi,rfl,fun h => (h ((congrArg Fin.val he).trans hv.2.1)).elim⟩
      · rw [ite_eq_right he] at branch
        have hu : (z 11).val ≠ u := fun h => he (Fin.ext (h.trans hv.2.1.symm))
        obtain ⟨hm,ht,hc,hok⟩ := check.sound _ hj hu z hi rfl branch
        exact ⟨hm,ht,hc,fun _ => hok⟩
    obtain ⟨hmv,ht,hc,hok⟩ := done
    subst mv
    obtain ⟨v',inc,hv',hnext⟩ := increment_partner (pub := pub) (macros := macros) (m := m)
      ctx ht (hc ▸ hj)
    obtain ⟨_,hz',hmz'⟩ := r₂.unique_of_deterministic rfl inc
    subst z'
    subst mz'
    rw [hc] at hnext
    refine ⟨rfl,hv',by omega,?_⟩
    intro i hil hu
    by_cases he : i = (z 11).val
    · subst i; exact hok hu
    · exact hprev i (by omega) hu
  obtain ⟨⟨hm,hv,hmax,all⟩,exit⟩ := run.while_invariant 11 3 _ Acc step rfl
    ⟨rfl,hs,by omega,by simp [start]⟩
  have hr := (ctx.values t hv).2.2
  have hn : (t 11).val = R := by change ¬ (t 11).val < (t 3).val at exit; omega
  exact ⟨hm,hv,hn,hn ▸ all⟩

end RoutingISA

end BorderVNP
end Computability
end OAI
