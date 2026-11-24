import OAI.Computability.VPVNP.PrimedStackRAMLeafVisit

/-!
# Internal visits of the primed counter

The range guards precede the counter update. An accepted internal choice
adds the dense binary production once and pushes the ordered children on
the external stack. All marks and all assembled input bits remain available.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedStackRAM

open BurstRAM PrimedCounter ParseGrammar
open scoped Fin.CommRing Classical

variable {base R n m H w : ℕ} {x : Fin 2 → Fin R → Fin m → Bool}
variable {st : VisitState n m H} {mem : Memory w}

private theorem push_holds (hr : Holds base x st mem) (state : Word w) (regs : Regs w 16)
    (d : Fin n) (h : Fin H) (hd : regs 0 = (d.val : Word w)) (hh : regs 1 = (h.val : Word w))
    (hf : base + size R n m (labelCount n m H) ≤ 2^w) (hc : st.pending.length < n) :
    ∃ es rs m', trace (publicData w base R n m H) state push regs mem = some (es,rs,m') ∧
      Holds base x {st with pending := (d,h)::st.pending} m' ∧ countProbes es = 4 := by
  have hlen : (frames w st.pending).length < n := by simpa [frames] using hc
  obtain ⟨es,rs,m',ht,hp,hs⟩ := push_rep state regs hr.pending hf hlen
  rw [hd,hh] at hs
  exact ⟨es,rs,m',ht,hr.withStack _ (push_data hr.pending hf hlen ht) hs,hp⟩

private theorem pushChildren_holds (hr : Holds base x st mem) (state : Word w) (regs : Regs w 16)
    (d : Fin n) (b : Fin d.val) (i j : Fin H) (hd : (regs 0).val = d.val)
    (hb : (regs 2).val = b.val) (hi : (regs 3).val = i.val) (hj : (regs 4).val = j.val)
    (hf : base + size R n m (labelCount n m H) ≤ 2^w) (hH : H < 2^w)
    (hcap : st.pending.length + 2 ≤ n) :
    ∃ es rs m', trace (publicData w base R n m H) state pushChildren regs mem = some (es,rs,m') ∧
      Holds base x {st with pending := (leftDegree d b,i)::(rightDegree d b,j)::st.pending} m' ∧
      countProbes es = 8 := by
  let pub := publicData w base R n m H
  have hB : regs 2 < regs 0 := by change (regs 2).val < (regs 0).val; simp [hb,hd]
  have hI : regs 3 < pub 7 := by
    change (regs 3).val < (H : Word w).val
    simp [hi,Fin.val_natCast,Nat.mod_eq_of_lt hH]
  have hJ : regs 4 < pub 7 := by
    change (regs 4).val < (H : Word w).val
    simp [hj,Fin.val_natCast,Nat.mod_eq_of_lt hH]
  obtain ⟨es₀,rs₀,h₀,p₀,_,hd₀,hs₀⟩ := rightFrame_spec pub state regs mem hB hI hJ
  have hdRight : rs₀ 0 = ((rightDegree d b).val : Word w) := by
    rw [hd₀, ← (child_degrees d b _ _ hd hb).2, Fin.cast_val_eq_self]
  have hhRight : rs₀ 1 = (j.val : Word w) := by rw [hs₀, ← hj, Fin.cast_val_eq_self]
  obtain ⟨es₁,rs₁,m₁,h₁,hr₁,p₁⟩ := push_holds hr state rs₀ (rightDegree d b) j hdRight hhRight hf (by omega)
  obtain ⟨es₂,rs₂,h₂,p₂,_,hd₂,hs₂⟩ := leftFrame_spec pub state rs₁ m₁
  have same (u : Fin 16) (hu : u = 2 ∨ u = 3) : rs₁ u = regs u := by
    have hu₁ : ∀ op ∈ push, op.destination ≠ some u := by rcases hu with rfl | rfl <;> decide
    have hu₀ : ∀ op ∈ rightFrame, op.destination ≠ some u := by rcases hu with rfl | rfl <;> decide
    exact (trace_preserves hu₁ h₁).trans (trace_preserves hu₀ h₀)
  have hdLeft : rs₂ 0 = ((leftDegree d b).val : Word w) := by
    rw [hd₂, same 2 (Or.inl rfl), ← (child_degrees d b _ _ hd hb).1, Fin.cast_val_eq_self]
  have hhLeft : rs₂ 1 = (i.val : Word w) := by rw [hs₂, same 3 (Or.inr rfl), ← hi, Fin.cast_val_eq_self]
  obtain ⟨es₃,rs₃,m₃,h₃,hr₃,p₃⟩ := push_holds hr₁ state rs₂ (leftDegree d b) i hdLeft hhLeft hf (by simp; omega)
  refine ⟨es₀ ++ (es₁ ++ (es₂ ++ es₃)),rs₃,m₃,?_,hr₃,?_⟩
  · change trace pub state pushChildren regs mem = _
    rw [pushChildren, trace_append, h₀]
    simp only [Option.bind_some]
    rw [trace_append, h₁]
    simp only [Option.bind_some]
    rw [trace_append, h₂]
    simp only [Option.bind_some]
    rw [h₃]
    rfl
  · simp [probes_append,p₀,p₁,p₂,p₃]

theorem binaryLines_valid (hr : Holds base x st mem) (state : Word w) (regs : Regs w 16)
    (d : Fin n) (b : Fin d.val) (h i j : Fin H) (hd : (regs 0).val = d.val)
    (hh : regs 1 = (h.val : Word w)) (hb : (regs 2).val = b.val)
    (hi : (regs 3).val = i.val) (hj : (regs 4).val = j.val)
    (hf : base + size R n m (labelCount n m H) ≤ 2^w) (hH : H < 2^w) (hw : 2 < 2^w)
    (hprod : (d.val-1)*d.val < 2^w) (hcap : st.pending.length + 2 ≤ n)
    (hcount : st.counts (.inr ⟨d,h,b,i,j⟩) + 1 < 2^w) :
    let a : Label n m (Fin H) := .inr ⟨d,h,b,i,j⟩
    ∃ es rs m', trace (publicData w base R n m H) state binaryLines regs mem = some (es,rs,m') ∧
      Holds base x ⟨(leftDegree d b,i)::(rightDegree d b,j)::st.pending, st.marked,
        st.counts + Finsupp.single a 1⟩ m' ∧ countProbes es = 10 := by
  let pub := publicData w base R n m H
  let a : Label n m (Fin H) := .inr ⟨d,h,b,i,j⟩
  let ix := labelIndex n m H a
  have hB : regs 2 < regs 0 := by change (regs 2).val < (regs 0).val; simp [hb,hd]
  have hI : regs 3 < pub 7 := by
    change (regs 3).val < (H : Word w).val
    simp [hi,Fin.val_natCast,Nat.mod_eq_of_lt hH]
  have hJ : regs 4 < pub 7 := by
    change (regs 4).val < (H : Word w).val
    simp [hj,Fin.val_natCast,Nat.mod_eq_of_lt hH]
  have ht₀ : trace pub state binaryChecks regs mem = some (List.replicate 4 .tick, Function.update regs 11 (pub 7), mem) := by
    simp (config := {decide := true}) [binaryChecks,trace,Op.effect,Function.update,hB,hI,hJ]
  let rs₀ := Function.update regs 11 (pub 7)
  have same₀ (u : Fin 16) (hu : u < 5) : rs₀ u = regs u := Function.update_of_ne (by omega) _ _
  have hT : labelCount n m H ≤ 2^w := by unfold size at hf; omega
  obtain ⟨es₁,rs₁,ht₁,hc₁,_,he₁⟩ := binaryIndex_spec pub state rs₀ mem d b h i j rfl rfl
    ((congrArg Fin.val (same₀ 0 (by decide))).trans hd) ((same₀ 1 (by decide)).trans hh)
    (by rw [same₀ 2 (by decide), ← hb, Fin.cast_val_eq_self])
    (by rw [same₀ 3 (by decide), ← hi, Fin.cast_val_eq_self])
    (by rw [same₀ 4 (by decide), ← hj, Fin.cast_val_eq_self]) hw hprod hT
  have hv : rs₁ 7 = (ix.val : Word w) := by change rs₁ 7 = (↑((labelIndex n m H _).val) : Word w); rw [← he₁, Fin.cast_val_eq_self]
  obtain ⟨es₂,rs₂,ht₂,hc₂⟩ := increment_cell mem state rs₁ ix hv hf ((hr.counts a) ▸ hcount)
  have hr₂ := hr.increment a hf hcount
  have same₂ (u : Fin 16) (hu : u < 5) : rs₂ u = regs u := by
    have ha : ∀ op ∈ increment, op.destination ≠ some u := by
      fin_cases u <;> first | decide | contradiction
    have hb' : ∀ op ∈ binaryIndex, op.destination ≠ some u := by
      fin_cases u <;> first | decide | contradiction
    exact (trace_preserves ha ht₂).trans ((trace_preserves hb' ht₁).trans (same₀ u hu))
  obtain ⟨es₃,rs₃,m₃,ht₃,hr₃,hc₃⟩ := pushChildren_holds hr₂ state rs₂ d b i j
    ((congrArg Fin.val (same₂ 0 (by decide))).trans hd)
    ((congrArg Fin.val (same₂ 2 (by decide))).trans hb)
    ((congrArg Fin.val (same₂ 3 (by decide))).trans hi)
    ((congrArg Fin.val (same₂ 4 (by decide))).trans hj) hf hH hcap
  refine ⟨((List.replicate 4 .tick ++ es₁) ++ es₂) ++ es₃,rs₃,m₃,?_,hr₃,?_⟩
  · change trace pub state binaryLines regs mem = _
    simp [binaryLines, trace_append, ht₀, ht₁, ht₂, rs₀, pub]
    exact ht₃
  · simp [probes_append,hc₁,hc₂,hc₃,countProbes]

theorem binaryLines_reject (pub : Fin 11 → Word w) (state : Word w) (regs : Regs w 16) (m' : Memory w)
    (bad : ¬regs 2 < regs 0 ∨ ¬regs 3 < pub 7 ∨ ¬regs 4 < pub 7) :
    trace pub state binaryLines regs m' = none := by
  have hguard : trace pub state binaryChecks regs m' = none := by
    by_cases hb : regs 2 < regs 0
    · by_cases hi : regs 3 < pub 7
      · have hj := (bad.resolve_left (not_not_intro hb)).resolve_left (not_not_intro hi)
        simp (config := { decide := true }) [binaryChecks, trace, Op.effect, Function.update, hb, hi, hj]
      · simp (config := { decide := true }) [binaryChecks, trace, Op.effect, Function.update, hb, hi]
    · simp [binaryChecks, trace, Op.effect, hb]
  rw [binaryLines, trace_append, trace_append, trace_append, hguard]
  rfl

end PrimedStackRAM

end VPVNP
end Computability
end OAI
