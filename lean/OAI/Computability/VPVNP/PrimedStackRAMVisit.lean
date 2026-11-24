import OAI.Computability.VPVNP.PrimedStackRAMChoices

/-!
# The native preorder visit agrees with the grammar traversal

The complete opcode execution rejects exactly the branch strings rejected by
the mathematical visit. When it succeeds, its external memory represents
the prescribed next pending stack, mark set and common production histogram.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedStackRAM

open BurstRAM PrimedCounter ParseGrammar
open scoped Fin.CommRing Classical

variable {base R n m H w : ℕ} {x : Fin 2 → Fin R → Fin m → Bool}
variable {st : VisitState n m H} {mem : Memory w}

/-- Agreement between a grammar visit and a native node execution. They reject together, or the
final memory represents the resulting visit state, the choice stream is exhausted, and the
trace uses at most fourteen probes. -/
inductive Agreement (base : ℕ) (x : Fin 2 → Fin R → Fin m → Bool) :
    Option (VisitState n m H) → Option (Output w 16) → Prop
  | reject : Agreement base x none none
  | accept {st' o} (holds : Holds base x st' o.mem) (bits : o.bits = [])
      (probes : countProbes o.events ≤ 14) : Agreement base x (some st') (some o)

private noncomputable def abstractChoice (x₀ : Fin m → Bool) (st₀ : VisitState n m H) (d : Fin n) (h : Fin H)
    (c : RawChoice w) : Option (VisitState n m H) := do
  let t ← c.token d.val m H
  let (a, children) ← step x₀ (d,h) t
  let marked ← markToken st₀.marked t
  return ⟨children ++ st₀.pending,marked,st₀.counts + Finsupp.single a 1⟩

private def physicalChoice (pub : Fin 11 → Word w) (state : Word w) (rs : Regs w 16)
    (m₀ : Memory w) (popEvents : List (Event w)) (c : RawChoice w) : Option (Output w 16) :=
  (trace pub state c.lines (choiceRegs rs c) m₀).map fun (es,rs',m') =>
    ⟨popEvents ++ (.tick :: (c.events ++ es)),rs',m',[]⟩

private theorem terminal_step (xx : Fin m → Bool) (d : Fin n) (h : Fin H) (j : Fin m)
    (hd : d.val = 0) : step xx (d,h) (.terminal j) = some (.inl (h,j,xx j),[]) := by
  rcases d with ⟨k,hk⟩
  change k = 0 at hd
  subst k
  rfl

private theorem binary_step (xx : Fin m → Bool) (d : Fin n) (b : Fin d.val) (h i j : Fin H) :
    step xx (d,h) (.binary b.val i j) = some (.inr ⟨d,h,b,i,j⟩,[(leftDegree d b,i),(rightDegree d b,j)]) := by
  rcases d with ⟨k,hk⟩
  cases k with
  | zero => exact Fin.elim0 b
  | succ k => simp [step,b.isLt]

private theorem choice_agreement (hr : Holds base x st mem) (g : Fin 2) (s : Fin R)
    (d : Fin n) (h : Fin H) (state : Word w) (rs : Regs w 16) (es₀ : List (Event w))
    (hp : countProbes es₀ = 4) (hr₀ : (rs 0).val = d.val) (hr₁ : rs 1 = (h.val : Word w))
    (hr₅ : rs 5 = (↑((g.val*R+s.val)*m) : Word w)) (c : RawChoice w) (hc : c.isLeaf = decide (d.val = 0))
    (hf : base + size R n m (labelCount n m H) ≤ 2^w) (hH : H < 2^w) (hw : 2 < 2^w)
    (hprod : (d.val-1)*d.val < 2^w) (hcap : 0 < d.val → st.pending.length+2 ≤ n)
    (hcounts : ∀ a, st.counts a + 1 < 2^w) :
    Agreement base x (abstractChoice (x g s) st d h c)
      (physicalChoice (publicData w base R n m H) state rs mem es₀ c) := by
  let pub := publicData w base R n m H
  cases c with
  | leaf v =>
    have hd : d.val = 0 := by simpa [RawChoice.isLeaf] using hc.symm
    let rg := choiceRegs rs (.leaf v)
    have hg : rg 2 = v ∧ rg 1 = rs 1 ∧ rg 5 = rs 5 := by
      simp (config := {decide := true}) [rg,choiceRegs,setGuess,guessRegs,GuessWord.resultRegs,Function.update]
    by_cases hv : v.val < m
    · let j : Fin m := ⟨v.val,hv⟩
      have hrj : rg 2 = (j.val : Word w) := hg.1.trans (Fin.cast_val_eq_self v).symm
      by_cases hused : j ∈ st.marked
      · have ht := leafLines_repeated hr state rg j hrj hused hf hw
        have hs := terminal_step (x g s) d h j hd
        change Agreement base x _ ((trace pub state leafLines rg mem).map _)
        rw [ht]
        simp [abstractChoice,RawChoice.token,hv,hs,markToken,j] at hused ⊢
        simp [hused,Agreement.reject]
      · obtain ⟨es,rg',m',ht,hst,hpr⟩ := leafLines_valid hr g s state rg h j (hg.2.1.trans hr₁) hrj
          (hg.2.2.trans hr₅) hused hf hw (hcounts _)
        have hs := terminal_step (x g s) d h j hd
        change Agreement base x _ ((trace pub state leafLines rg mem).map _)
        rw [ht]
        change Agreement base x (abstractChoice (x g s) st d h (.leaf v)) (some _)
        have ha : abstractChoice (x g s) st d h (.leaf v) = some
            ⟨st.pending,insert j st.marked,st.counts + Finsupp.single (.inl (h,j,x g s j)) 1⟩ := by
          simp only [abstractChoice,RawChoice.token,hv,dite_true,bind,Option.bind_some]
          rw [hs]
          have hused' : (⟨v.val,hv⟩ : Fin m) ∉ st.marked := hused
          simp [markToken,hused',j]
        rw [ha]
        exact .accept hst rfl (by simp [probes_append,countProbes,hp,RawChoice.no_probes,hpr])
    · have ht := leafLines_outside (R := R) (n := n) (H := H) state rg (mem := mem) hf
        (by rw [hg.1]; omega)
      change Agreement base x _ ((trace pub state leafLines rg mem).map _)
      rw [ht]
      simpa [abstractChoice, RawChoice.token, hv] using (Agreement.reject (base := base) (x := x) (w := w) (H := H) (n := n))
  | binary b i j =>
    let rg := choiceRegs rs (.binary b i j)
    have hg : rg 0 = rs 0 ∧ rg 1 = rs 1 ∧ rg 2 = b ∧ rg 3 = i ∧ rg 4 = j := by
      simp (config := {decide := true}) [rg,choiceRegs,setGuess,guessRegs,GuessWord.resultRegs,Function.update]
    have hpub : (pub 7).val = H := (Fin.val_natCast H (2^w)).trans (Nat.mod_eq_of_lt hH)
    by_cases hv : b.val < d.val ∧ i.val < H ∧ j.val < H
    · let b' : Fin d.val := ⟨b.val,hv.1⟩
      let i' : Fin H := ⟨i.val,hv.2.1⟩
      let j' : Fin H := ⟨j.val,hv.2.2⟩
      have hsz : 0 < d.val := by have := b'.isLt; omega
      obtain ⟨es,rg',m',ht,hst,hpr⟩ := binaryLines_valid hr state rg d b' h i' j'
        ((congrArg Fin.val hg.1).trans hr₀) (hg.2.1.trans hr₁) (congrArg Fin.val hg.2.2.1)
        (congrArg Fin.val hg.2.2.2.1) (congrArg Fin.val hg.2.2.2.2) hf hH hw hprod (hcap hsz) (hcounts _)
      have hs := binary_step (x g s) d b' h i' j'
      change Agreement base x _ ((trace pub state binaryLines rg mem).map _)
      rw [ht]
      have ha : abstractChoice (x g s) st d h (.binary b i j) = some
          ⟨(leftDegree d b',i') :: (rightDegree d b',j') :: st.pending, st.marked,
            st.counts + Finsupp.single (.inr ⟨d,h,b',i',j'⟩) 1⟩ := by
        simp only [abstractChoice,RawChoice.token,hv.1,hv.2.1,hv.2.2,dite_true,ite_true,bind,Option.bind_some]
        rw [hs]
        rfl
      rw [ha]
      exact .accept hst rfl (by simp [probes_append,countProbes,hp,RawChoice.no_probes,hpr])
    · have hbad : ¬rg 2 < rg 0 ∨ ¬rg 3 < pub 7 ∨ ¬rg 4 < pub 7 := by
        change ¬(rg 2).val < (rg 0).val ∨ ¬(rg 3).val < (pub 7).val ∨ ¬(rg 4).val < (pub 7).val
        rw [hg.1,hg.2.2.1,hg.2.2.2.1,hg.2.2.2.2,hpub,hr₀]
        tauto
      have ht := binaryLines_reject pub state rg mem hbad
      change Agreement base x _ ((trace pub state binaryLines rg mem).map _)
      rw [ht]
      have ha : abstractChoice (x g s) st d h (.binary b i j) = none := by
        by_cases hb : b.val < d.val <;> by_cases hi : i.val < H <;> by_cases hj : j.val < H <;>
          simp_all [abstractChoice, RawChoice.token]
      rw [ha]
      exact .reject

private theorem length_le_leafMass (stack : List (Frame n (Fin H))) : stack.length ≤ leafMass stack := by
  induction stack with
  | nil => rfl
  | cons f stack ih => change stack.length+1 ≤ f.1.val+1+leafMass stack; omega

/-- Complete correctness at a single scheduled node, including malformed
and truncated bitstrings, repeated locations and exact post-memory. -/
theorem completeNode_visit (hr : Holds base x st mem) (g : Fin 2) (s : Fin R) (state : Word w)
    (regs : Regs w 16) (bits : List Bool) (hrow : regs 5 = (↑((g.val*R+s.val)*m) : Word w))
    (hf : base + size R n m (labelCount n m H) ≤ 2^w) (hH : H < 2^w) (hw : 2 < 2^w)
    (hprod : n*n ≤ 2^w) (hmass : leafMass st.pending ≤ n) (hcounts : ∀ a, st.counts a + 1 < 2^w) :
    Agreement base x (visit w (x g s) st bits)
      (completeNode (publicData w base R n m H) state regs mem bits) := by
  let pub := publicData w base R n m H
  cases hp : st.pending with
  | nil =>
    have ht := pop_holds_empty hr hp hf state regs
    simpa [visit,hp,completeNode,nodeKernel,seqKernel,lineKernel,ht] using
      (Agreement.reject (base := base) (x := x) (w := w) (H := H) (n := n))
  | cons f tail =>
    obtain ⟨d,h⟩ := f
    obtain ⟨es₀,r₀,m₀,ht,hr',hd,hh,hrow',hz,hprobes⟩ := pop_holds hr hp hf state regs
    have hdw : (r₀ 0).val = d.val := by
      rw [hd, Fin.val_natCast, Nat.mod_eq_of_lt (d.isLt.trans (capacity_fit base hf))]
    have he : (r₀ 0 = r₀ 12) ↔ d.val = 0 := by simp [Fin.ext_iff,hz,hdw]
    rw [completeNode_pop pub state regs r₀ mem m₀ es₀ bits ht, decide_eq_decide.mpr he]
    cases hc : exactChoice w (decide (d.val=0)) bits with
    | none =>
      simpa [visit,hp,readToken_eq_choice,hc] using
        (Agreement.reject (base := base) (x := x) (w := w) (H := H) (n := n))
    | some c =>
      have hcap (hs : 0 < d.val) : tail.length+2 ≤ n := by
        rw [hp] at hmass
        change d.val + 1 + leafMass tail ≤ n at hmass
        have := length_le_leafMass tail
        omega
      have htri : (d.val - 1)*d.val < 2^w := by
        exact ((Nat.mul_le_mul_right _ (Nat.sub_le d.val 1)).trans_lt
          (Nat.mul_self_lt_mul_self d.isLt)).trans_le hprod
      have ha := choice_agreement hr' g s d h state r₀ es₀ hprobes hdw hh (hrow'.trans hrow) c
        (exactChoice_kind w (decide (d.val = 0)) bits c hc) hf hH hw htri hcap hcounts
      simpa only [visit,hp,readToken_eq_choice,hc,bind,Option.bind_some,abstractChoice,physicalChoice,
        Option.bind_assoc] using ha

end PrimedStackRAM

end VPVNP
end Computability
end OAI
