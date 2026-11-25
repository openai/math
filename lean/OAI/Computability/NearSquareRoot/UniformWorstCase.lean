import OAI.Computability.NearSquareRoot.Specification
import OAI.Computability.NearSquareRoot.Asymptotic
import OAI.Computability.NearSquareRoot.VisitedCells

/-! # Literal worst-case formulation of the uniform multiplication theorem

For positive input lengths the worst-case time is attained by a pair of
binary strings. The excess exponent is one function tending to zero, with
leading coefficient one in the eventual time inequality. Both input strings
may begin with zero. The machine, its input and output conventions, and its
space coefficient are fixed before the length of the strings is chosen.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

open IntegerMultiplication Filter
open scoped Topology

/-- The set of actual halting times on pairs of width `n`. The initializer
fixes the input tape and its finite alphabet before any length is chosen. -/
def haltingTimes {A Q I : Type} (m : TM.Rule A Q I)
    (load : List Bool → List Bool → TM.Config A Q I) (n : ℕ) : Set ℕ :=
  {t | ∃ x y, x.length = n ∧ y.length = n ∧ ∃ c,
    Trace (TM.advance m) (load x y) t c ∧ TM.advance m c = none}

/-- An actual maximum over the deterministic halting lengths; `T` need
only be an upper bound. The maximum is computed before choosing an exponent. -/
private theorem attained {E : ℕ → Set ℕ} {T : ℕ → ℕ}
    (someTime : ∀ n, 0 < n → (E n).Nonempty)
    (bound : ∀ n, 0 < n → ∀ t ∈ E n, t ≤ T n) :
    ∃ W : ℕ → ℕ, (∀ n, W n ≤ T n) ∧ ∀ n, 0 < n → IsGreatest (E n) (W n) := by
  classical
  let L n := (Finset.range (T n+1)).filter (fun t => t ∈ E n)
  let W n := if h : (L n).Nonempty then (L n).max' h else 0
  have mem {t n : ℕ} (hn : 0 < n) : t ∈ L n ↔ t ∈ E n := by
    simp only [L,Finset.mem_filter,Finset.mem_range]
    exact ⟨And.right,fun ht => ⟨Nat.lt_succ_of_le (bound n hn t ht),ht⟩⟩
  have top {n : ℕ} (hn : 0 < n) : IsGreatest (E n) (W n) := by
    obtain ⟨t,ht⟩ := someTime n hn
    have pos : (L n).Nonempty := ⟨t,(mem hn).2 ht⟩
    simp only [W,pos,↓reduceDIte]
    exact ⟨(mem hn).1 (Finset.max'_mem _ _),fun t ht => Finset.le_max' _ _ ((mem hn).2 ht)⟩
  refine ⟨W,?_,fun _ hn => top hn⟩
  intro n
  by_cases h : (L n).Nonempty
  · have m := Finset.max'_mem (L n) h
    simp only [L,Finset.mem_filter,Finset.mem_range] at m
    simp only [W,h,↓reduceDIte]
    exact Nat.le_of_lt_succ m.1
  · simp [W,h]

/-- Manuscript form of `thm:uniform-main`. The same finite machine realizes
both the complete product specification and the attained worst-case bound. -/
def UniformWorstCaseSpec : Prop :=
  ∃ (A Q I : Type) (_ : Finite A) (_ : Finite Q) (_ : Finite I)
    (bit : Bool → A) (sep blank : A) (inp out : I) (start : Q)
    (m : TM.Rule A Q I) (W : ℕ → ℕ) (S : ℕ),
    Function.Injective bit ∧ (∀ b, bit b ≠ sep ∧ bit b ≠ blank) ∧ sep ≠ blank ∧
    (∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, (W n : ℝ) ≤ n*(1+Real.log n)^((1 : ℝ) / (2 : ℕ) + δ n)) ∧
    (∀ n : ℕ, 0 < n → IsGreatest
      (haltingTimes m (initialConfig start inp bit sep blank) n) (W n)) ∧
    ∀ n : ℕ, 0 < n → ∀ x y : List Bool, x.length = n → y.length = n →
      let init := initialConfig start inp bit sep blank x y
      ∃ (t : ℕ) (finish : TM.Config A Q I) (z : List Bool),
        Trace (TM.advance m) init t finish ∧ TM.advance m finish = none ∧
        TM.whole blank (z.map bit) (finish.tape out) ∧ z.length = 2*n ∧
        bitValue z = bitValue x*bitValue y ∧ VisitsAtMost m init t (S*n)

/-- Equivalence of the all-excess-exponents specification and the literal
worst-case theorem, including actual attainment for each positive width. -/
theorem uniformMultiplicationSpec_iff_worstCase : UniformMultiplicationSpec ↔ UniformWorstCaseSpec := by
  constructor
  · rintro ⟨A,Q,I,hA,hQ,hI,bit,sep,blank,inp,out,start,m,T,S,hinj,hs,hsep,ht,run⟩
    let E := haltingTimes m (initialConfig start inp bit sep blank)
    have inhabited (n : ℕ) (hn : 0 < n) : (E n).Nonempty := by
      let x := List.replicate n false
      have hx : x.length = n := List.length_replicate
      obtain ⟨t,c,_,r,h,_⟩ := run n hn x x hx hx
      exact ⟨t,x,x,hx,hx,c,r,h⟩
    have bound n (hn : 0 < n) : ∀ t ∈ E n, t ≤ T n := by
      rintro t ⟨x,y,hx,hy,c,r,hc⟩
      obtain ⟨t',c',_,r',hc',_,_,_,le,_⟩ := run n hn x y hx hy
      exact (halting_trace_unique r hc r' hc').1 ▸ le
    obtain ⟨W,le,top⟩ := attained inhabited bound
    obtain ⟨δ,lim,eq⟩ := (allEpsilonBounds_iff_vanishingExponentBound T).mp
      ((allEpsilonBounds_iff_forall_pos T).mpr ht)
    refine ⟨A,Q,I,hA,hQ,hI,bit,sep,blank,inp,out,start,m,W,S,hinj,hs,hsep,⟨δ,lim,?_⟩,top,?_⟩
    · filter_upwards [eq] with n h
      exact (Nat.cast_le.mpr (le n)).trans h
    · intro n hn x y hx hy
      obtain ⟨t,c,z,r,h,word,len,value,_,space⟩ := run n hn x y hx hy
      exact ⟨t,c,z,r,h,word,len,value,space⟩
  · rintro ⟨A,Q,I,hA,hQ,hI,bit,sep,blank,inp,out,start,m,W,S,hinj,hs,hsep,hδ,top,run⟩
    refine ⟨A,Q,I,hA,hQ,hI,bit,sep,blank,inp,out,start,m,W,S,hinj,hs,hsep,
      (allEpsilonBounds_iff_forall_pos W).mp ((allEpsilonBounds_iff_vanishingExponentBound W).mpr hδ),?_⟩
    intro n hn x y hx hy
    obtain ⟨t,c,z,r,h,word,len,value,space⟩ := run n hn x y hx hy
    exact ⟨t,c,z,r,h,word,len,value,(top n hn).2 ⟨x,y,hx,hy,c,r,h⟩,space⟩

end NearSquareRoot
end Computability
end OAI
