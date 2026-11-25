import OAI.Optimization.LinearProgramming.RAM.CallableBootFill
import OAI.Optimization.LinearProgramming.RAM.CallableBootScatter
import OAI.Optimization.LinearProgramming.RAM.CallableBootEven
import OAI.Optimization.LinearProgramming.RAM.CallableBootRestore

/-! Construct both physical address banks, including the bounded encoded-zero tail
and exact erasure of all temporary high words. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Callable
namespace Boot

open Block

def addressBlock : Block := .seq fillBlock (.seq scatterBlock (.seq clearEvenBlock restoreBlock))

def addressCost (cap B : ℕ) : ℕ :=
  (6+((cap+1)/2)*(5*B+16)+1)+(10+(((cap+1)/2-6)*8+1))+ (3+((cap/2+1-6)*5+1))+24

def physicalIndex (cap : ℕ) (f : ℕ→ℕ) (r : ℕ) : ℕ :=
  if r ≤ cap ∧ r%2=1 then 2*f (r/2)+1 else 0

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem addressBlock_spec (P : K → Prop) (s : Memory K) (cap n B : ℕ) (f : ℕ→ℕ)
    (hs : s.AllData P) (hc : 64 ≤ cap) (hncap : 2*n+4 ≤ cap)
    (h0 : s.index 0=cap) (h1 : s.index 1=n)
    (low : ∀ i < n, i < 9 → s.index (cap+1+i)=f i)
    (high : ∀ i, 9 ≤ i → i < n → s.index (3+i)=f i)
    (zero : ∀ i, n ≤ i → f i=0) (bound : ∀ i, f i ≤ B)
    (outer : ∀ r, cap+10 ≤ r → s.index r=0) :
    ∃ t k, k ≤ addressCost cap B ∧ Eval (Memory.AllData P) addressBlock s k t ∧
      t.data=s.data ∧ ∀ r,t.index r=physicalIndex cap f r := by
  obtain ⟨a,ka,hka,ea,ad,a0,aw,af⟩ := fillBlock_spec P s cap n B f hs hc hncap h0 h1
    low high zero bound
  obtain ⟨m,em,md,m0,mw,mf⟩ := scatterBlock_spec P a cap (fun i => 2*f i+1) ea.safe_end hc a0 aw
  obtain ⟨u,eu,ud,u0,uw,uf⟩ := clearEvenBlock_spec P m cap em.safe_end hc m0
  obtain ⟨t,et,td,tw,te,tf⟩ := restoreBlock_spec P u cap eu.safe_end hc u0
  have hkeep (i : ℕ) (hi : i < 6) : u.index (cap+1+i)=2*f i+1 := by
    have ev := uf (cap+1+i) (by omega) (.inl (by omega))
    have sc := mf (cap+1+i) (by omega) (fun j j6 jhi => by constructor <;> omega)
    exact ev.trans (sc.trans (aw i (by omega)))
  have whole := ea.seq (em.seq (eu.seq et))
  refine ⟨t,_,?_,whole,td.trans (ud.trans (md.trans ad)),?_⟩
  · unfold addressCost
    omega
  intro r
  by_cases live : r ≤ cap
  · by_cases odd : r%2=1
    · have rep : 2*(r/2)+1=r := by omega
      simp [physicalIndex,live,odd]
      by_cases small : r/2 < 6
      · simpa only [rep] using (tw (r/2) small).1.trans (hkeep (r/2) small)
      · have hr : 11 < r := by omega
        have eq := (tf r hr (.inl (by omega))).trans (uf r hr (.inr odd))
        have w := (mw (r/2) (by omega) (by omega)).1
        exact eq.trans (by simpa only [rep] using w)
    · have rep : 2*(r/2)=r := by omega
      simp [physicalIndex,live,odd]
      by_cases small : r/2 < 6
      · simpa only [rep] using te (r/2) small
      · have hr : 11 < r := by omega
        exact (tf r hr (.inl (by omega))).trans (by simpa only [rep] using uw (r/2) (by omega) (by omega))
  · simp [physicalIndex,live]
    have hr : 11 < r := by omega
    let j := r-(cap+1)
    have rep : cap+1+j=r := by dsimp [j]; omega
    by_cases small : j < 6
    · simpa only [rep] using (tw j small).2
    · have fr := (tf r hr (.inr (by dsimp [j] at small; omega))).trans (uf r hr (.inl (by omega)))
      by_cases mid : j < (cap+1)/2
      · exact fr.trans (by simpa only [rep] using (mw j (by omega) mid).2)
      · have beyond : cap+1+(cap+1)/2 ≤ r := by dsimp [j] at mid; omega
        have mf' := mf r hr (fun i i6 ih => by constructor <;> omega)
        exact fr.trans (mf'.trans ((af r hr (.inr beyond)).trans (outer r (by omega))))

theorem addressCost_le (cap B : ℕ) : addressCost cap B ≤ 100*(cap+B+1)^2 := by
  let a := cap+B+1
  have h : (cap+1)/2 ≤ a := by dsimp [a]; omega
  have g : 5*B+16 ≤ 21*a := by dsimp [a]; omega
  have prod := Nat.mul_le_mul h g
  have simpProd : a*(21*a)=21*a^2 := by ring
  rw [simpProd] at prod
  have pos : 0 < a := by dsimp [a]; omega
  have linear : a ≤ a^2 := by simpa [pow_two] using Nat.le_mul_of_pos_right a pos
  change addressCost cap B ≤ 100*a^2
  unfold addressCost
  have capBound : cap ≤ a := by dsimp [a]; omega
  omega

end Boot
end Callable
end RAM
end LinearProgramming
end Optimization
end OAI
