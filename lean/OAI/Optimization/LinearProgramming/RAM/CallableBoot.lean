import OAI.Optimization.LinearProgramming.RAM.CallableBootAddress
import OAI.Optimization.LinearProgramming.RAM.CallableBootScalar
import OAI.Optimization.LinearProgramming.RAM.CallableBootSave
import OAI.Optimization.LinearProgramming.RAM.CallableFiniteInput

/-! Ordinary contiguous input entry for callable arithmetic-RAM fragments. The
whole physical memory equals the finite two-bank encoding at the return point. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Callable
namespace Boot

variable {K : Type*}

open Block

def bootBlock : Block := .seq saveBlock (.seq scalarBlock addressBlock)

/-- Sufficient room for all input cells and fixed pointer registers. -/
def minimumCap (addressLength scalarLength : ℕ) : ℕ :=
  max 64 (max (2*addressLength+4) (2*scalarLength+4))

private theorem mem_eq {s t : Memory K} (hd : ∀ j,s.data j=t.data j)
    (hi : ∀ j,s.index j=t.index j) : s=t := by
  cases s
  cases t
  congr <;> funext j
  · exact hd j
  · exact hi j

private theorem listWord_le (xs : List ℕ) (r : ℕ) : xs[r]?.getD 0 ≤ xs.sum := by
  cases h : xs[r]? with
  | none => exact Nat.zero_le _
  | some x => exact List.le_sum_of_mem (List.mem_of_getElem? h)

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- A preceding fixed preheader may leave arbitrary address scratch below the cap.
Only the declared dimensions, the three public counters, and the zero high tail
are read before the complete target memory has been produced. -/
theorem bootBlock_from_memory (P : K→Prop) (s : Memory K) (ds : List ℕ) (xs : List K) (cap : ℕ)
    (hc : minimumCap ds.length xs.length ≤ cap) (hs : s.AllData P) (hz : P 0)
    (c0 : s.index 0=cap) (c1 : s.index 1=ds.length) (c2 : s.index 2=xs.length)
    (dims : ∀ i < ds.length, s.index (3+i)=ds[i]?.getD 0)
    (scalar : ∀ r, s.data r=xs[r]?.getD 0) (tail : ∀r, cap < r → s.index r=0) :
    ∃ k, k ≤ 1000*(cap+ds.sum+xs.length+1)^2 ∧
      Eval (Memory.AllData P) bootBlock s k
        (start (Odd.finiteDims cap [] ds) (Odd.finiteScalars [] xs)).memory := by
  unfold minimumCap at hc
  have big : 64 ≤ cap := by omega
  have roomD : 2*ds.length+4 ≤ cap := by omega
  have roomX : 2*xs.length+4 ≤ cap := by omega
  obtain ⟨a,ea,ad,a0,aw,af⟩ := saveBlock_spec P s cap hs c0 (by omega)
  have a2 := (af 2 (.inl (by omega))).trans c2
  have azero (r : ℕ) (hr : xs.length ≤ r) : a.data r=0 := by
    rw [ad,scalar,List.getElem?_eq_none hr]
    rfl
  obtain ⟨q,l,hl,eq,qd,qi⟩ := scalarBlock_spec P a cap xs.length ea.safe_end hz a0 a2 roomX azero
  let f := fun i : ℕ => ds[i]?.getD 0
  have q0 := (qi 0 (by decide)).trans a0
  have q1 := (qi 1 (by decide)).trans ((af 1 (.inl (by omega))).trans c1)
  obtain ⟨t,k,hk,et,td,ti⟩ := addressBlock_spec P q cap ds.length ds.sum f eq.safe_end
    big roomD q0 q1
    (fun i hi small => (qi _ (.inr (by omega))).trans ((aw i small).trans (dims i hi)))
    (fun i i9 hi => (qi _ (.inr (by omega))).trans ((af _ (.inl (by omega))).trans (dims i hi)))
    (fun i hi => by simp [f,List.getElem?_eq_none hi]) (listWord_le ds)
    (fun r hr => (qi _ (.inr (by omega))).trans ((af _ (.inr (by omega))).trans (tail _ (by omega))))
  have finish : t=(start (Odd.finiteDims cap [] ds) (Odd.finiteScalars [] xs)).memory := by
    apply mem_eq
    · intro r
      change t.data r=(Odd.finiteScalars ([] : List K) xs)[r]?.getD 0
      rw [td,qd,Odd.finiteScalars_empty_native,ad,scalar]
    · intro r
      change t.index r=(Odd.finiteDims cap [] ds)[r]?.getD 0
      rw [ti,Odd.finiteDims_empty_native]
      rfl
  refine ⟨27+(l+k),?_,finish ▸ ea.seq (eq.seq et)⟩
  let a' := cap+ds.sum+xs.length+1
  have hc' : cap+ds.sum+1 ≤ a' := by dsimp [a']; omega
  have hx' : xs.length+1 ≤ a' := by dsimp [a']; omega
  have pos : 0 < a' := by dsimp [a']; omega
  have sq : (cap+ds.sum+1)^2 ≤ a'^2 := Nat.pow_le_pow_left hc' 2
  have lin : a'≤a'^2 := by simpa [pow_two] using Nat.le_mul_of_pos_right a' pos
  have bound := hk.trans (addressCost_le cap ds.sum)
  change 27+(l+k) ≤ 1000*a'^2
  omega

/-- The fixed, generically callable bootstrap on the native machine's ordinary list
entry. The counted trace satisfies the scalar predicate throughout. -/
theorem bootBlock_spec (P : K→Prop) (ds : List ℕ) (xs : List K) (cap : ℕ)
    (hc : minimumCap ds.length xs.length ≤ cap) (hz : P 0) (hx : ∀ x∈xs,P x) :
    ∃ k, k ≤ 1000*(cap+ds.sum+xs.length+1)^2 ∧
      Eval (Memory.AllData P) bootBlock (start ([cap,ds.length,xs.length]++ds) xs).memory k
        (start (Odd.finiteDims cap [] ds) (Odd.finiteScalars [] xs)).memory := by
  let s := (start ([cap,ds.length,xs.length]++ds) xs).memory
  have safe : s.AllData P := by
    intro r
    change P (xs[r]?.getD 0)
    cases h : xs[r]? with
    | none => exact hz
    | some x => exact hx x (List.mem_of_getElem? h)
  have dims (i : ℕ) (_ : i < ds.length) : s.index (3+i)=ds[i]?.getD 0 := by
    change ((cap::ds.length::xs.length::ds)[3+i]?).getD 0=_
    rw [show 3+i=i+1+1+1 by omega]
    rfl
  have tail (r : ℕ) (hr : cap < r) : s.index r=0 := by
    change (([cap,ds.length,xs.length]++ds)[r]?).getD 0=0
    have length : ([cap,ds.length,xs.length]++ds).length ≤ r := by
      unfold minimumCap at hc
      simp
      omega
    rw [List.getElem?_eq_none length]
    rfl
  exact bootBlock_from_memory P s ds xs cap hc safe hz rfl rfl rfl dims (fun _ => rfl) tail

end Boot
end Callable
end RAM
end LinearProgramming
end Optimization
end OAI
