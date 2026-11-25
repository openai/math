import OAI.Optimization.LinearProgramming.RAM.FrameStatic
import OAI.Optimization.LinearProgramming.RAM.Footprint

/-! Argument headers used to start the first feasibility call of the optimization program. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Call

variable {K : Type*}

open Block Tape

/-- The program exponent is fixed before the input; this is code generation for an
ordinary sequence of address multiplications. -/
def addressPower {n : Nat} (x : AddressTerm n) : Nat → AddressTerm n
  | 0 => 1
  | e+1 => addressPower x e * x

@[simp] theorem addressPower_value {n : Nat} (x : AddressTerm n) (e : Nat) (env : Fin n → Nat) :
    (addressPower x e).value env = (x.value env)^e := by
  induction e with
  | zero => simp [addressPower,AddressTerm.value]
  | succ e ih => change (addressPower x e).value env*x.value env = _; rw [ih,pow_succ]

def primalLength (m d : Nat) : Nat := m*d+m
def optimizationLength (m d : Nat) : Nat := primalLength m d+d
def firstSource (m d : Nat) : Nat := 3+2*(primalLength m d+optimizationLength m d)

def firstHeaders (p : Program) (C E : Nat) : HeaderPlan 40 :=
  let m : AddressTerm 40 := .reg 9
  let d : AddressTerm 40 := .reg 11
  [(9,.reg 0), (11,.reg 1), (15,m*d+m), (19,.reg 15+d),
   (13,3+2*(.reg 15+.reg 19)), (17,.reg 13),
   (21,.reg 13+.reg 19+100+.val (addressBudget p)+.val C * addressPower (m+d+1) E),
   (2,.reg 19), (1,.reg 13), (0,0), (3,0)]

def rawLimit (p : Program) (C E m d : Nat) : Nat :=
  firstSource m d + optimizationLength m d + 100 + addressBudget p + polyBound C E (m+d)

def firstStatic (p : Program) (C E : Nat) : Nat :=
  max 100 (indexLimitBlock (HeaderPlan.code 40 (firstHeaders p C E)))

def firstLimit (p : Program) (C E m d : Nat) : Nat := max (rawLimit p C E m d) (firstStatic p C E)

def raiseLimit (cap : Nat) : Block := .seq (.op (.addrConst 39 cap))
  (.branch (.addrLT 21 39) (.op (.addrCopy 21 39)) .skip)

def firstHeaderBlock (p : Program) (C E : Nat) : Block :=
  .seq (HeaderPlan.code 40 (firstHeaders p C E)) (raiseLimit (firstStatic p C E))

structure FirstPointers (p : Program) (C E m d : Nat) (t : Memory K) : Prop where
  source : t.index 0 = 0
  destination : t.index 1 = firstSource m d
  count : t.index 2 = optimizationLength m d
  zero : t.index 3 = 0
  rows : t.index 9 = m
  cols : t.index 11 = d
  primalSource : t.index 13 = firstSource m d
  primalWords : t.index 15 = primalLength m d
  savedSource : t.index 17 = firstSource m d
  savedWords : t.index 19 = optimizationLength m d
  limit : t.index 21 = firstLimit p C E m d

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {P : K → Prop}

private theorem raiseLimit_correct (cap : Nat) (s : Memory K) (hs : Good P s) :
    ∃ t k, Eval (Good P) (raiseLimit cap) s k t ∧ k ≤ 4 ∧ t.data = s.data ∧
      t.index 21 = max (s.index 21) cap ∧ ∀ i, i ≠ 39 → i ≠ 21 → t.index i = s.index i := by
  let a := s.putIndex 39 cap
  have head : Eval (Good P) (.op (.addrConst 39 cap)) s 1 a := eval_constI s hs _ _
  by_cases h : s.index 21 < cap
  · let t := a.putIndex 21 (a.index 39)
    have set : Eval (Good P) (.op (.addrCopy 21 39)) a 1 t := eval_copyI a head.safe_end _ _
    have test : (Cond.addrLT 21 39).test a = true := by simp [Cond.test,a,h]
    exact ⟨t,4,head.seq (.branchTrue test set),by decide,rfl,
      by simp [t,a,max_eq_right h.le],fun i h39 h21 => by simp [t,a,h39,h21]⟩
  · have test : (Cond.addrLT 21 39).test a = false := by simp [Cond.test,a,h]
    exact ⟨a,2,head.seq (.branchFalse test (.skip head.safe_end)),by decide,rfl,
      by simp [a,max_eq_left (Nat.le_of_not_gt h)],fun i h39 _ => by simp [a,h39]⟩

/-- Program limits and scratch extents are part of the finite code. Their values do
not introduce an uncharged operation depending on a field coefficient. -/
theorem firstHeaderBlock_correct (p : Program) (C E m d : Nat) (s : Memory K)
    (hs : Good P s) (hm : s.index 0 = m) (hd : s.index 1 = d)
    (hidx : ∀ i : Fin 40, s.index i ≤ m+d) :
    ∃ t k, Eval (Good P) (firstHeaderBlock p C E) s k t ∧
      k ≤ (HeaderPlan.budget (firstHeaders p C E)).eval (m+d) + 4 ∧
      t.data = s.data ∧ FirstPointers p C E m d t ∧
      ∀ i, firstStatic p C E ≤ i → t.index i = s.index i := by
  let env := fun i : Fin 40 => s.index i
  obtain ⟨u,k,run,hk,hu,low⟩ := HeaderPlan.correct (firstHeaders p C E) 40 (by decide)
    s env (fun _ => rfl) hs
  obtain ⟨t,j,limit,hj,dt,top,unchanged⟩ := raiseLimit_correct (firstStatic p C E) u run.safe_end
  have raw : u.index 21 = rawLimit p C E m d := by
    have h := low (21 : Fin 40)
    simpa [env,firstHeaders,HeaderPlan.output,AddressTerm.value,AddressOp.value,
      rawLimit,primalLength,optimizationLength,firstSource,polyBound,hm,hd] using h
  have regs : FirstPointers p C E m d t := by
    constructor
    all_goals first | (exact top.trans (by rw [raw]; rfl)) |
      (rw [unchanged _ (by decide) (by decide)];
       first | apply (low (0 : Fin 40)).trans | apply (low (1 : Fin 40)).trans |
         apply (low (2 : Fin 40)).trans | apply (low (3 : Fin 40)).trans |
         apply (low (9 : Fin 40)).trans | apply (low (11 : Fin 40)).trans |
         apply (low (13 : Fin 40)).trans | apply (low (15 : Fin 40)).trans |
         apply (low (17 : Fin 40)).trans | apply (low (19 : Fin 40)).trans)
    all_goals simp [env,firstHeaders,HeaderPlan.output,AddressTerm.value,AddressOp.value,
      firstSource,optimizationLength,primalLength,hm,hd]
  have cap : indexLimitBlock (HeaderPlan.code 40 (firstHeaders p C E)) ≤ firstStatic p C E :=
    le_max_right _ _
  refine ⟨t,k+j,run.seq limit,Nat.add_le_add (hk.trans (HeaderPlan.cost_le _ _ _ hidx)) hj,
    dt.trans hu,regs,?_⟩
  intro i hi
  have hundred : 100 ≤ i := (le_max_left _ _).trans hi
  rw [unchanged _ (by omega) (by omega)]
  exact run.index_frame (indexWritesBelow_of_direct _ _ (header_direct _ _) cap) hi

end Call
end RAM
end LinearProgramming
end Optimization
end OAI
