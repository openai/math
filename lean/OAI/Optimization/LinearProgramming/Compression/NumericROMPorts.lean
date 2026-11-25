import OAI.Optimization.LinearProgramming.RAM.FrameFirstHeader
import OAI.Optimization.LinearProgramming.RAM.Array

/-! Compute the finite cache-window and BitRAM ports in disposable low address registers.
The source cache data and all logical address words from 60 upwards remain intact. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace NumericROM

variable {K : Type*}

open RAM RAM.Block RAM.Tape RAM.Call Polynomial

private def moves : List (ℕ × ℕ) → Block
  | [] => .skip
  | (d,s)::xs => .seq (.op (.addrCopy d s)) (moves xs)

private def moved (m : Memory K) : List (ℕ × ℕ) → Memory K
  | [] => m
  | (d,s)::xs => moved (m.putIndex d (m.index s)) xs

private theorem moved_data (m : Memory K) (xs : List (ℕ×ℕ)) : (moved m xs).data=m.data := by
  induction xs generalizing m with
  | nil => rfl
  | cons head tail ih => obtain ⟨d,s⟩ := head; exact ih _

private theorem moved_bound (m : Memory K) (xs : List (ℕ×ℕ)) {R : ℕ} (bound : ∀i,m.index i≤R) :
    ∀i,(moved m xs).index i≤R := by
  induction xs generalizing m with
  | nil => exact bound
  | cons x xs ih =>
    obtain ⟨d,s⟩ := x
    apply ih
    intro j
    by_cases h : j=d
    · subst j; simpa using bound s
    · simpa [Memory.putIndex_ne _ h] using bound j

private def sourceMoves : List (ℕ×ℕ) := [(1,102),(2,83),(3,84),(4,67)]
private def finalMoves : List (ℕ×ℕ) := [(43,5),(47,3),(51,2),(53,1),(55,4)]

private def capExpr (C E : ℕ) : AddressTerm 6 := .val C*addressPower (.reg 1+1) E

/-- Low address 0 holds cap and 1 through 5 hold the future external port parameters. -/
private def portPlan : HeaderPlan 6 :=
  [(5,2*.reg 0+1),(1,.reg 5+(.reg 2+1)*(2*(.reg 3+1)+2)),
   (3,.reg 1+(.reg 2+1)),(4,4*.reg 4+2),(2,.reg 2+1)]

def numericPortBlock (C E : ℕ) : Block :=
  .seq (moves sourceMoves) (.seq ((capExpr C E).code 8)
    (.seq (.op (.addrCopy 0 8)) (.seq (HeaderPlan.code 8 portPlan) (moves finalMoves))))

private theorem power_writesBelow (E : ℕ) :
    ((addressPower ((.reg 1+1) : AddressTerm 6) E).code 9).indexWritesBelow 60=true := by
  induction E with
  | zero => rfl
  | succ E ih =>
    change (((addressPower ((.reg 1+1) : AddressTerm 6) E).code 9).indexWritesBelow 60 && true)=true
    simp [ih]

private theorem numericPort_writesBelow (C E : ℕ) : (numericPortBlock C E).indexWritesBelow 60=true := by
  change ((true && (true && (((addressPower ((.reg 1+1) : AddressTerm 6) E).code 9).indexWritesBelow 60 && true))) && true)=true
  simp [power_writesBelow]

structure NormalPorts (cap d fuel base : ℕ) (m : Memory K) : Prop where
  window : m.index 0=cap
  send : m.index 43=2*cap+1
  recv : m.index 47=2*cap+1+(d+1)*(2*(fuel+1)+2)+(d+1)
  count : m.index 51=d+1
  src : m.index 53=2*cap+1+(d+1)*(2*(fuel+1)+2)
  target : m.index 55=4*base+2

noncomputable def numericPortPolynomial (C E : ℕ) (R : Polynomial ℕ) : Polynomial ℕ :=
  (capExpr C E).boundCost.comp R + (HeaderPlan.budget portPlan).comp (Polynomial.C C*(X+1)^E+R)+10

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {P : K → Prop}

private theorem moves_run (xs : List (ℕ×ℕ)) (m : Memory K) (hs : m.AllData P) :
    Block.Eval (Memory.AllData P) (moves xs) m xs.length (moved m xs) := by
  induction xs generalizing m with
  | nil => exact .skip hs
  | cons x rest ih =>
    obtain ⟨d,s⟩ := x
    have cp : Block.Eval (Memory.AllData P) (.op (.addrCopy d s)) m 1 (m.putIndex d (m.index s)) :=
      Block.Eval.op_addrCopy (safe := Memory.AllData P) m d s hs (hs.putIndex _ _)
    simpa only [moves,moved,List.length_cons,Nat.add_comm 1] using cp.seq (ih _ cp.safe_end)

/-- The fixed numerical port computation charges its absolute addresses by a polynomial
of the input dimension and is independent of all scalar values. -/
theorem numericPortBlock_correct (C E : ℕ) (R : Polynomial ℕ) (n d fuel base : ℕ) (m : Memory K)
    (hs : m.AllData P) (size : ∀ i,m.index i≤R.eval n)
    (dim : m.index 102=n) (arity : m.index 83=d) (cutoff : m.index 84=fuel) (row : m.index 67=base) :
    ∃ t k, Block.Eval (Memory.AllData P) (numericPortBlock C E) m k t ∧
      k≤(numericPortPolynomial C E R).eval n ∧ NormalPorts (polyBound C E n) d fuel base t ∧
      t.data=m.data ∧ ∀ j,60≤j → t.index j=m.index j := by
  have scalarInvariant : RAM.Tape.Good P = Memory.AllData P := by
    funext state
    rfl
  let s := moved m sourceMoves
  let env (i : Fin 6) := s.index i
  have read := moves_run sourceMoves m hs
  have known : s.index 1=n ∧ s.index 2=d ∧ s.index 3=fuel ∧ s.index 4=base := by
    simp [s,moved,sourceMoves,dim,arity,cutoff,row]
  have sBound := moved_bound m sourceMoves size
  obtain ⟨k,u,calcCap,hk,ud,lower,value⟩ := (capExpr C E).correct (P := P) env 8 s (by decide)
    (fun _ => rfl) read.safe_end
  rw [scalarInvariant] at calcCap
  have upper : k ≤ (capExpr C E).boundCost.eval (R.eval n) := hk.trans ((capExpr C E).cost_le env _ (fun i => sBound i))
  let cap := polyBound C E n
  have capValue : u.index 8=cap := by
    simpa [capExpr,addressPower_value,AddressTerm.value,AddressOp.value,env,known.1,cap,polyBound] using value
  let v := u.putIndex 0 (u.index 8)
  have cp : Block.Eval (Memory.AllData P) (.op (.addrCopy 0 8)) u 1 v :=
    Block.Eval.op_addrCopy (safe := Memory.AllData P) u 0 8 calcCap.safe_end (calcCap.safe_end.putIndex _ _)
  let ve (i : Fin 6) := v.index i
  have v0 : v.index 0=cap := by simpa [v] using capValue
  have v2 : v.index 2=d := by rw [show v.index 2=u.index 2 by simp [v],lower 2 (by decide)];exact known.2.1
  have v3 : v.index 3=fuel := by rw [show v.index 3=u.index 3 by simp [v],lower 3 (by decide)];exact known.2.2.1
  have v4 : v.index 4=base := by rw [show v.index 4=u.index 4 by simp [v],lower 4 (by decide)];exact known.2.2.2
  have vone (i : Fin 6) : ve i≤cap+R.eval n := by
    by_cases h : i.val=0
    · change v.index i.val≤_
      rw [h,v0];omega
    · change v.index i.val≤_
      rw [show v.index i.val=u.index i.val from Memory.putIndex_ne u h _,lower i (by omega)]
      exact (sBound i).trans (Nat.le_add_left _ _)
  obtain ⟨z,l,run,hl,zd,low⟩ := HeaderPlan.correct (P := P) portPlan 8 (by decide) v ve (fun _ => rfl) cp.safe_end
  rw [scalarInvariant] at run
  let t := moved z finalMoves
  have last := moves_run finalMoves z run.safe_end
  have assembled := read.seq (calcCap.seq (cp.seq (run.seq last)))
  have hclock := hl.trans (HeaderPlan.cost_le portPlan ve _ vone)
  refine ⟨t,_,assembled,?_,?_,(moved_data z finalMoves).trans (zd.trans (ud.trans (moved_data m sourceMoves))),fun _ hj => assembled.index_frame (numericPort_writesBelow C E) hj⟩
  · simp only [numericPortPolynomial,eval_add,eval_comp,eval_mul,eval_C,eval_pow,eval_X,eval_one,eval_ofNat]
    change 4+(k+(1+(l+5))) ≤ _
    dsimp only [cap,polyBound] at hclock
    omega
  · constructor
    all_goals change (moved z finalMoves).index _=_
    all_goals simp [finalMoves,moved]
    all_goals first | apply (low (0 : Fin 6)).trans | apply (low (1 : Fin 6)).trans |
      apply (low (2 : Fin 6)).trans | apply (low (3 : Fin 6)).trans | apply (low (4 : Fin 6)).trans | apply (low (5 : Fin 6)).trans
    all_goals simp [portPlan,HeaderPlan.output,AddressTerm.value,AddressOp.value,ve,v0,v2,v3,v4]
    all_goals rfl

end NumericROM
end Compression
end LinearProgramming
end Optimization
end OAI
