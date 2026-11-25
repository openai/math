import OAI.Optimization.LinearProgramming.RAM.Code
import OAI.Optimization.LinearProgramming.Contract.AppOracleMachine
import OAI.Optimization.LinearProgramming.Geometry.BorderTailColumns
import OAI.Optimization.LinearProgramming.Geometry.PivotQueries

/-! One structural proof runs the column loop over any scalar memory with decidable
comparisons. The typed oracle values are rational, while `encode` places them in the
scalar bank of the particular machine. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace ScanKernel

open RAM RAM.Block Contract BorderBatch

variable {K : Type} {n : ℕ} {κ : Type*}

/-- Restart and successful data have different wire tags. -/
def reply [Zero K] [One K] (encode : ℚ → K) : Option ℚ → List K
  | none => [1]
  | some q => [0, encode q]

/-- The scalar oracle stores its history newest first. -/
def scanHistory [Zero K] (encode : ℚ → K) (packet : κ → List K) (xs : List (κ × ℚ)) (h : Contract.History K) : Contract.History K :=
  (xs.map (fun p => (packet p.1,[0,encode p.2]))).reverse ++ h

private theorem scanHistory_cons [Zero K] (encode : ℚ → K) (packet : κ → List K) (a : κ) (q : ℚ)
    (xs : List (κ × ℚ)) (h : Contract.History K) :
    scanHistory encode packet ((a,q)::xs) h = scanHistory encode packet xs ((packet a,[0,encode q])::h) := by
  simp [scanHistory,List.append_assoc]

/-- A scalar execution relation with a charged cost and a live oracle history. -/
abbrev ColumnExecution (K : Type) := Memory K → Contract.History K → ℕ → Memory K → Contract.History K → Prop

/-- A zero determinant skips the service. Every nonzero determinant transmits exactly
one canonical packet, either supplying the next value or stopping this scan. -/
def ColumnActionFor [Zero K] [One K] (encode : ℚ → K) (bodyRun : ColumnExecution K) (I : ℕ → (Fin n → ℚ) → Memory K → Prop) (stop : Memory K → Prop)
    (raw : Fin n → ℚ) (key : Fin n → κ) (packet : κ → List K) (C : ℕ) : Prop :=
  ∀ (j : Fin n) (v : Fin n → ℚ) (m : Memory K) (h : Contract.History K), I j.val v m →
    if raw j=0 then ∃ t c, c≤C ∧ bodyRun m h c t h ∧ I (j.val+1) v t
    else ∃ t c ans, c≤C ∧ bodyRun m h c t ((packet (key j), reply encode ans)::h) ∧
      match ans with
      | none => stop t
      | some q => I (j.val+1) (Function.update v j q) t

/-- The scalar history and the typed request trace describe the same exit. -/
def ScanExit [Zero K] [One K] (encode : ℚ → K) (I : ℕ → (Fin n → ℚ) → Memory K → Prop) (stop : Memory K → Prop)
    (packet : κ → List K) (t : Memory K) (h final : Contract.History K)
    (xs : List (κ × ℚ)) : Sum κ (Fin n → ℚ) → Prop
  | .inl a => stop t ∧ final = (packet a,[1]) :: scanHistory encode packet xs h
  | .inr vals => I n vals t ∧ final = scanHistory encode packet xs h

/-- The numerical and history induction for a charged column loop. The two supplied
rules are its stop and continue instructions; both ordinary and marked RAM executions
use precisely these instruction costs. -/
theorem scan_loop_with [Zero K] [One K] [LT K] [DecidableLT K] (encode : ℚ → K)
    (I : ℕ → (Fin n → ℚ) → Memory K → Prop) (stop : Memory K → Prop)
    (raw : Fin n → ℚ) (key : Fin n → κ) (packet : κ → List K) (P : Memory K → Prop)
    (bodyRun loopRun : ColumnExecution K) (C : ℕ)
    (stopRule : ∀ m h, P m → (Cond.addrLT 90 130).test m=false → loopRun m h 1 m h)
    (stepRule : ∀ {m u t h mid dest c k}, (Cond.addrLT 90 130).test m=true →
      bodyRun m h c u mid → loopRun u mid k t dest → loopRun m h (1+c+1+k) t dest)
    (live : ∀ i v (m : Memory K), I i v m → P m ∧ m.index 90=i ∧ m.index 130=n)
    (stopped : ∀ m, stop m → P m ∧ m.index 90=n ∧ m.index 130=n)
    (action : ColumnActionFor encode bodyRun I stop raw key packet C)
    (i : ℕ) (hi : i≤n) (v : Fin n → ℚ) (m : Memory K) (hist : Contract.History K) (start : I i v m) :
    ∃ t final cost xs out, cost ≤ (n-i)*(C+2)+1 ∧
      loopRun m hist cost t final ∧
      MinorQuery.Run (MinorQuery.readColumns key (tailColumns raw i) v) xs out ∧
      ScanExit encode I stop packet t hist final xs out := by
  suffices go : ∀ fuel a, a+fuel=n → ∀ w z h, I a w z →
      ∃ t final cost xs out, cost ≤ fuel*(C+2)+1 ∧
        loopRun z h cost t final ∧
        MinorQuery.Run (MinorQuery.readColumns key (tailColumns raw a) w) xs out ∧
        ScanExit encode I stop packet t h final xs out by
    exact go (n-i) i (by omega) v m hist start
  intro fuel
  induction fuel with
  | zero =>
    intro a ha w z h hw
    have ea : a=n := by omega
    subst a
    obtain ⟨safe,pos,cols⟩ := live n w z hw
    have guard : (Cond.addrLT 90 130).test z=false := by simp [Cond.test,pos,cols]
    refine ⟨z,h,1,[],.inr w,by simp,stopRule _ _ safe guard,?_,hw,rfl⟩
    simp only [tailColumns_end,MinorQuery.readColumns]
    exact .done _
  | succ rem ih =>
    intro a ha w z h hw
    let j : Fin n := ⟨a,by omega⟩
    have next : a+1+rem=n := by omega
    obtain ⟨_,pos,cols⟩ := live a w z hw
    have guard : (Cond.addrLT 90 130).test z=true := by simp [Cond.test,pos,cols,show a<n by omega]
    have act := action j w z h hw
    have table := tailColumns_step raw j
    change tailColumns raw a = _ at table
    by_cases hz : raw j=0
    · rw [ite_eq_left hz] at act table
      obtain ⟨u,c,hc,edge,hu⟩ := act
      obtain ⟨t,final,k,xs,out,hk,tail,trace,done⟩ := ih (a+1) next w u h hu
      exact ⟨t,final,1+c+1+k,xs,out,by rw [Nat.succ_mul]; omega,
        stepRule guard edge tail,by simpa only [table] using trace,done⟩
    · rw [ite_eq_right hz] at act table
      obtain ⟨u,c,ans,hc,edge,hu⟩ := act
      cases ans with
      | none =>
        obtain ⟨safe,ep,ec⟩ := stopped u hu
        have stopGuard : (Cond.addrLT 90 130).test u=false := by simp [Cond.test,ep,ec]
        refine ⟨u,_,1+c+1+1,[],.inl (key j),by rw [Nat.succ_mul]; omega,
          stepRule guard edge (stopRule _ _ safe stopGuard),?_,hu,rfl⟩
        rw [table]
        exact .restart _ _
      | some q =>
        obtain ⟨t,final,k,xs,out,hk,tail,trace,done⟩ :=
          ih (a+1) next (Function.update w j q) u ((packet (key j),[0,encode q])::h) hu
        refine ⟨t,final,1+c+1+k,(key j,q)::xs,out,by rw [Nat.succ_mul]; omega,
          stepRule guard edge tail,?_,?_⟩
        · rw [table]
          exact .answer _ _ q trace
        · cases out <;> simpa only [ScanExit,scanHistory_cons] using done

end ScanKernel
end Geometry
end LinearProgramming
end Optimization
end OAI
