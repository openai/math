import OAI.Computability.BorderVNP.DiagonalResidueRAMPathSum
import OAI.Computability.BorderVNP.RoutingISAEvaluator

/-! # Team zero executes the residue reader exactly once -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalResidueRAM

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM RoutingISA RoutingISA.Evaluator

variable {w : ℕ}

/-- The word bank after reading team number and initializing the zero comparison operand. -/
def leadBank (pub : Arg → Word w) (s : Bank w) (m : Memory w) : Bank w :=
  Function.update (Function.update (Function.update (Function.update s 62 (pub 0)) 63 0) 59
    (m (pub 0).val)) 58 0

/-- Fixed team-ID reads and checks before either native branch. -/
def leadPrefix (pub : Arg → Word w) (m : Memory w) : List (TeamRAM.Event w) :=
  [tick w,tick w,tick w,Evaluator.branchRead (pub 0).val m,tick w,tick w]

private theorem leadRead {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    (s : Bank w) (m : Memory w) :
    let t := Function.update (Function.update (Function.update s 62 (pub 0)) 63 0) 59 (m (pub 0).val)
    Runs pub mac (readFrame 59 62 63 0) s m
      [tick w,tick w,tick w,Evaluator.branchRead (pub 0).val m] t m := by
  intro t
  let b := Function.update s (62 : Reg) (pub 0)
  let c := Function.update b (63 : Reg) 0
  have hp : Runs pub mac (.publicWord 62 0) s m [tick w] b m := Runs.localStep _ rfl rfl
  have hc : Runs pub mac (.constant 63 0) b m [tick w] c m := Runs.localStep _ rfl rfl
  have hadd : Runs pub mac (.binary .add 62 62 63) c m [tick w] c m := by
    apply Runs.localStep _ rfl
    have restore : Function.update c (62 : Reg) (c 62) = c := Function.update_eq_self ..
    simp [Code.atom,BinaryOp.eval,c,b,Function.update] at restore ⊢
  have hget : Runs pub mac (.load 59 62) c m [Evaluator.branchRead (pub 0).val m] t m := by
    simpa [t,c,b,Function.update,Evaluator.branchRead] using Runs.load pub mac 59 62 c m
  exact hp.seq (hc.seq (hadd.seq hget))

/-- Every returning path through the linked lead fragment consists of six
deterministic read/compare ticks and precisely the selected branch. Both
directions preserve the final register bank and memory. -/
theorem lead_iff {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    (s : Bank w) (m : Memory w) {es z mz} :
    Runs pub mac leadEntry s m es z mz ↔
      ∃ tail, es = leadPrefix pub m ++ tail ∧
        Runs pub mac (if m (pub 0).val = 0 then stagedReader else .nop) (leadBank pub s m) m tail z mz := by
  let t := Function.update (Function.update (Function.update s (62 : Reg) (pub 0)) 63 0) 59 (m (pub 0).val)
  let z' := leadBank pub s m
  have first := leadRead (pub := pub) (mac := mac) s m
  have second : Runs pub mac (.constant 58 0) t m [tick w] z' m := Runs.localStep _ rfl rfl
  have cmp : z' 59 = z' 58 ↔ m (pub 0).val = 0 := by simp [z',leadBank,Function.update]
  change Runs pub mac (.seq (readFrame 59 62 63 0) (.seq (.constant 58 0) (.ifEq 59 58 stagedReader .nop)))
    s m es z mz ↔ _
  constructor
  · intro run
    obtain ⟨_,_,a,b,rfl,ra,rb⟩ := Runs.seq_iff.mp run
    obtain ⟨rfl,rfl,rfl⟩ := first.unique_of_deterministic (by decide) ra
    obtain ⟨_,_,a,b,rfl,ra,rb⟩ := Runs.seq_iff.mp rb
    obtain ⟨rfl,rfl,rfl⟩ := second.unique_of_deterministic rfl ra
    obtain ⟨tail,rfl,rt⟩ := CellDispatch.eq_split rb
    exact ⟨tail,rfl,by simpa only [←cmp] using rt⟩
  · rintro ⟨tail,rfl,rt⟩
    have branch : Runs pub mac (.ifEq 59 58 stagedReader .nop) z' m (tick w::tail) z mz :=
      .ifEq (by simpa only [cmp] using rt)
    exact first.seq (second.seq branch)

/-- A nonzero team contributes one positive seven-tick path and performs
no writes at this stage. -/
theorem lead_other_iff {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    (s : Bank w) (m : Memory w) (team : m (pub 0).val ≠ 0) {es z mz} :
    Runs pub mac leadEntry s m es z mz ↔
      es = leadPrefix pub m ++ [tick w] ∧ z = leadBank pub s m ∧ mz = m := by
  rw [lead_iff s m,ite_eq_right team]
  have nop : Runs pub mac .nop (leadBank pub s m) m [tick w] (leadBank pub s m) m := Runs.localStep m rfl rfl
  constructor
  · rintro ⟨tail,rfl,r⟩
    obtain ⟨rfl,rfl,rfl⟩ := r.unique_of_deterministic rfl nop
    exact ⟨rfl,rfl,rfl⟩
  · rintro ⟨rfl,rfl,rfl⟩
    exact ⟨_,rfl,nop⟩

/-- Event traces of a returning linked lead fragment. -/
def LeadReturns (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w) :=
  {es : List (TeamRAM.Event w) // ∃ z mz, Runs pub mac leadEntry s m es z mz}

/-- Prefixing the six team-test instructions identifies all team-zero returns
with the actual native traces of the staged reader. -/
noncomputable def leadZeroEquiv {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    (s : Bank w) (m : Memory w) (team : m (pub 0).val = 0) :
    StagedPaths pub mac (leadBank pub s m) m ≃ LeadReturns pub mac s m := by
  let f (p : StagedPaths pub mac (leadBank pub s m) m) : LeadReturns pub mac s m :=
    ⟨leadPrefix pub m++p.val,by
      obtain ⟨⟨z,mz,r⟩,_⟩ := (Code.execute_iff_runs (c := stagedReader) (by decide)).mp p.property
      exact ⟨z,mz,(lead_iff s m).mpr ⟨_,rfl,by simpa only [ite_eq_left team] using r⟩⟩⟩
  refine Equiv.ofBijective f ⟨?_,?_⟩
  · intro a b h
    exact Subtype.ext (List.append_cancel_left (congrArg Subtype.val h))
  · intro p
    obtain ⟨z,mz,r⟩ := p.property
    obtain ⟨tail,he,rt⟩ := (lead_iff s m).mp r
    rw [ite_eq_left team] at rt
    exact ⟨⟨tail,rt.execute⟩,Subtype.ext he.symm⟩

/-- The six fixed lead ticks contribute one and use no branch choices. -/
theorem leadPrefix_trace (pub : Arg → Word w) (m : Memory w) : TraceOK (leadPrefix pub m) [] 6 := by
  simp [TraceOK,leadPrefix,tick,Evaluator.branchRead]

/-- Every other team's unique return is the required unsigned unit. -/
theorem lead_other_card {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    (s : Bank w) (m : Memory w) (team : m (pub 0).val ≠ 0) : Nat.card (LeadReturns pub mac s m) = 1 := by
  let val : LeadReturns pub mac s m := ⟨leadPrefix pub m++[tick w],_,_,(lead_other_iff s m team).mpr ⟨rfl,rfl,rfl⟩⟩
  let e : LeadReturns pub mac s m ≃ Unit := {
    toFun := fun _ => ()
    invFun := fun _ => val
    left_inv := fun p => by
      obtain ⟨_,_,r⟩ := p.property
      exact Subtype.ext ((lead_other_iff s m team).mp r).1.symm
    right_inv := fun _ => rfl }
  rw [Nat.card_congr e,Nat.card_eq_fintype_card]; rfl

end DiagonalResidueRAM

end BorderVNP
end Computability
end OAI
