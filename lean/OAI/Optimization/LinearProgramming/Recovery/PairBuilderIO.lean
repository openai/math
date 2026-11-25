import OAI.Optimization.LinearProgramming.Recovery.DenseEncoding
import OAI.Optimization.LinearProgramming.Recovery.PairBuilderMeta

/-! Stage rectangular inputs and account for the exact two result addresses for either ordering. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace PairBuilder
open RAM RAM.Call RAM.Callable RAM.Tape Matrix
open _root_.OAI.Optimization.LinearProgramming.Geometry

variable {K : Type}
variable {h n k s a b : ℕ} {l : Layout h n} {m t : Memory K}

theorem matrix_frame {r c p : ℕ} {x y : Memory K} (hw : y.data=x.data) : uniformRect r c p y=uniformRect r c p x := by
  ext i j; simp only [uniformRect,hw]

theorem init_run [Field K] [LinearOrder K] [IsStrictOrderedRing K] (l : Layout h n) (native caller : Memory K) (v : InputRegs l caller) (P : K→Prop)
    (hn : native.AllData P) (hm : caller.AllData P) :
    ∃t,(«meta» .init).Run P (Odd.memory native caller) (metaBudget.eval (limit l)) (Odd.memory native t) ∧
      t.AllData P ∧ MetaEffect .init caller t ∧ Internal l 0 0 0 0 t := by
  have fit (i : Fin 220) (hi : i∈needed (plan .init)) : caller.index i ≤ limit l := by
    have mem := (by decide : needed (plan .init) ⊆ ({200,201,205}:Finset (Fin 220))) hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at mem
    have hp := old_fits h n l.previous
    rcases mem with rfl|rfl|rfl
    · exact bound_read caller 200 v.height (by decide) (by unfold limit; omega)
    · exact bound_read caller 201 v.width (by decide) (by unfold limit; omega)
    · exact bound_read caller 205 v.previous (by decide) (by unfold limit; omega)
  obtain ⟨t,run,safe,q⟩:=meta_run native caller P hn hm (limit l) fit
  have empty : ({200,201,202,203,204,205} : Finset (Fin 220)) ∩ written (plan .init) = ∅ := by decide
  have fixed : InputRegs l t := v.transfer (fun _ hi => q.kept_on empty hi)
  refine ⟨t,run,safe,q,fixed,?_,?_,?_,?_,?_,Nat.zero_le _,Nat.zero_le _,Nat.zero_le _,Nat.zero_le _⟩
  · simpa [plan,HeaderPlan.output,capacityExpr_eq,AddressTerm.value,v.height,v.width,v.previous] using q.updated 210
  · simpa [plan,HeaderPlan.output,AddressTerm.value] using q.updated 206
  · simpa [plan,HeaderPlan.output,AddressTerm.value] using q.updated 207
  · simpa [plan,HeaderPlan.output,AddressTerm.value] using q.updated 211
  · simpa [plan,HeaderPlan.output,AddressTerm.value] using q.updated 212

theorem first_range (rev : Bool) (l : Layout h n) (k : ℕ) (hk : k ≤ n) :
    l.out ≤ firstDst rev l.out n k ∧ firstDst rev l.out n k+k*n ≤ l.out+n*n := by
  have eq : (n-k)*n+k*n=n*n := by rw [←Nat.add_mul,Nat.sub_add_cancel hk]
  have kn := Nat.mul_le_mul_right n hk
  cases rev <;> simp only [firstDst,Bool.false_eq_true,↓reduceIte,add_le_add_iff_left,le_refl,true_and] <;> omega

theorem second_range (rev : Bool) (l : Layout h n) (k s : ℕ) (dim : s+k=n) :
    l.out ≤ secondDst rev l.out n k ∧ secondDst rev l.out n k+s*n ≤ l.out+n*n := by
  have eq : s*n+k*n=n*n := by rw [←Nat.add_mul,dim]
  cases rev <;> simp only [secondDst,Bool.false_eq_true,↓reduceIte,add_le_add_iff_left,le_refl,true_and] <;> omega

theorem place_values (rev : Bool) (v : Internal l k s a b m) (q : MetaEffect (.place rev) m t) :
    Internal l k s (firstDst rev l.out n k) (secondDst rev l.out n k) t ∧ t.index 181=firstDst rev l.out n k ∧ t.index 182=k*n := by
  have empty : ({200,201,202,203,204,205,206,207,210} : Finset (Fin 220)) ∩ written (plan (.place rev)) = ∅ := by
    cases rev <;> decide
  have fixed : ∀i : Fin 220,i∈({200,201,202,203,204,205,206,207,210}:Finset (Fin 220))→t.index i=m.index i :=
    fun _ hi => q.kept_on empty hi
  have anchors := v.toInputRegs.transfer (fun i hi=>fixed i ((by decide : ({200,201,202,203,204,205}:Finset (Fin 220)) ⊆ {200,201,202,203,204,205,206,207,210}) hi))
  have ff : t.index 211=firstDst rev l.out n k ∧ t.index 212=secondDst rev l.out n k ∧
      t.index 181=firstDst rev l.out n k ∧ t.index 182=k*n := by
    have read_sub (env : Fin 220 → ℕ) (left right : AddressTerm 220) :
        AddressTerm.value env (left - right) = left.value env - right.value env := rfl
    cases rev <;>
      simpa [plan, firstDst, secondDst, HeaderPlan.output, read_sub, AddressTerm.value, AddressOp.value,
        v.target, v.firstRank, v.width] using
        (And.intro (q.updated 211) (And.intro (q.updated 212) (And.intro (q.updated 181) (q.updated 182))))
  have lr := first_range rev l k v.firstFits
  have sr : secondDst rev l.out n k ≤ l.out+n*n := by
    have kn := Nat.mul_le_mul_right n v.firstFits
    cases rev <;> simp [secondDst]
    omega
  have work:=l.outputRoom
  exact ⟨⟨anchors,(fixed 210 (by decide)).trans v.cap,(fixed 206 (by decide)).trans v.firstRank,
    (fixed 207 (by decide)).trans v.lastRank,ff.1,ff.2.1,v.firstFits,v.lastFits,by omega,sr.trans work⟩,ff.2.2⟩

inductive InPort where | first | residual | last

def InPort.phase : InPort→Phase | .first=>.firstLoad | .residual=>.residualLoad | .last=>.lastLoad
def InPort.rows (port : InPort) (h n k : ℕ) : ℕ := match port with | .first=>h | .residual=>k | .last=>n
def InPort.source (port : InPort) (l : Layout h n) (first : ℕ) : ℕ := match port with | .first=>l.src | .residual=>first | .last=>l.scratch

theorem load_raw (port : InPort) (v : Internal l k s a b m) (q : MetaEffect port.phase m t)
    (A : Matrix (Fin (port.rows h n k)) (Fin n) K) (table : uniformRect (port.rows h n k) n (port.source l a) m=A) :
    RawTapes t (port.source l a) 208 (capacity h n l.previous) (encodedGramInput A) [port.rows h n k,n] := by
  refine ⟨?_,?_,?_,?_,?_,dense_encoded t A ((matrix_frame q.data).trans table),?_⟩
  · cases port <;> simpa [InPort.phase,InPort.source,plan,HeaderPlan.output,AddressTerm.value,v.source,v.firstBase,v.workspace] using q.updated 55
  · rw [length_encodedGramInput A]
    cases port <;> simpa [InPort.rows,InPort.phase,plan,HeaderPlan.output,AddressTerm.value,AddressOp.value,v.height,v.width,v.firstRank] using q.updated 56
  · cases port <;> simpa [InPort.phase,plan,HeaderPlan.output,AddressTerm.value] using q.updated 57
  · cases port <;> simpa [InPort.phase,plan,HeaderPlan.output,AddressTerm.value] using q.updated 58
  · cases port <;> simpa [InPort.phase,plan,HeaderPlan.output,AddressTerm.value,v.cap] using q.updated 60
  · intro j hj
    rcases j with _|j
    · cases port <;> simpa [InPort.rows,InPort.phase,plan,HeaderPlan.output,AddressTerm.value,v.height,v.width,v.firstRank] using q.updated 208
    · rcases j with _|j
      · cases port <;> simpa [InPort.phase,plan,HeaderPlan.output,AddressTerm.value,v.width] using q.updated 209
      · simp at hj

end PairBuilder
end Recovery
end LinearProgramming
end Optimization
end OAI
