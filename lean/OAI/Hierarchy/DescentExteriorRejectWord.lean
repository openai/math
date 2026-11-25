import OAI.Hierarchy.DescentExteriorChoice
import OAI.Hierarchy.ProtocolRAMPruneFlag

namespace OAI
/-! # One zero coefficient authenticates every native exterior proposal -/
namespace Hierarchy.DescentExteriorRejectWord
open DescentExteriorShelf DescentExterior DescentGL Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section

def indicator (flag : Bank) : Expr := .branch .eq (.lookup flag .row) (.lit 0) (.lit 0) (.lit 1)

def mismatch {w n : ℕ} (flag : Bank) (mem : Memory w) (i : Fin n) : ℕ :=
  if mem (flag.base+i.val)=0 then 0 else 1

theorem failed {w n : ℕ} (flag : Bank) (m : Memory w) :
    (∑i:Fin (2*n),mismatch flag m i)=0 ↔ ∀s : Fin 2,∀i : Fin n,m (flag.base+s.val*n+i.val)=0 := by
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _=>Nat.zero_le _)]
  have char (i : Fin (2*n)) : mismatch flag m i=0 ↔ m (flag.base+i.val)=0 := by
    by_cases val : m (flag.base+i.val)=0 <;>simp [mismatch,val]
  simp only [Finset.mem_univ,true_implies,char]
  constructor
  · intro all s i
    have got:=all (finProdFinEquiv (s,i))
    change m (flag.base+(i.val+n*s.val))=0 at got
    convert got using 2; ring
  · intro all u
    obtain ⟨⟨s,i⟩,rfl⟩:=finProdFinEquiv.surjective u
    change m (flag.base+(i.val+n*s.val))=0
    convert all s i using 2;ring

theorem run {w n : ℕ} (flag : Bank) (out : ℕ) (safe : flag.Fits w out) (span : 2*n≤flag.size)
    (room : out+(2*n+1)<2^w) :
    (SumScores.procedure w out (2*n) 1 (indicator flag)).Spec (fun _=>True)
      (fun m dst=> (dst (out+2*n)=if ∀s:Fin 2,∀i:Fin n,m (flag.base+s.val*n+i.val)=0 then 0 else 1) ∧
        ∀u<out,dst u=m u) (4+(2*n+1)*64) ∧ CheapCode (SumScores.procedure w out (2*n) 1 (indicator flag)) := by
  refine ⟨?_,@PruneFlag.cheap w out (2*n) 1 (indicator flag)⟩
  intro P R V machine pc reg pub exit inst «public» cfg m entry _
  let s : Fin (2*n)→ℕ:=mismatch flag m
  have bill : (∑i,s i)≤2*n := by
    calc
      _≤∑_i:Fin (2*n),1:=Finset.sum_le_sum fun i _=>by unfold s mismatch;split <;>decide
      _=2*n:=by simp
  have fit : (indicator flag).Fits w out := ⟨⟨safe,trivial⟩,trivial,trivial,trivial⟩
  have one : (1:ℕ)<2^w := by have:=safe.1;have:=safe.2.1;omega
  have reads : SumScores.Reads m (indicator flag) s := by
    intro i
    have bits := i.isLt.trans_le span
    have addr : flag.read m (i.val:Word w)=m (flag.base+i.val) := by
      simp [Bank.read,Fin.val_cast_of_lt (bits.trans safe.2.1),Nat.mod_eq_of_lt bits]
    by_cases hz : m (flag.base+i.val)=0 <;>
      simp [indicator, Expr.eval, DescriptorExpr.Comparison.test, beq_iff_eq, addr, s, mismatch, hz]
  obtain ⟨cnt,time,z,dst,adv,done,eq⟩:=
    SumScores.run out 1 (indicator flag) s fit room one (by omega)
      machine pc reg pub exit inst «public» cfg m entry reads
  refine ⟨cnt,by simpa [indicator,Expr.work] using time,z,dst,adv,done,?_,?_⟩
  · rw [eq,SumScores.read_flag]
    by_cases zero : (∑i,s i)=0
    · rw [ite_eq_right (show ¬1≤∑i,s i by omega),ite_eq_left ((failed (n:=n) flag m).mp zero)]
    · rw [ite_eq_left (show 1≤∑i,s i by omega),ite_eq_right (fun all=>zero ((failed (n:=n) flag m).mpr all))]
  · intro u low
    simp [eq,fillSegment,Nat.not_le_of_gt low]

/-- The entire physical flag block contributes a single zero scalar raised
to the one-bit failure exponent emitted by the checked prefix procedure. -/
theorem aggregate_weight {F : Type} [CommSemiring F] {w n : ℕ} (start : ℕ)
    (m : Memory w) (word : Word w) (one : 1<2^w)
    (emitted : word=if ∀s:Fin 2,∀i:Fin n,m (start+s.val*n+i.val)=0 then 0 else 1) :
    (0:F)^word.val=guard (F:=F) n start m := by
  rw [guard_value,emitted]
  by_cases ok : ∀s:Fin 2,∀i:Fin n,m (start+s.val*n+i.val)=0
  · rw [ite_eq_left ok,ite_eq_left ok]
    simp
  · have v : (1:Word w).val=1 := by
      change 1 % (2^w)=1
      exact Nat.mod_eq_of_lt one
    rw [ite_eq_right ok,ite_eq_right ok,v,pow_one]

theorem single_factor {F : Type} [CommSemiring F] {w e j r t : ℕ} (origin : ℕ)
    (M : Fin e→Layout (j+(j+r))) (x : Fin e→Plane j r→Fin t→Bool)
    (zs : (Hidden e j r t→Bool)→Memory w)
    (receipt : ∀z,Receipt origin M x z (zs z))
    (flag : (Hidden e j r t→Bool)→Word w) (one : 1<2^w) (room : 2^j*t≤w)
    (emit : ∀z,flag z=if ∀s:Fin 2,∀i:Fin (e*2^(j+r)),
      zs z (start j r t e origin+s.val*(e*2^(j+r))+i.val)=0 then 0 else 1)
    (rest : (Fin e→Plane j r→Fin t→Bool)→F) :
    (∑z,(0:F)^(flag z).val*rest (observed origin (zs z)))=
      rest (fun a v=>x a (coords j r ((M a).symm ((coords j r).symm v)))) := by
  have each (z : Hidden e j r t→Bool) :
      (0:F)^(flag z).val=guard (F:=F) (e*2^(j+r)) (start j r t e origin) (zs z) :=
    aggregate_weight (F:=F) (start j r t e origin) (zs z) (flag z) one (emit z)
  simp_rw [each]
  exact contraction origin room M x zs receipt rest

end
end Hierarchy.DescentExteriorRejectWord

end OAI
