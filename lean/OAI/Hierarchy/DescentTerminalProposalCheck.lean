import OAI.Hierarchy.ProtocolRAMPruneFlag

namespace OAI
/-! # Comparing a shared transpose proposal with actual generated RAM words -/
namespace Hierarchy.DescentTerminalProposalCheck
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {w n out : ℕ}

def compare (a b : Bank) : Expr := .branch .eq (.lookup a .row) (.lookup b .row) (.lit 0) (.lit 1)
def diff (a b : Bank) (m : Memory w) (i : Fin n) : ℕ := if m (a.base+i.val)=m (b.base+i.val) then 0 else 1
def same (a b : Bank) (n : ℕ) (m : Memory w) := ∀i:Fin n,m (a.base+i.val)=m (b.base+i.val)
def after (a b : Bank) (out n : ℕ) (m : Memory w) :=
  fillSegment out (n+1) (SumScores.word out 1 (fun i:Fin n=>diff a b m i)) m
def program (w out n : ℕ) (a b : Bank) := SumScores.procedure w out n 1 (compare a b)

theorem run (a b : Bank) (m : Memory w) (ra : a.Fits w out) (rb : b.Fits w out)
    (na : n≤a.size) (nb : n≤b.size) (fit : out+(n+1)<2^w) :
    (program w out n a b).Exec m (after a b out n m) (4+(n+1)*76) ∧ CheapCode (program w out n a b) := by
  let sc:=fun i:Fin n=>diff a b m i
  have rc : (compare a b).Fits w out:=⟨⟨ra,trivial⟩,⟨rb,trivial⟩,trivial,trivial⟩
  have summ : (∑i,sc i)≤n := calc
    _ ≤ ∑_i:Fin n,1 := Finset.sum_le_sum fun i _=>by unfold sc diff;split <;>decide
    _ = _:=by simp
  have one : 1<2^w:=by have:=ra.1;have:=ra.2.1;omega
  have rd : SumScores.Reads m (compare a b) sc := by
    intro i
    have read (z : Bank) (h:n≤z.size) (hz:z.Fits w out) : z.read m (i.val:Word w)=m (z.base+i.val) := by
      have hi:=i.isLt.trans_le h
      simp [Bank.read,Fin.val_cast_of_lt (hi.trans hz.2.1),Nat.mod_eq_of_lt hi]
    by_cases hit : m (a.base+i.val)=m (b.base+i.val) <;>
      simp [compare,Expr.eval,Comparison.test,read a na ra,read b nb rb,diff,sc,hit]
  have main : (SumScores.procedure w out n 1 (compare a b)).Spec
      (fun μ=>SumScores.Reads μ (compare a b) sc)
      (fun μ after=>after=fillSegment out (n+1) (SumScores.word out 1 sc) μ)
      (4+(n+1)*(42+2*(compare a b).work)) :=
    SumScores.run out 1 (compare a b) sc rc fit one (by omega)
  refine ⟨?_,@PruneFlag.cheap w out n 1 (compare a b)⟩
  intro P R K M pc reg pub exit rom data cfg mem entry eqn
  subst mem
  simpa only [program,after,compare,Expr.work,show 42+2*(7+7+1+1+1)=76 by decide] using
    main M pc reg pub exit rom data cfg m entry rd

theorem flag (a b : Bank) (m : Memory w) :
    after a b out n m (out+n)=(if same a b n m then 0 else 1) := by
  have zero : (∑i:Fin n,diff a b m i)=0 ↔ same a b n m := by
    simp [same,diff,Finset.sum_eq_zero_iff_of_nonneg (fun _ _=>Nat.zero_le _)]
  rw [after,SumScores.read_flag,←zero]
  by_cases empty : (∑i:Fin n,diff a b m i)=0
  · simp [empty]
  · have live : 1≤∑i:Fin n,diff a b m i :=by omega
    simp [live,empty]

theorem frame (a b : Bank) (m : Memory w) {j : ℕ} (low : j<out) : after a b out n m j=m j := by
  simp [after,fillSegment,not_le.mpr low]

/-- Add one finite proposal alphabet to a selector. Only the computably
canonical choice survives for each old history and each supplied payload. -/
def extend {A B T Pay : Type} (decode : Pay→(A→Bool)→Option T) (want : T→Pay→B→Bool)
    (pay : Pay) (z : A⊕B→Bool) : Option T :=
  match decode pay (z∘Sum.inl) with
  | none=>none
  | some h=>if z∘Sum.inr=want h pay then some h else none

theorem extend_iff {A B T Pay : Type} (decode : Pay→(A→Bool)→Option T) (want : T→Pay→B→Bool)
    (pay : Pay) (z : A⊕B→Bool) (t : T) :
    extend decode want pay z=some t ↔ decode pay (z∘Sum.inl)=some t ∧ z∘Sum.inr=want t pay := by
  cases h : decode pay (z∘Sum.inl) with
  | none=>simp [extend,h]
  | some t'=>by_cases right : z∘Sum.inr=want t' pay <;> by_cases e:t'=t <;> simp_all [extend]

theorem extend_unique {A B T Pay : Type} (decode : Pay→(A→Bool)→Option T) (want : T→Pay→B→Bool)
    (unique : ∀p h,∃!a,decode p a=some h) (pay : Pay) (t : T) :
    ∃!z,extend decode want pay z=some t := by
  obtain ⟨a,h,only⟩:=unique pay t
  refine ⟨Sum.elim a (want t pay),(extend_iff ..).2 ⟨h,rfl⟩,?_⟩
  intro z hz
  obtain ⟨old,new⟩:=(extend_iff ..).1 hz
  funext i
  cases i with
  | inl i=>exact congrFun (only _ old) i
  | inr i=>exact congrFun new i

end
end Hierarchy.DescentTerminalProposalCheck

end OAI
