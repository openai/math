import OAI.Computability.BorderVNP.CellCQFTabStepCost
import OAI.Computability.BorderVNP.CellCQFIterationCost
import OAI.Computability.BorderVNP.CellCQFPrimitiveCosts

/-! # Pointwise cost of the native indexed table generator

The state contains the actual environment, unary loop index and accumulated
output list. We bound the lengths of those reached prefixes and charge the body
at each of the indices actually requested by the caller.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace StackProcedure

open _root_.OAI.ExactQuantumFactoring _root_.OAI.ExactQuantumFactoring.BitStackProgram
open _root_.OAI.ExactQuantumFactoring.BitStackProgram.Procedure

variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → ℕ → β}

/-- An upper bound on the environment, index and stored-prefix sizes. -/
def tabSpan (ea : α → List Bool) (n : ℕ) (a : α) (L : ℕ) :=
  (ea a).length+n+(n+1)*(L+1)+1

private theorem list_prefix {n L : ℕ} (a : α) (h : ∀ i < n, (eb (f a i)).length ≤ L) {i : ℕ} (hi : i ≤ n) :
    (listCode eb (((List.range i).map (f a)).reverse)).length ≤ 2*tabSpan ea n a L := by
  rw [listCode_length_rev]
  have hh := listCode_length_map_bound eb (f a) (List.range i) L
    (fun k hk => h k ((List.mem_range.mp hk).trans_le hi))
  rw [List.length_range] at hh
  have h' := Nat.mul_le_mul_right (L+1) hi
  dsimp [tabSpan]
  rw [Nat.succ_mul n (L+1)]
  rw [show 2*L+2=2*(L+1) by omega,Nat.mul_left_comm i 2] at hh
  omega

private theorem iterated (i : ℕ) (a : α) :
    (tabStep f)^[i] (0,a,[]) = (i,a,((List.range i).map (f a)).reverse) := by
  simp only [tabStep_iterate,Nat.zero_add,List.append_nil,List.range_eq_range']

private theorem iterate_tab_bound (p : Procedure (prodCode unaryCode ea) eb (fun x => f x.2 x.1))
    (q : Polynomial ℕ) (growth) (n : ℕ) (a : α) {L C : ℕ}
    (hL : ∀ i < n, (eb (f a i)).length ≤ L) (hC : ∀ i < n, p.cost (i,a) ≤ C) :
    ((tabStepP p).iterate q growth).cost (n,0,a,[]) ≤ 10^50*(n+1)*(C+tabSpan ea n a L) := by
  let S := tabSpan ea n a L
  have hs : (ea a).length+n+L+1 ≤ S := by
    dsimp [S,tabSpan]; rw [Nat.succ_mul]; omega
  have span (i : ℕ) (hi : i ≤ n) : (tabCode ea eb ((tabStep f)^[i] (0,a,[]))).length ≤ 5*S := by
    rw [iterated]
    have := list_prefix (ea := ea) a hL hi
    simp only [tabCode,prodCode,pairBits_length,unaryCode,List.length_replicate]
    change _ ≤ 2*S at this
    omega
  have step (i : ℕ) (hi : i < n) : (tabStepP p).cost ((tabStep f)^[i] (0,a,[])) ≤ 10^47*(C+S) := by
    rw [iterated]
    apply ((cost_le_meter ..).trans (meter_tabStepP ..)).trans
    have hlist := list_prefix (ea := ea) a hL hi.le
    change _ ≤ 2*S at hlist
    have hc := hC i hi
    have hl := hL i hi
    simp only [meter,prodCode,pairBits_length,unaryCode,List.length_replicate]
    omega
  have hh := cost_iterate (tabStepP p) q growth n (0,a,[]) span step
  have h₀ := span 0 (Nat.zero_le _)
  rw [Function.iterate_zero_apply] at h₀
  apply hh.trans
  have hs' : n+1 ≤ S := by omega
  have hu : 10^47*(C+S)+8*(5*S)+5 ≤ 10^49*(C+S) := by omega
  have hu' := Nat.mul_le_mul_left n hu
  change _ ≤ 10^50*(n+1)*(C+S)
  rw [Nat.mul_right_comm (10^50) (n+1) (C+S),Nat.mul_succ (10^50*(C+S)) n]
  rw [Nat.mul_comm n (10^49*(C+S)), Nat.mul_assoc (10^49) (C+S) n] at hu'
  rw [Nat.mul_assoc (10^50) (C+S) n]
  omega

private noncomputable def tabOuter {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → ℕ → β}
    (p : Procedure (prodCode unaryCode ea) eb (fun x => f x.2 x.1)) (q : Polynomial ℕ) (growth) (d : β) :=
  let inputN := first unaryCode ea
  let inputA := second unaryCode ea
  let start := (constant (prodCode unaryCode ea) unaryCode 0).pair
    (inputA.pair (constant (prodCode unaryCode ea) (listCode eb) []))
  let rep := (tabStepP p).iterate q growth
  let result := ((second ea (listCode eb)).comp (second unaryCode (prodCode ea (listCode eb)))).comp
    (rep.comp (inputN.pair start))
  (listReverse eb d).comp result

set_option maxHeartbeats 2000000 in
private theorem outer_bound (p : Procedure (prodCode unaryCode ea) eb (fun x => f x.2 x.1))
    (q : Polynomial ℕ) (growth) (d : β) (n : ℕ) (a : α) {L C : ℕ}
    (hL : ∀ i < n, (eb (f a i)).length ≤ L) (hC : ∀ i < n, p.cost (i,a) ≤ C) :
    (tabOuter p q growth d).meter (n,a) ≤
      10^75*((listReverse eb d).bound.eval 1+1)*(n+1)*(C+(tabSpan ea n a L)^2+1) := by
  let S := tabSpan ea n a L
  let R := (listReverse eb d).bound.eval 1
  let V := C+S^2+1
  let lc := listCode eb
  let enc := prodCode unaryCode ea
  let inpN := first unaryCode ea
  let inpA := second unaryCode ea
  let z := constant enc unaryCode 0
  let nil := constant enc lc []
  let pairA := inpA.pair nil
  let start := z.pair pairA
  let init := inpN.pair start
  let rep := (tabStepP p).iterate q growth
  let go := rep.comp init
  let get1 := second unaryCode (prodCode ea lc)
  let get2 := second ea lc
  let get := get2.comp get1
  let result := get.comp go
  let rev := listReverse eb d
  let out := ((List.range n).map (f a)).reverse
  have hspan : (ea a).length+n+1 ≤ S := by dsimp [S,tabSpan]; omega
  have hl := list_prefix (ea := ea) a hL (le_rfl : n ≤ n)
  change (lc out).length ≤ 2*S at hl
  have h₁ := meter_first unaryCode ea (n,a)
  have h₂ := meter_second unaryCode ea (n,a)
  have hz := meter_constant enc unaryCode 0 (n,a)
  have hn := meter_constant enc lc [] (n,a)
  have hp := meter_pair inpA nil (n,a)
  have hst := meter_pair z pairA (n,a)
  have hinit := meter_pair inpN start (n,a)
  have hiter := iterate_tab_bound p q growth n a hL hC
  have hgo := meter_comp rep init (n,a)
  have hfirst := meter_second unaryCode (prodCode ea lc) (n,a,out)
  have hsecond := meter_second ea lc (a,out)
  have hget := meter_comp get2 get1 (n,a,out)
  have hresult := meter_comp get go (n,a)
  have hrev := cost_listReverse eb d out
  have htop := meter_comp rev result (n,a)
  have his : rep.meter (n,0,a,[]) ≤ 10^50*(n+1)*(C+S)+12*S := by
    let e := prodCode unaryCode (tabCode ea eb)
    have he : (e (n,0,a,[])).length ≤ 5*S := by
      simp only [e,tabCode,prodCode,pairBits_length,unaryCode,List.length_replicate]
      change 2*n+(2*0+(2*(ea a).length+1+1)+1)+1 ≤ 5*S
      omega
    have hv : (tabCode ea eb ((tabStep f)^[n] (0,a,[]))).length ≤ 6*S := by
      rw [iterated]
      simp only [tabCode,prodCode,pairBits_length,unaryCode,List.length_replicate]
      change (listCode eb (((List.range n).map (f a)).reverse)).length ≤ 2*S at hl
      omega
    unfold meter
    apply (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hiter he) hv) 1).trans
    change 10^50*(n+1)*(C+S)+5*S+6*S+1 ≤ 10^50*(n+1)*(C+S)+12*S
    omega
  change inpN.meter (n,a) ≤ _ at h₁
  change inpA.meter (n,a) ≤ _ at h₂
  change z.meter (n,a) ≤ _ at hz
  change nil.meter (n,a) ≤ _ at hn
  change pairA.meter (n,a) ≤ _ at hp
  change start.meter (n,a) ≤ _ at hst
  change init.meter (n,a) ≤ _ at hinit
  change go.meter (n,a) ≤ 6*(init.meter (n,a)+rep.meter (n,0,a,[])) at hgo
  change get1.meter (n,a,out) ≤ _ at hfirst
  change get2.meter (a,out) ≤ _ at hsecond
  change get.meter (n,a,out) ≤ 6*(get1.meter (n,a,out)+get2.meter (a,out)) at hget
  have he : (tabStep f)^[n] (0,a,[]) = (n,a,out) := iterated ..
  change result.meter (n,a) ≤ 6*(go.meter (n,a)+get.meter ((tabStep f)^[n] (0,a,[]))) at hresult
  rw [he] at hresult
  change (rev.comp result).meter (n,a) ≤ 6*(result.meter (n,a)+rev.meter (((tabStep f)^[n] (0,a,[])).2.2)) at htop
  rw [he] at htop
  change (rev.comp result).meter (n,a) ≤ 6*(result.meter (n,a)+rev.meter out) at htop
  have hsmall : S ≤ V := by have h : S ≤ S^2 := Nat.le_self_pow (by decide) S; dsimp [V]; omega
  have hV : C+S ≤ V := by have h : S ≤ S^2 := Nat.le_self_pow (by decide) S; dsimp [V]; omega
  have hRV : rev.meter out ≤ 10*(R+1)*V := by
    have hsq : ((lc out).length+1)^2 ≤ (2*S+1)^2 := Nat.pow_le_pow_left (by omega) 2
    have : (2*S+1)^2 ≤ 9*V := by dsimp [V]; nlinarith only [Nat.zero_le C, Nat.zero_le (S^2), (Nat.le_self_pow (by decide : 2 ≠ 0) S)]
    have hh := hrev.trans (Nat.mul_le_mul_left R (hsq.trans this))
    unfold meter
    change rev.cost out + (lc out).length + (listCode eb out.reverse).length + 1 ≤ _
    rw [listCode_length_rev eb out]
    dsimp [lc] at hl
    change rev.cost out ≤ R*(9*V) at hh
    change (listCode eb out).length ≤ 2*S at hl
    change rev.cost out + (listCode eb out).length + (listCode eb out).length + 1 ≤ _
    have hp : 1 ≤ V := by dsimp [V]; omega
    nlinarith only [hh,hl,hsmall,Nat.zero_le (R*V),hp]
  have hgeom : (n+1)*(C+S) ≤ (R+1)*(n+1)*V := by
    calc _ ≤ (n+1)*V := Nat.mul_le_mul_left _ hV
         _ ≤ _ := Nat.mul_le_mul_right V (Nat.le_mul_of_pos_left _ (by omega))
  have hscale : V ≤ (R+1)*(n+1)*V := Nat.le_mul_of_pos_left _ (by positivity)
  have hscaleR : (R+1)*V ≤ (R+1)*(n+1)*V := Nat.mul_le_mul_right V (Nat.le_mul_of_pos_right _ (by omega))
  change (rev.comp result).meter (n,a) ≤ 10^75*(R+1)*(n+1)*V
  rw [Nat.mul_assoc (10^75) (R+1) (n+1), Nat.mul_assoc]
  simp only [enc,lc,prodCode,pairBits_length,unaryCode,List.length_replicate, show (listCode eb []).length = 1 by rfl] at h₁ h₂ hz hn hfirst hsecond
  change (listCode eb out).length ≤ 2*S at hl
  rw [Nat.mul_assoc] at his hRV
  clear hrev hiter
  omega

/-- Actual native tabulation time is polynomial in the table dimensions and
output widths, and linear in the actual bound on a single visited subroutine. -/
theorem cost_tabulate (d : β) (p : Procedure (prodCode unaryCode ea) eb (fun x => f x.2 x.1))
    (n : ℕ) (a : α) {L C : ℕ} (hL : ∀ i < n, (eb (f a i)).length ≤ L)
    (hC : ∀ i < n, p.cost (i,a) ≤ C) :
    (tabulate d p).cost (n,a) ≤ 10^75*((listReverse eb d).bound.eval 1+1)*(n+1)*(C+(tabSpan ea n a L)^2+1) := by
  apply (cost_le_meter ..).trans
  unfold tabulate
  rw [meter_congrFun]
  exact outer_bound p _ _ d n a hL hC

end StackProcedure

end BorderVNP
end Computability

namespace ExactQuantumFactoring.BitStackProgram.Procedure

export OAI.Computability.BorderVNP.StackProcedure (
  tabSpan
  cost_tabulate)

end ExactQuantumFactoring.BitStackProgram.Procedure
end OAI
