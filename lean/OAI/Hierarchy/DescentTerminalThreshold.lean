import OAI.ThreeFlat.Routing.TypedWiring
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Log

namespace OAI
/-! # All binary cutoff comparisons on a row with linearly many trivalent gates -/

namespace Hierarchy.DescentTerminalThreshold
open ThreeFlat ThreeFlat.Routing
open scoped Classical BigOperators
noncomputable section

abbrev Flag (k : ℕ) := (d : Fin (k+1)) × Fin (2^d.val)
abbrev Pin (k word : ℕ) := Fin k ⊕ Fin word
abbrev Row (k word : ℕ) := Flag k ⊕ Fin word

variable {F : Type*} [CommSemiring F] {k word : ℕ}

private def index (a : Flag k) (live : a.1.val≠0) : Fin k := ⟨a.1.val-1,by have := a.1.isLt;omega⟩

private def parent (a : Flag k) : Flag k :=
  ⟨⟨a.1.val-1,by have := a.1.isLt;omega⟩,⟨a.2.val % 2^(a.1.val-1),Nat.mod_lt _ (Nat.two_pow_pos _)⟩⟩

private def high (a : Flag k) := decide (2^(a.1.val-1)≤a.2.val)

private def gate (a : Flag k) (digit previous : Bool) : Bool :=
  if high a then !digit || previous else !digit && previous

private def expected (digits : Fin k→Bool) (h : Flag k→Bool) (a : Flag k) : Bool :=
  if live : a.1.val≠0 then gate a (digits (index a live)) (h (parent a)) else true

def flags (q : ℕ) (a : Flag k) : Bool := decide (q % 2^a.1.val≤a.2.val)

private theorem flags_step (q : ℕ) (a : Flag k) :
    flags q a=expected (fun j=>q.testBit j.val) (flags q) a := by
  rcases a with ⟨⟨d,hd⟩,j⟩
  cases d with
  | zero=>simp [expected,flags,Nat.mod_one]
  | succ t=>
    let S:=2^t
    have hs : 0<S:=Nat.two_pow_pos _
    have jlt : j.val<2*S := by simpa [S,pow_succ,Nat.mul_comm] using j.isLt
    have low : q%S<S:=Nat.mod_lt _ hs
    change decide (q%2^(t+1)≤j.val)=_
    rw [Nat.mod_pow_succ]
    simp only [expected,gate,high,index,parent,flags,Nat.succ_sub_one,Fin.val_mk,Nat.testBit_eq_decide_div_mod_eq,decide_eq_true_eq]
    change decide (q%S+S*(q/S%2)≤j.val) =
      (if S≤j.val then !(decide (q/S%2=1)) || decide (q%S≤j.val%S)
       else !(decide (q/S%2=1)) && decide (q%S≤j.val%S))
    rcases Nat.mod_two_eq_zero_or_one (q/S) with even|odd
    · by_cases H:S≤j.val
      · simp [H,even]; omega
      · simp [H,even,Nat.mod_eq_of_lt (Nat.lt_of_not_ge H)]
    · by_cases H:S≤j.val
      · have rem : j.val%S=j.val-S := by
          rw [Nat.mod_eq_sub_mod H,Nat.mod_eq_of_lt (by omega)]
        simp [H,rem,odd]; omega
      · simp [H,odd]; omega

private theorem unique (q : ℕ) (h : Flag k→Bool)
    (law : ∀a,h a=expected (fun j=>q.testBit j.val) h a) : h=flags q := by
  funext a
  generalize eqn : a.1.val=d
  induction d using Nat.strong_induction_on generalizing a with
  | h d ih=>
    rw [law a,flags_step q a]
    by_cases zero : a.1.val=0
    · simp [expected,zero]
    · have lower : (parent a).1.val<d := by change a.1.val-1<d;omega
      simp only [expected,dite_eq_left zero,ih _ lower (parent a) rfl]

private def last (fit : word≤2^k) (j : Fin word) : Flag k := ⟨Fin.last k,j.castLE (by simpa using fit)⟩

private def wires (fit : word≤2^k) : Row k word→Fin 3→Pin k word ⊕ Flag k
  | .inl a=>if live : a.1.val≠0 then ![.inr a,.inl (.inl (index a live)),.inr (parent a)]
      else fun _=>.inr a
  | .inr j=>![.inr (last fit j),.inl (.inr j),.inl (.inr j)]

private def table (leaf : Bool→Bool→F) : Row k word→(Fin 3→Bool)→F
  | .inl a,x=>if x 0=(if a.1.val≠0 then gate a (x 1) (x 2) else true) then 1 else 0
  | .inr _,x=>leaf (x 0) (x 1)

private def primitive (f : (Fin 3→Bool)→F) : BitNetwork F (Fintype.card (Fin 3)) where
  internal:=0
  cells:=1
  source _ j:=.pin (Fintype.equivFin _ j)
  table _:=f

private theorem primitive_value (f : (Fin 3→Bool)→F) (x : Fin 3→Bool) :
    TypedWiring.value (primitive f) x=f x := by
  unfold TypedWiring.value BitNetwork.eval BitNetwork.weight BitNetwork.factor
  simp only [primitive, BitSource.read, Equiv.symm_apply_apply]
  change (∑ _ : Fin 0 → Bool, ∏ _ : Fin 1, f x) = f x
  have empty (a : F) : (∑ _ : Fin 0 → Bool, a) = a := by
    simp [Finset.sum_const]
  rw [empty, Fin.prod_univ_one]

def network (fit : word≤2^k) (leaf : Bool→Bool→F) : BitNetwork F (Fintype.card (Pin k word)) :=
  TypedWiring.glue (fun a=>primitive (table leaf a)) (wires fit)

private def reading (fit : word≤2^k) (leaf : Bool→Bool→F)
    (q : ℕ) (pay : Fin word→Bool) (h : Flag k→Bool) : Row k word→F
  | .inl a=>if h a=expected (fun j=>q.testBit j.val) h a then 1 else 0
  | .inr j=>leaf (h (last fit j)) (pay j)

theorem network_value (fit : word≤2^k) (leaf : Bool→Bool→F) (q : ℕ) (cap : q<2^k) (pay : Fin word→Bool) :
    TypedWiring.value (network fit leaf) (Sum.elim (fun j=>q.testBit j.val) pay)=
      ∏j : Fin word,leaf (decide (q≤j.val)) (pay j) := by
  let : DecidableEq (Flag k) := fun a b => Classical.propDecidable (a=b)
  let x:=Sum.elim (fun j : Fin k=>q.testBit j.val) pay
  have factor (h : Flag k→Bool) (r : Row k word) :
      TypedWiring.value (primitive (table leaf r)) (fun i=>Sum.elim x h (wires fit r i)) =
        reading fit leaf q pay h r := by
    rw [primitive_value]
    rcases r with a|j
    · by_cases l : a.1.val≠0 <;> simp [wires,table,reading,expected,l,x]
    · simp [wires,table,reading,x]
  rw [network,TypedWiring.glue_value]
  change (∑h : Flag k→Bool,∏r : Row k word,
    TypedWiring.value (primitive (table leaf r)) (fun i=>Sum.elim x h (wires fit r i)))=_
  simp only [factor]
  rw [Finset.sum_eq_single_of_mem (flags q) (Finset.mem_univ _) (fun h _ neq=>?_)]
  · rw [Fintype.prod_sum_type]
    have checks : (∏a : Flag k,reading fit leaf q pay (flags q) (.inl a))=1 := by
      apply Finset.prod_eq_one
      intro a _
      exact ite_eq_left (flags_step q a)
    rw [checks,one_mul]
    apply Finset.prod_congr rfl
    intro j _
    change leaf (flags q (last fit j)) _=leaf _ _
    simp [flags,last,Nat.mod_eq_of_lt cap]
  · have witness : ∃a,h a≠expected (fun t=>q.testBit t.val) h a := by
      by_contra! law
      exact neq (unique q h law)
    obtain ⟨a,wrong⟩ := witness
    exact Finset.prod_eq_zero (Finset.mem_univ (Sum.inl a)) (by simp [reading,wrong])

private theorem count_levels (n : ℕ) : (∑d : Fin n,2^d.val)+1=2^n := by
  induction n with
  | zero=>simp
  | succ n ih=>rw [Fin.sum_univ_castSucc];simp only [Fin.val_last,Fin.val_castSucc,pow_succ];omega

theorem flag_count (k : ℕ) : Fintype.card (Flag k)+1=2^(k+1) := by
  simpa [Flag,Fintype.card_sigma] using count_levels (k+1)

theorem network_size (fit : word≤2^k) (leaf : Bool→Bool→F) :
    (network fit leaf).cells+(network fit leaf).internal=Fintype.card (Flag k)*2+word := by
  simp [network,primitive,Row,Fintype.card_sum,Nat.mul_two,Nat.add_comm,Nat.add_left_comm]

def depth (word : ℕ) := word.log2+1

theorem depth_room (word : ℕ) : word<2^depth word := by
  by_cases zero : word=0
  · simp [zero,depth]
  · exact (Nat.log2_lt zero).mp (Nat.lt_succ_self _)

theorem depth_size {word : ℕ} (positive : 0<word) : 2^depth word≤2*word := by
  rw [depth,pow_succ,Nat.mul_comm]
  exact Nat.mul_le_mul_left _ ((Nat.le_log2 positive.ne').mp le_rfl)

theorem linear (leaf : Bool→Bool→F) (positive : 0<word) :
    let A:=network (depth_room word).le leaf
    A.cells+A.internal≤9*word := by
  dsimp only
  rw [network_size]
  have count:=flag_count (depth word)
  rw [pow_succ] at count
  have cap:=depth_size positive
  omega

end
end Hierarchy.DescentTerminalThreshold

end OAI
