import OAI.Hierarchy.DescentPackedScore
import OAI.Hierarchy.DescentFirstMinimumRAM

namespace OAI
/-! # The compact public score ledger for candidate-dependent packed short fields -/

namespace Hierarchy.DescentPackedMinimum
open DescentSIMDLookup DescentPackedScore ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing Classical BigOperators
noncomputable section
attribute [local irreducible] Procedure.Exec
variable {a M H r w q : ℕ}

structure Layout (q : ℕ) where
  source : Fin q→Bank
  dictionary : Fin q→Bank
  work : ℕ
  ledger : Bank
  result : ℕ

structure Fits (L : Layout q) (w a M H r : ℕ) : Prop where
  rows : ∀i,H*chunks r M ≤ (L.source i).size
  fields : ∀i,(L.dictionary i).bits=a*M
  source : ∀i,(L.source i).Fits w L.work
  dictionary : ∀i,(L.dictionary i).Fits w L.work
  workspace : L.work+(H*chunks r M+1)≤L.ledger.base
  capacity : q≤L.ledger.size
  ledger : L.ledger.Fits w L.result
  room : L.result+q<2^w
  word : 1<2^w

def fetch (base n : ℕ) : Expr :=
  if n=0 then .lit 0 else .lookup ⟨base+(n-1),0⟩ (.lit 0)

def copy (L : Layout q) (w n : ℕ) (i : Fin q) :=
  scan w (L.ledger.base+i.val) 1 (fetch L.work n)

def program (L : Layout q) (w H r M : ℕ) : List (Fin q)→Procedure w
  | []=>scan w L.work 0 (.lit 0)
  | i::is=>((program L w H r M is).seq
      (raw (L.source i) (L.dictionary i) L.work 0 H r M w)).seq (copy L w (H*chunks r M) i)

def cost (base n : ℕ) : ℕ := (4+(n+1)*66)+(4+1*(2*(fetch base n).work+4))

def scores (f : Fin q→Cell a→ℕ) (x : Fin q→Fin H→Fin r→Cell a) (i : Fin q) :=
  ∑v,∑j,f i (x i v j)

def memory {M : ℕ} (L : Layout q) (f : Fin q→Cell a→ℕ) (x : Fin q→Fin H→Fin r→Cell a) (m : Memory w) :
    List (Fin q)→Memory w
  | []=>m
  | i::is=>
    let before:=memory (M:=M) L f x m is
    let saved:= fillSegment L.work (H*chunks r M+1) (SumScores.word L.work 0 (terms (M:=M) (f i) (x i))) before
    fillSegment (L.ledger.base+i.val) 1 (fun _=>(scores f x i:Word w)) saved

private theorem low (L : Layout q) (bounds : Fits L w a M H r) (f : Fin q→Cell a→ℕ)
    (x : Fin q→Fin H→Fin r→Cell a) (m : Memory w) (is : List (Fin q)) {u : ℕ} (hu : u<L.work) :
    memory (M:=M) L f x m is u=m u := by
  induction is with
  | nil=>rfl
  | cons i is ih=>
    have sep:=bounds.workspace
    simp [memory,fillSegment,Nat.not_le_of_gt hu,show ¬L.ledger.base+i.val≤u by omega,ih]

private theorem load (L : Layout q) (_bounds : Fits L w a M H r) (f : Fin q→Cell a→ℕ)
    (zf : ∀i,f i 0=0) (x : Fin q→Fin H→Fin r→Cell a) (pos : 0<M)
    (m : Memory w) (i : Fin q) (idx : Word w) :
    (fetch L.work (H*chunks r M)).eval
      (fillSegment L.work (H*chunks r M+1) (SumScores.word L.work 0 (terms (M:=M) (f i) (x i))) m)
      idx=(scores f x i:Word w) := by
  let n:=H*chunks r M
  have all := total (f i) (zf i) (x i) pos
  by_cases empty : n=0
  · have none : (∑j,terms (M:=M) (f i) (x i) j)=0 := by
      apply Finset.sum_eq_zero
      intro j _
      have impossible : j.val<n:=j.isLt
      omega
    have zero : scores f x i=0:= all.symm.trans none
    simp [fetch,show H*chunks r M=0 from empty,Expr.eval,zero]
  · let j : Fin (H*chunks r M):=⟨n-1,by change n-1<n;omega⟩
    have endAt : j.val+1=n := by change n-1+1=n;omega
    have readout:=SumScores.read_prefix L.work 0 (terms (M:=M) (f i) (x i)) m j
    rw [endAt,SumScores.total_all,all] at readout
    simpa [fetch,show H*chunks r M≠0 from empty,Expr.eval,Bank.read,Bank.size,j,n,scores] using readout

theorem issue (L : Layout q) (bounds : Fits L w a M H r) (f : Fin q→Cell a→ℕ)
    (x : Fin q→Fin H→Fin r→Cell a) (m : Memory w) (zero : ∀i,f i 0=0) (positive : 0<M)
    (sumFits : ∀i,scores f x i<2^w)
    (ready : ∀i,Input (M:=M) (L.source i) (L.dictionary i) (f i) (x i) m) (is : List (Fin q)) :
    (program L w H r M is).Exec m (memory (M:=M) L f x m is) (4+is.length*cost L.work (H*chunks r M)) := by
  induction is with
  | nil=>
    have go:=scan_exec L.work 0 (.lit 0) m trivial (by have:=bounds.workspace;have:=bounds.ledger.2.2;have:=bounds.room;omega)
    have same : image L.work 0 (.lit 0) m=m := by funext u;simp [image,fillSegment]
    simpa [program,memory,same] using go
  | cons i is ih=>
    let n:=H*chunks r M
    let before:=memory (M:=M) L f x m is
    let written:=fillSegment L.work (n+1) (SumScores.word L.work 0 (terms (M:=M) (f i) (x i))) before
    have span:=bounds.workspace
    have ledger:=bounds.ledger.2.2
    have room:=bounds.room
    have ix:=i.isLt.trans_le bounds.capacity
    have resident : Input (M:=M) (L.source i) (L.dictionary i) (f i) (x i) before := by
      constructor
      · intro p
        rw [show before ((L.source i).base+(row H r M p).val)=m _ from low _ bounds _ _ _ _
            (by have:=(row H r M p).isLt.trans_le (bounds.rows i);have:=(bounds.source i).2.2;omega)]
        exact (ready i).input p
      · intro key
        rw [show before ((L.dictionary i).base+key.val)=m _ from low _ bounds _ _ _ _
            (by have sz : key.val<(L.dictionary i).size:=by simp [Bank.size,bounds.fields i]
                have:=(bounds.dictionary i).2.2;omega)]
        exact (ready i).table key
    have collect:=DescentPackedScore.run (L.source i) (L.dictionary i) L.work 0 (f i) (x i) before
      (zero i) positive (bounds.source i) (bounds.dictionary i) (bounds.rows i) (bounds.fields i) (by omega)
      (by omega) (sumFits i) resident
    have fits : (fetch L.work n).Fits w (L.ledger.base+i.val) := by
      unfold fetch
      split
      · trivial
      · refine ⟨⟨by simp [Bank.size],by simpa [Bank.size] using bounds.word,?_⟩,trivial⟩
        change L.work+(n-1)+1≤L.ledger.base+i.val
        dsimp [n] at *;omega
    have cp:=scan_exec (L.ledger.base+i.val) 1 (fetch L.work n) written fits (by omega)
    have copyEq : image (L.ledger.base+i.val) 1 (fetch L.work n) written=
        fillSegment (L.ledger.base+i.val) 1 (fun _=>(scores f x i:Word w)) written := by
      funext u
      simp only [image,fillSegment]
      split
      · exact load L bounds f zero x positive before i _
      · rfl
    rw [copyEq] at cp
    have clock : (4+is.length*cost L.work n+(4+(n+1)*66))+(4+1*(2*(fetch L.work n).work+4))=
        4+(i::is).length*cost L.work n := by simp [cost,List.length_cons];ring
    rw [←clock]
    exact (ih.then collect).then cp

theorem entries (L : Layout q) (bounds : Fits L w a M H r) (f : Fin q→Cell a→ℕ)
    (x : Fin q→Fin H→Fin r→Cell a) (m : Memory w) (is : List (Fin q)) (i : Fin q) (mem : i∈is) :
    memory (M:=M) L f x m is (L.ledger.base+i.val)=(scores f x i:Word w) := by
  induction is with
  | nil=>simp at mem
  | cons j js ih=>
    by_cases eq : i=j
    · subst i;simp [memory,fillSegment]
    · have distinct : i.val≠j.val:=fun h=>eq (Fin.ext h)
      have sep:=bounds.workspace
      have low : ¬(L.ledger.base+j.val≤L.ledger.base+i.val ∧ L.ledger.base+i.val<L.ledger.base+j.val+1) := by omega
      simp only [memory,fillSegment,ite_eq_right low]
      rw [ite_eq_right (by omega)]
      exact ih ((List.mem_cons.mp mem).resolve_left eq)

def scoreAt (f : Fin q→Cell a→ℕ) (x : Fin q→Fin H→Fin r→Cell a) (j : ℕ) : ℕ :=
  if h : j<q then scores f x ⟨j,h⟩ else 0

def search (L : Layout q) (w H r M : ℕ) :=
  (program L w H r M (List.finRange q)).seq (DescentFirstMinimumRAM.code w L.result L.ledger (List.range q))

theorem minimum (L : Layout q) (bounds : Fits L w a M H r) (f : Fin q→Cell a→ℕ)
    (x : Fin q→Fin H→Fin r→Cell a) (m : Memory w) (zero : ∀i,f i 0=0) (positive : 0<M)
    (sumFits : ∀i,scores f x i<2^w)
    (ready : ∀i,Input (M:=M) (L.source i) (L.dictionary i) (f i) (x i) m) {j s : ℕ}
    (winner : (DescentColonies.scanMinimum (scoreAt f x) (List.range q)).1=some (j,s)) :
    ∃after, (search L w H r M).Exec m after
       ((4+q*cost L.work (H*chunks r M))+DescentFirstMinimumRAM.ticks L.result L.ledger (List.range q)) ∧
       after (L.result+(q-1))=(j:Word w) ∧ ∀u<L.work,after u=m u := by
  let ledger:=memory (M:=M) L f x m (List.finRange q)
  have run:=issue L bounds f x m zero positive sumFits ready (List.finRange q)
  have select:=DescentFirstMinimumRAM.exec L.ledger ledger (List.range q) bounds.ledger (by simpa using bounds.room) bounds.word
  have words (k : ℕ) (hk : k∈List.range q) : ledger (L.ledger.base+k)=(scoreAt f x k:Word w) := by
    let i : Fin q:=⟨k,List.mem_range.mp hk⟩
    have out:=entries L bounds f x m (List.finRange q) i (List.mem_finRange i)
    simpa only [ledger,scoreAt,dite_eq_left (List.mem_range.mp hk)] using out
  refine ⟨_,by simpa [search,ledger] using run.then select,?_,?_⟩
  · simpa only [List.length_range] using DescentFirstMinimumRAM.winner L.ledger ledger (scoreAt f x) (List.range q) bounds.ledger
      (fun k hk=>(List.mem_range.mp hk).trans_le bounds.capacity) words
      (fun k hk=>by simpa [scoreAt,List.mem_range.mp hk] using sumFits ⟨k,List.mem_range.mp hk⟩) winner
  · intro u hu
    rw [DescentFirstMinimumRAM.frame _ _ _ _ _ (by have:=bounds.workspace;have:=bounds.ledger.2.2;omega)]
    exact low L bounds f x m _ hu

theorem bit_price (L : Layout q) (w a H r : ℕ) (positive : 0<a) (wide : 2*a≤w) :
    ((4+q*cost L.work (H*chunks r (lanes w a)))+DescentFirstMinimumRAM.ticks L.result L.ledger (List.range q))*w
      ≤ 200*(q+1)*(w+H*w+4*H*r*a) := by
  let n:=H*chunks r (lanes w a)
  have packed:= (invoice H r w a positive wide).1
  have pick:=DescentFirstMinimumRAM.length_budget L.result L.ledger (List.range q)
  rw [List.length_range] at pick
  have get : (fetch L.work n).work≤6 := by unfold fetch;split <;> simp [Expr.work]
  let B:=w+H*w+4*H*r*a
  have word_le : w≤B := by dsimp [B];omega
  have priced : cost L.work n*w ≤ 90*B := by
    have extra : (4+1*(2*(fetch L.work n).work+4))*w≤20*w := Nat.mul_le_mul_right _ (by omega)
    calc
      _ = (4+(n+1)*66)*w+(4+1*(2*(fetch L.work n).work+4))*w := by simp only [cost,Nat.add_mul]
      _ ≤ 70*B+20*B := Nat.add_le_add packed (extra.trans (Nat.mul_le_mul_left 20 word_le))
      _ = _ := by ring
  calc
    _ ≤ (4+q*cost L.work n)*w+(4+70*q)*w := by
      rw [Nat.add_mul];exact Nat.add_le_add_left (Nat.mul_le_mul_right w pick) _
    _ = 4*w+q*(cost L.work n*w)+(4+70*q)*w := by ring
    _ ≤ 4*B+q*(90*B)+(4+70*q)*B := Nat.add_le_add
      (Nat.add_le_add (Nat.mul_le_mul_left 4 word_le) (Nat.mul_le_mul_left q priced))
      (Nat.mul_le_mul_left _ word_le)
    _ = (8+160*q)*B := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (by omega)

end
end Hierarchy.DescentPackedMinimum

end OAI
