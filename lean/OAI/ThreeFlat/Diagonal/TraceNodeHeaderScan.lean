import OAI.ThreeFlat.Diagonal.TraceNodeCompactCode
import OAI.ThreeFlat.Diagonal.TraceNodeHeaderFields
import OAI.Hierarchy.TraceParentScanner

namespace OAI
/-! # Uniform native compaction of the physical directory into the node-publisher tape -/

namespace ThreeFlat.Diagonal.NavigationPass.TraceNodeHeaders
open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.NavigationNodeRows PhysicalPinsExpr PhysicalProcedure
open scoped Fin.CommRing Classical

/-- Fields 0 and 1 also control the common fixed-trip output instruction. -/
def scanFields (b : Banks) (stages src dst : ℕ) (seed : Layer) : ℕ → ℕ
  | 0 => dst | 1 => 16*(stages+1) | 2 => src | 3 => stages
  | 4 => b.charges | 5 => b.nodes
  | 6 => seed.first | 7 => seed.count | 8 => seed.kind | 9 => seed.childCount
  | 10 => seed.children | 11 => seed.kernels | 12 => seed.incident | _ => 0

def addressedLayer (m : ℕ → ℕ) (src t : ℕ) (seed : Layer) :=
  if t=0 then seed else readLayer m (src+64*(t-1))

def addressedParent (m : ℕ → ℕ) (src stages t : ℕ) : Parent :=
  if t < stages then readParent m (src+64*t) else ⟨true,0,0⟩

def addressedWord (b : Banks) (m : ℕ → ℕ) (src dst stages : ℕ) (seed : Layer)
    (t j : ℕ) := header b (addressedLayer m src t seed) (addressedParent m src stages t)
      (dst+16*(t+1)) j

theorem compactTape_get (b : Banks) (m : ℕ → ℕ) (src dst stages : ℕ)
    (seed : Layer) (t : ℕ) (ht : t≤ stages) (j : Fin 16) :
    (compactTape b m stages src dst seed)[16*t+j.val]? =
      some (addressedWord b m src dst stages seed t j.val) := by
  induction stages generalizing src dst seed t with
  | zero =>
    have : t=0 := by omega
    subst t
    rw [compactTape]
    simp only [Nat.mul_zero,Nat.zero_add,List.getElem?_ofFn,dite_eq_left j.isLt]
    simp [addressedWord,addressedLayer,addressedParent]
  | succ stages ih =>
    let first := List.ofFn (fun d : Fin 16 =>
      header b seed (readParent m src) (dst+16) d.val)
    have len : first.length=16 := List.length_ofFn
    cases t with
    | zero =>
      change (first++_)[16*0+j.val]? = _
      rw [Nat.mul_zero,Nat.zero_add,List.getElem?_append_left (show j.val<first.length by
        rw [len]; exact j.isLt)]
      simp only [first,List.getElem?_ofFn,dite_eq_left j.isLt]
      simp [addressedWord,addressedLayer,addressedParent]
    | succ t =>
      change (first++compactTape b m stages (src+64) (dst+16) (readLayer m src))[16*(t+1)+j.val]? = _
      rw [List.getElem?_append_right (show first.length≤16*(t+1)+j.val by omega),
        show 16*(t+1)+j.val-first.length=16*t+j.val by omega,
        ih _ _ _ t (by omega)]
      unfold addressedWord addressedParent addressedLayer
      have here : src+64+64*t=src+64*(t+1) := by omega
      have out : dst+16+16*(t+1)=dst+16*((t+1)+1) := by omega
      simp only [Nat.add_one_sub_one, Nat.succ_ne_zero, ite_false, Nat.succ_lt_succ_iff,
        here, out]
      cases t with
      | zero => simp
      | succ t => simp [Nat.mul_succ,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

set_option maxHeartbeats 1600000 in
/-- The natural semantics reads only the twelve displayed control words and the two physical rows. -/
theorem compactRow_natural {W ctrl head src dst stages : ℕ} (b : Banks) (m : ℕ → ℕ)
    (seed : Layer) (t : ℕ) (j : Fin 16) (pointer : m ctrl=head)
    (fields : ∀ q < 13, m (head+q) = scanFields b stages src dst seed q) :
    (compactRow ctrl).natural W (fun _=>0) m (fun _=>dst+16*t+j.val) =
      addressedWord b m src dst stages seed t j.val := by
  have hj := j.isLt
  have base : m head=dst := by simpa [scanFields] using fields 0 (by decide)
  have sub : dst+16*t+j.val-dst=16*t+j.val := by omega
  have div : (16*t+j.val)/16=t := by omega
  have mod : (16*t+j.val)%16=j.val := by omega
  by_cases atSeed : t=0 <;> by_cases within : t<stages <;> fin_cases j <;>
    simp [compactRow,pick,MotifRows.field,Formula.natural,natOp,natTest,pointer,
      fields,scanFields,base,div,mod,addressedWord,addressedLayer,addressedParent,
      readLayer,decodeLayer,readParent,decodeParent,nextId,outputCount,header,atSeed,within,
      Nat.add_assoc] <;> split_ifs <;> first | rfl | assumption | contradiction

private theorem pick_fits {W : ℕ} (mem : ℕ → ℕ) (args : Fin 1 → ℕ) (index : E)
    (start : ℕ) (items : List E) (key : index.Fits W (fun _=>0) mem args)
    (keyBound : index.natural W (fun _=>0) mem args < 2^W)
    (range : start+items.length ≤ 2^W) (itemsFit : ∀ x ∈ items, x.Fits W (fun _=>0) mem args) :
    (pick index start items).Fits W (fun _=>0) mem args := by
  induction items generalizing start with
  | nil => trivial
  | cons x xs ih =>
    have first := itemsFit x (List.mem_cons_self ..)
    have rest := ih (start+1) (by simp only [List.length_cons] at range; omega)
      (fun x hx => itemsFit x (List.mem_cons_of_mem _ hx))
    have bound : start < 2^W := by simp only [List.length_cons] at range; omega
    simp [pick, Formula.Fits, Formula.natural, key, keyBound, bound, first, rest]

set_option maxHeartbeats 1600000 in
/-- Addresses and public arithmetic operands of the word scanner fit the target machine. -/
theorem compactRow_fits {W ctrl head src dst stages : ℕ} (b : Banks) (m : ℕ → ℕ) (seed : Layer)
    (t : ℕ) (j : Fin 16) (ht : t≤ stages) (pointer : m ctrl=head)
    (fields : ∀ q<13, m (head+q) = scanFields b stages src dst seed q)
    (word : ∀ x, m x < 2^W) (ctrlFits : ctrl<2^W) (controlFits : head+12<2^W)
    (sourceFits : src+64*stages+44 < 2^W) (targetFits : dst+16*(stages+1)≤2^W) :
    (compactRow ctrl).Fits W (fun _=>0) m (fun _=>dst+16*t+j.val) := by
  have hj := j.isLt
  have base : m head=dst := by simpa [scanFields] using fields 0 (by decide)
  have srcField : m (head+2)=src := fields 2 (by decide)
  have stageField : m (head+3)=stages := fields 3 (by decide)
  have here : dst+16*t+j.val < 2^W := by omega
  have sub : dst+16*t+j.val-dst=16*t+j.val := by omega
  have div : (16*t+j.val)/16=t := by omega
  have mod : (16*t+j.val)%16=j.val := by omega
  have srcBound (p : ℕ) (hp : p ≤ 44) : src+64*t+p<2^W := by omega
  have prevBound (p : ℕ) (hp : p ≤ 44) : src+64*(t-1)+p<2^W := by omega
  have outCount (x : ℕ) : m x / 5 < 2^W := (Nat.div_le_self ..).trans_lt (word x)
  have wide : W ≠ 0 := by
    rintro rfl
    norm_num at sourceFits
  have positive : t<2^W := by omega
  have headBound (q : ℕ) (hq : q≤12) : head+q<2^W := by omega
  have hp : head<2^W := by omega
  have dp : dst<2^W := by omega
  have relative : 16*t+j.val<2^W := by omega
  have digits : 16<2^W := by omega
  have five : 5<2^W := by omega
  have stagesBound : stages<2^W := by omega
  have jBound : j.val<2^W := by omega
  unfold compactRow
  apply pick_fits
  · simp [Formula.Fits,Formula.natural,MotifRows.field,opFits,natOp,pointer,base,sub]; omega
  · simp [Formula.natural,MotifRows.field,pointer,base,natOp,sub,mod]; omega
  · simp; omega
  · simp only [List.forall_mem_cons]
    by_cases atSeed : t=0 <;> by_cases within : t<stages <;>
      simp (disch := omega) [Formula.Fits,Formula.natural,MotifRows.field,opFits,
        natOp,natTest,pointer,base,sub,div,srcField,stageField,word,outCount,
        srcBound,prevBound,ctrlFits,here,positive,headBound,hp,dp,relative,digits,
        five,stagesBound,jBound,Nat.div_eq_of_lt hj,atSeed,within] <;>
      (repeat' first | apply And.intro | intro) <;> omega

end ThreeFlat.Diagonal.NavigationPass.TraceNodeHeaders

end OAI
