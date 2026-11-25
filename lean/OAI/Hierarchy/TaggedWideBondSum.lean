import OAI.Hierarchy.TaggedWideEdgeBasis
import OAI.Hierarchy.TaggedWideFreeEdges

namespace OAI
/-! # The paid shorter-bank and private-switch product has one bond per emitted row -/

set_option maxHeartbeats 1600000
noncomputable section
namespace Hierarchy.Tagged.WideStack
open TaggedShorterBudget ProtocolRAMReportedPorts
open scoped Classical BigOperators

variable {F T : Type*} [CommSemiring F] [Fintype T] {n : ℕ} (key : T ↪ ℕ×ℕ)
  (groups : T→ℕ) (raw : Fin n→ProtocolRAMEmit.Row) (positive : Fin n→Prop)
  (stage : Fin n→ℕ) (w m : ℕ)
set_option quotPrecheck false in
local notation "reported" => fun t:T=>atScale positive stage (key t).1 raw
set_option quotPrecheck false in
local notation "occ" => Occ groups (fun t:T=>(key t).2) reported w m
set_option quotPrecheck false in
local notation "BankBit" => (o : occ) × Fin ((reported o.1 o.2.2.val).width)
set_option quotPrecheck false in
local notation "Free" => {i : Fin n // ¬positive i}
set_option quotPrecheck false in
local notation "used" => fun e : Free=>(raw e.val).width

/-- Fix the equality dictionary actually used in the abstract private basis. -/
private noncomputable def basisDecidable (E : Type*) [Fintype E] : DecidableEq E := inferInstance

/-- Transport the single genuine private-bank identity through an arbitrary
outer finite sum before introducing the price-dependent row subsets. -/
private theorem private_sum {A E : Type*} [Fintype A] [Fintype E] [dec : DecidableEq E]
    (length cap : E→ℕ) (bounded : ∀e,length e≤cap e) (f : A→PrivatePorts cap→F) :
    (∑a:A,∑y : PrivatePorts cap,
      (∏e,if ∀j:Fin (cap e),j.val<length e→y false e j=y true e j then (1:F) else 0)*
        (if EndsPadded length cap y then f a y else 0)) =
      ∑a:A,∑b : (e:E)→Fin (2^length e),f a (privateEncode length cap fun e j=>(b e).val.testBit j.val) := by
  have same : dec=basisDecidable E := Subsingleton.elim _ _
  subst dec
  exact congrArg (fun z : A→F=>∑a:A,z a)
    (funext fun a:A=>private_basis (F:=F) (E:=E) length cap bounded (f a))

/-- Fuse an independent finite partition with the private-bank sum while
the row and bit types are still abstract. -/
private theorem join_partitions {A E Z : Type*} [Fintype A] [Fintype E] [Fintype Z] [DecidableEq E]
    (length cap : E→ℕ) (bounded : ∀e,length e≤cap e)
    (split : Z≃ A × ((e:E)→Fin (2^length e))) (f : A→PrivatePorts cap→F) :
    (∑a:A,∑y : PrivatePorts cap,
      (∏e,if ∀j:Fin (cap e),j.val<length e→y false e j=y true e j then (1:F) else 0)*
        (if EndsPadded length cap y then f a y else 0)) =
      ∑z:Z,f (split z).1 (privateEncode length cap fun e j=>((split z).2 e).val.testBit j.val) := by
  let eval (pair : A × ((e:E)→Fin (2^length e))) :=
    f pair.1 (privateEncode length cap fun e j=>(pair.2 e).val.testBit j.val)
  calc
    _ = ∑a:A,∑b : (e:E)→Fin (2^length e),eval (a,b) :=
      private_sum length cap bounded f
    _ = ∑p : A × ((e:E)→Fin (2^length e)),eval p := (Fintype.sum_prod_type eval).symm
    _ = ∑z:Z,eval (split z) := (split.sum_comp eval).symm

/-- Split the original report before instantiating its geometric paid basis.
This lemma also applies when the retained private rows form the empty type. -/
private theorem join_private {X : Type*} (length : Fin n→ℕ) (P : Fin n→Prop)
    (free : {i : Fin n // ¬P i}→ℕ)
    (bound : ∀i : {i : Fin n // ¬P i},length i.val≤free i)
    (name : ((i : {i : Fin n // P i})→Fin (2^length i.val))→X)
    (φ : X→PrivatePorts free→F) :
    (∑ a : (i : {i : Fin n // P i})→Fin (2^length i.val),∑ y : PrivatePorts free,
      (∏e,if ∀ j : Fin (free e),j.val<length e.val → y false e j=y true e j then (1:F) else 0)*
        (if EndsPadded (fun e=>length e.val) free y then φ (name a) y else 0)) =
      ∑ a : (i:Fin n)→Fin (2^length i),φ (name fun i=>a i.val)
        (privateEncode (fun e=>length e.val) free (fun e j=>(a e.val).val.testBit j.val)) :=
  join_partitions (fun e : {i : Fin n // ¬P i}=>length e.val) free bound
    (Equiv.piEquivPiSubtypeProd P (fun i=>Fin (2^length i))) (fun a=>φ (name a))

/-- The ordinary zero-scale prefix switches and the data bits remaining
after the positive cuts close can appear inside the same signed local
weight. Their joint sum ranges over the original complete report exactly
once, including its zero-width and dormant entries. -/
theorem terminal_bonds (capacity : Free→ℕ) (room : ∀ i,used i≤capacity i)
    (cover : ∀ i,positive i → 0<(raw i).width →
      ∃t, key t=(stage i,widthIndex m ((raw i).width/(w:ℝ))) ∧ (raw i).group<groups t)
    (φ : (BankBit→Bool)→PrivatePorts capacity→F) :
    (∑ x : BankBit→Bool,∑ y : PrivatePorts capacity,
      (∏e,if ∀ j : Fin (capacity e),j.val<used e → y false e j=y true e j then (1:F) else 0)*
          (if EndsPadded used capacity y then φ x y else 0)) =
      ∑ a : (i:Fin n)→Fin (2^(raw i).width),
        φ (fun p=>let q := edgeBit key groups raw positive stage w m p
                  (a q.1.val).val.testBit q.2.val)
          (privateEncode used capacity (fun e j=>(a e.val).val.testBit j.val)) := by
  let action (x : BankBit→Bool) := ∑ y : PrivatePorts capacity,
    (∏e,if ∀ j : Fin (capacity e),j.val<used e → y false e j=y true e j then (1:F) else 0)*
      (if EndsPadded used capacity y then φ x y else 0)
  let read := fun (a : (i : {i : Fin n // positive i})→Fin (2^(raw i.val).width)) (p : BankBit)=>
    let q:=edgeBit key groups raw positive stage w m p
    (a q.1).val.testBit q.2.val
  exact (sum_edge_words key groups raw positive stage w m cover action).trans
    (join_private (fun i=>(raw i).width) positive capacity room read φ)

end Hierarchy.Tagged.WideStack

end
end OAI
