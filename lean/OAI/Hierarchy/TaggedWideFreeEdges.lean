import OAI.Computability.VPVNP.LiveHeaderBits
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Logic.Equiv.Prod

namespace OAI
/-! # Ordinary zero-scale switches retain exactly one data word on each private link -/

noncomputable section
namespace Hierarchy.Tagged.WideStack
open scoped Classical BigOperators

variable {E F : Type*} [Fintype E] [CommSemiring F] (used capacity : E→ℕ)
abbrev PrivatePorts := Bool → (e:E)→Fin (capacity e)→Bool

def privateEncode (x : (e:E)→Fin (used e)→Bool) : PrivatePorts capacity :=
  fun _ e j=>if h : j.val<used e then x e ⟨j.val,h⟩ else false

def EqUsed (y : PrivatePorts capacity) := ∀ e (j : Fin (capacity e)),j.val<used e → y false e j=y true e j

def EndsPadded (y : PrivatePorts capacity) :=
  ∀ b e (j : Fin (capacity e)),used e≤j.val → y b e j=false

/-- The product of all actual private prefix-equality switches and the
physical zero suffix tests, for any joint signed site coefficient. -/
theorem private_basis (room : ∀e,used e≤capacity e) (φ : PrivatePorts capacity→F) :
    (∑ y : PrivatePorts capacity,
      (∏e,if ∀ j : Fin (capacity e),j.val<used e → y false e j=y true e j then (1:F) else 0)*
        (if EndsPadded used capacity y then φ y else 0)) =
      ∑ a : (e:E)→Fin (2^(used e)),φ (privateEncode used capacity (fun e j=>(a e).val.testBit j.val)) := by
  classical
  let data := (e:E)→Fin (used e)→Bool
  let read (y : PrivatePorts capacity) : data := fun e j=>y false e (j.castLE (room e))
  have left (a : data) : read (privateEncode used capacity a)=a := by
    funext e j
    change (if _ : j.val<used e then _ else _) = _
    simp [j.isLt]
  let emb : data ↪ PrivatePorts capacity := ⟨privateEncode used capacity,fun x y eqn=>by
    simpa only [left] using congrArg read eqn⟩
  let f (y : PrivatePorts capacity) : F :=
    (if EqUsed used capacity y then 1 else 0)*(if EndsPadded used capacity y then φ y else 0)
  have suffix (a : data) : EndsPadded used capacity (emb a) := by
    intro b e j miss
    change (if _ : j.val<used e then _ else _) = false
    simp [Nat.not_lt.mpr miss]
  have agree (a : data) : EqUsed used capacity (emb a) := fun _ _ _=>rfl
  have recover (y : PrivatePorts capacity) (links : EqUsed used capacity y)
      (canon : EndsPadded used capacity y) : y∈Finset.univ.map emb := by
    refine Finset.mem_map.mpr ⟨read y,Finset.mem_univ _,funext fun b=>funext fun e=>funext fun j=>?_⟩
    change (if _ : j.val<used e then _ else _) = y b e j
    by_cases h : j.val<used e
    · rw [dite_eq_left h]
      change y false e j=y b e j
      cases b
      · rfl
      · exact links e j h
    · rw [dite_eq_right h]
      exact (canon b e j (Nat.le_of_not_gt h)).symm
  have rid (y : PrivatePorts capacity) :
      (∏e,if ∀ j : Fin (capacity e),j.val<used e → y false e j=y true e j then (1:F) else 0) =
        if EqUsed used capacity y then 1 else 0 := by
    rw [Fintype.prod_boole]
    by_cases h : EqUsed used capacity y
    · simp only [ite_eq_left h,ite_eq_left (show ∀e (j:Fin (capacity e)),j.val<used e → y false e j=y true e j from h)]
    · simp only [ite_eq_right h,ite_eq_right (show ¬∀e (j:Fin (capacity e)),j.val<used e → y false e j=y true e j from h)]
  simp_rw [rid]
  change (∑ y,f y) = _
  let bits : ((e:E)→Fin (2^(used e))) ≃ data := Equiv.piCongrRight (fun e=>Computability.VPVNP.RAMSerialization.wordBits (used e))
  calc
    _ = ∑ y∈Finset.univ.map emb,f y := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro y _ missing
      by_cases h : EqUsed used capacity y
      · have miss : ¬EndsPadded used capacity y := fun c=>missing (recover y h c)
        simp [f,miss]
      · simp [f,h]
    _ = ∑ a : data,φ (emb a) := by
      rw [Finset.sum_map]
      apply Finset.sum_congr rfl
      intro a _
      simp [f,agree,suffix]
    _ = ∑ a,φ (emb (bits a)) := (bits.sum_comp (fun a=>φ (emb a))).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      apply congrArg φ
      change privateEncode used capacity (bits a)=_
      apply congrArg (privateEncode used capacity)
      funext e j
      exact (Computability.VPVNP.LiveHeader.testBit_wordBits (a e) j).symm

/-- Closing the positive shorter cuts and ordinary private switches
separately gives exactly the original full physical graph bond sum. -/
theorem partition_words (positive : E→Prop) (width : E→ℕ)
    (φ : ((e:E)→Fin (2^(width e)))→F) :
    (∑ x : (e : {e:E // positive e})→Fin (2^(width e.val)),
      ∑ y : (e : {e:E // ¬positive e})→Fin (2^(width e.val)),
        φ ((Equiv.piEquivPiSubtypeProd positive (fun e=>Fin (2^(width e)))).symm (x,y))) =
      ∑ z,φ z := by
  let split := Equiv.piEquivPiSubtypeProd positive (fun e=>Fin (2^(width e)))
  exact (Fintype.sum_prod_type (fun z=>φ (split.symm z))).symm.trans
    (split.symm.sum_comp φ)

end Hierarchy.Tagged.WideStack

end
end OAI
