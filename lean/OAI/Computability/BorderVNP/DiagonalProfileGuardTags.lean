import OAI.Computability.BorderVNP.DiagonalSiteTagRead
import OAI.Computability.BorderVNP.PackedInheritedProfileValue

/-! # Local tagged observation fiber for a profile selector or terminal -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.InheritedProfile

open Crossing Packing.Inherited BankSite CellSparse Diagonal.CellEntries
open private bits_left bits_right from OAI.Computability.BorderVNP.PackedInheritedStaging
open private exterior read_inputs from OAI.Computability.BorderVNP.PackedInheritedProfileValue
open scoped Classical

/-- A field and a tagged table with the same Boolean indicator agree on success, and
the passing tagged indicator has zero scalar multiplicity at every position. -/
theorem guard_agrees {K Param Gadget : Type*} [Field K] (check : Prop) [Decidable check] :
    let f := if check then (1 : K) else 0
    let z := if check then (1 : Entry Param Gadget) else 0
    (f = 1 ↔ z ≠ 0) ∧ ∀ a, (counters z).2 a = 0 := by
  by_cases h : check <;> simp only [h,ite_true,ite_false,ne_eq,zero_ne_one,one_ne_zero,
    not_false_eq_true,not_true_eq_false,eq_self,iff_self,true_and]
  all_goals intro a; rfl

/-- Read a guard on the actual incident and exterior inputs. Its unique work vector
depends only on those inputs. Its successful native report is empty. -/
theorem guard_tag_read {D ne np : ℕ} {P K Param Gadget : Type} [Fintype P] [Field K]
    {bits : P → ℕ} (N : Network D P bits) (v : N.Site)
    (aux : N.Site → ℕ) (rows : N.Edge ↪ Fin ne) (ports : P ↪ Fin np)
    (site : Site) (work : site.work = aux v) (inc : site.incoming = incoming N v)
    (noLoop : ∀ z : Incident N v, N.src z.val ≠ N.dst z.val)
    (table : N.Tables K) (target : N.Assignment → Fin site.work → Bool)
    (observe : ∀ ext bank,
      let y := (cellView N aux bank).wires rows ports v
      site.observe bank = if (fun k : Fin site.work => bank k.val) = target y ∧
        N.read table y ext v = 1 then some [] else none)
    (z : ∀ c : Incident N v, Fin (N.width c.val) → Bool)
    (x : ∀ a : Attached N v, Fin (bits a.val) → Bool)
    (tag : Entry Param Gadget) (number : Gadget ↪ ℕ)
    (agree : (table v z x = 1 ↔ tag ≠ 0) ∧ ∀ a, (counters tag).2 a = 0) :
    Nonempty (site.TagRead (inputWords N rows ports v z x ∘ Fin.cast inc) (fun _ => True) tag number) := by
  let raw := inputWords N rows ports v z x
  let inp := raw ∘ Fin.cast inc
  let zero := fun _ : Fin (aux v) => false
  let base := Inherited.bits zero raw
  let y := (cellView N aux base).wires rows ports v
  let ext := exterior N v x
  have ht : N.read table y ext v = table v z x := read_inputs N rows ports v aux noLoop zero z x table
  refine ⟨⟨target y,[],trivial,?_,?_⟩⟩
  · intro g os _
    let b := Inherited.bits g inp
    have hw : (cellView N aux b).wires rows ports v = y := by
      apply view_wires_eq N v aux rows ports noLoop b base
      intro i
      calc
        b (aux v+i.val) = b (site.work+(Fin.cast inc.symm i).val) := congrArg b (by rw [work]; rfl)
        _ = inp (Fin.cast inc.symm i) := bits_right g inp _
        _ = raw i := rfl
        _ = base (aux v+i.val) := (bits_right zero raw i).symm
    have hg : (fun i : Fin site.work => b i.val) = g := funext (bits_left g inp)
    have h := observe ext b
    dsimp only at h
    rw [hw,hg,ht,agree.1] at h
    change site.observe b = some os ↔ _
    rw [h]
    by_cases ok : g = target y ∧ tag ≠ 0
    · simp [ok,eq_comm]
    · rw [ite_eq_right ok]
      simp only [reduceCtorEq,false_iff]
      tauto
  · intro _ a
    rw [agree.2 a]
    rfl

end Packing.InheritedProfile

end BorderVNP
end Computability
end OAI
