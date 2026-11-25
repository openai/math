import OAI.Hierarchy.DescentExteriorCoefficient

namespace OAI
/-! # Combining a genuine selected history with the two physical proposal planes -/
namespace Hierarchy.DescentExteriorShelf
open DescentExterior DescentGL Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open scoped Classical Fin.CommRing
noncomputable section
variable {w e j r t : ℕ} {A T : Type}
local notation "D" => Hidden e j r t
local notation "k" => j+(j+r)
local notation "n" => e*2^(j+r)

/-- The proposal pins and the earlier history pins occupy disjoint
parts of one auxiliary Boolean assignment. -/
def proposed (decode : (A→Bool)→Option T) (layout : T→Fin e→Layout k)
    (x : Fin e→Plane j r→Fin t→Bool) (all : A⊕D→Bool) : Option T :=
  (decode (all∘Sum.inl)).bind fun h=>
    if all∘Sum.inr=canonical (layout h) x then some h else none

theorem proposed_eq (decode : (A→Bool)→Option T) (layout : T→Fin e→Layout k)
    (x : Fin e→Plane j r→Fin t→Bool) (all : A⊕D→Bool) (h : T) :
    proposed decode layout x all=some h ↔
      decode (all∘Sum.inl)=some h ∧ all∘Sum.inr=canonical (layout h) x := by
  cases old : decode (all∘Sum.inl) with
  | none=>simp [proposed,old]
  | some q=>
    by_cases same : q=h
    · subst q
      by_cases right : all∘Sum.inr=canonical (layout h) x <;> simp [proposed,old,right]
    · by_cases right : all∘Sum.inr=canonical (layout q) x <;> simp [proposed,old,right,same]

theorem proposed_unique (decode : (A→Bool)→Option T) (layout : T→Fin e→Layout k)
    (x : Fin e→Plane j r→Fin t→Bool) (single : ∀h,∃! a,decode a=some h) (h : T) :
    ∃! all,proposed decode layout x all=some h := by
  obtain ⟨a,ha,once⟩:=single h
  refine ⟨Sum.elim a (canonical (layout h) x),(proposed_eq ..).mpr ⟨ha,rfl⟩,?_⟩
  intro z hit
  obtain ⟨o,v⟩:=(proposed_eq ..).mp hit
  funext i
  cases i with
  | inl a'=>exact congrFun (once _ o) a'
  | inr d=>exact congrFun v d

theorem flag_present (origin : ℕ) (M : Fin e→Layout k) (x : Fin e→Plane j r→Fin t→Bool)
    (z : D→Bool) (m : Memory w) (rc : Receipt origin M x z m) (bad : z≠canonical M x) :
    ∃s : Fin 2,∃i : Fin n,∃b : Fin w,
      (m (start j r t e origin+s.val*n+i.val)).val.testBit b.val=true := by
  obtain ⟨s,fail⟩:=not_forall.mp (fun all=>bad (rc.1.mp all))
  obtain ⟨i,word⟩:=not_forall.mp fail
  refine ⟨s,i,?_⟩
  by_contra! no
  apply word
  apply (wordBits w).injective
  funext b
  rw [←Computability.VPVNP.LiveHeader.testBit_wordBits,←Computability.VPVNP.LiveHeader.testBit_wordBits]
  have h:=no b
  simpa using h

theorem rejected (origin : ℕ) (decode : (A→Bool)→Option T) (layout : T→Fin e→Layout k)
    (x : Fin e→Plane j r→Fin t→Bool) (z : A⊕D→Bool) (m : Memory w) (h : T)
    (prior : decode (z∘Sum.inl)=some h) (rc : Receipt origin (layout h) x (z∘Sum.inr) m)
    (bad : proposed decode layout x z=none) :
    ∃s : Fin 2,∃i : Fin n,∃b : Fin w,
      (m (start j r t e origin+s.val*n+i.val)).val.testBit b.val=true := by
  apply flag_present origin (layout h) x (z∘Sum.inr) m rc
  intro good
  have e:=(proposed_eq decode layout x z h).mpr ⟨prior,good⟩
  rw [bad] at e
  contradiction

end
end Hierarchy.DescentExteriorShelf

end OAI
