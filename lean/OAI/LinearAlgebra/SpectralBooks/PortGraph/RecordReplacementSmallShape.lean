import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementDecoder
import OAI.LinearAlgebra.SpectralBooks.PortGraph.MapType

/-! # Numbered replacement ports and the single-role template

The tag in a catalogue port determines one replacement. Within that
replacement the port is exactly one of the internal incidences or one of
the attached old stubs. For a one-vertex replacement only the stubs occur.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
open scoped Classical
namespace PortGraph.ReplacementTemplate

/-- Internal ports and attached stubs, with the catalogue tag omitted. -/
abbrev LocalPort (t : ReplacementTemplate) (v : t.Role) :=
  t.graph.Port v ⊕ {s : t.Stub // t.attach s = v}

variable {J : Type*} (T : J → ReplacementTemplate)

/-- Reinserting the catalogue tag in a port of one replacement. -/
def tagPort (j : J) (v : (T j).Role) : LocalPort (T j) v → RolePort T ⟨j,v⟩
  | .inl p => ⟨.inl (⟨j,p.val.1⟩,p.val.2), congrArg (Sigma.mk j) p.property⟩
  | .inr s => ⟨.inr ⟨j,s.val⟩, congrArg (Sigma.mk j) s.property⟩

private theorem tagPort_bijective (j : J) (v : (T j).Role) : Function.Bijective (tagPort T j v) := by
  constructor
  · rintro (p|s) (q|t) h
    · have e := Sum.inl.inj (congrArg Subtype.val h)
      have hw := (Sigma.mk.inj_iff.mp (congrArg Prod.fst e)).2.eq
      have hb := congrArg (fun z : (Σ j, (T j).Wire) × Bool => z.2) e
      exact congrArg Sum.inl (Subtype.ext (Prod.ext hw hb))
    · have hh := congrArg Subtype.val h
      contradiction
    · have hh := congrArg Subtype.val h
      contradiction
    · exact congrArg Sum.inr (Subtype.ext (Sigma.mk.inj_iff.mp (Sum.inr.inj (congrArg Subtype.val h))).2.eq)
  · rintro ⟨(⟨⟨k,e⟩,b⟩ | ⟨k,s⟩), h⟩
    · obtain rfl : k = j := congrArg Sigma.fst h
      exact ⟨.inl ⟨(e,b),(Sigma.mk.inj_iff.mp h).2.eq⟩,rfl⟩
    · obtain rfl : k = j := congrArg Sigma.fst h
      exact ⟨.inr ⟨s,(Sigma.mk.inj_iff.mp h).2.eq⟩,rfl⟩

/-- The interface between a catalogue coefficient and a table on one template. -/
def localPortEquiv (a : Σ j, (T j).Role) : RolePort T a ≃ LocalPort (T a.1) a.2 :=
  (Equiv.ofBijective (tagPort T a.1 a.2) (tagPort_bijective T a.1 a.2)).symm

@[simp] theorem localPortEquiv_symm_apply (j : J) (v : (T j).Role) (p : LocalPort (T j) v) :
    (localPortEquiv T ⟨j,v⟩).symm p = tagPort T j v p := rfl

/-- Direction of a local incidence, including the saved old polarity on stubs. -/
def localSide (t : ReplacementTemplate) {v : t.Role} : LocalPort t v → Bool :=
  Sum.elim (fun p => p.val.2) (fun s => t.direction s.val)

@[simp] theorem localPortEquiv_side (a : Σ j, (T j).Role) (p : RolePort T a) :
    localSide (T a.1) (localPortEquiv T a p) = side T p.val := by
  obtain ⟨p,rfl⟩ := (localPortEquiv T a).symm.surjective p
  rw [Equiv.apply_symm_apply]
  cases p <;> rfl

/-- Combine the fixed local numberings of a mixed catalogue into the
port-number lookup used by the replacement decoder. -/
def catalogueNumbering (slot : (a : Σ j, (T j).Role) → LocalPort (T a.1) a.2 ↪ Fin 4) :
    Numbering T := fun a => (localPortEquiv T a).toEmbedding.trans (slot a)

variable {B : Type} (direction : B → Bool)

private def singleGraph : PortGraph Unit Empty := ⟨Empty.elim, Empty.elim⟩

private def singleTree : RootedTreeData singleGraph () where
  edge := {
    toFun v := (v.property (Subsingleton.elim _ _)).elim
    invFun := Empty.elim
    left_inv v := (v.property (Subsingleton.elim _ _)).elim
    right_inv e := nomatch e }
  side _ := false
  at_child v := (v.property (Subsingleton.elim _ _)).elim
  depth _ := 0
  toward_root v := (v.property (Subsingleton.elim _ _)).elim

/-- The direct term of a patch with at most three stubs. Its only role
holds the entire open tensor and every stub retains its old polarity. -/
def singleRole : ReplacementTemplate.{0,0,0} where
  Role := Unit
  Wire := Empty
  Stub := B
  graph := singleGraph
  root := ()
  tree := singleTree
  attach _ := ()
  direction := direction

instance : Fintype (singleRole direction).Role := inferInstanceAs (Fintype Unit)
instance : Fintype (singleRole direction).Wire := inferInstanceAs (Fintype Empty)
instance [Fintype B] : Fintype (singleRole direction).Stub := inferInstanceAs (Fintype B)

@[simp] theorem single_direction (s : B) : (singleRole direction).direction s = direction s := rfl

theorem single_role_count {b : ℕ} (hb : b ≤ 3) :
    Fintype.card (singleRole direction).Role = max 1 (b-2) := by
  change Fintype.card Unit = _
  rw [Fintype.card_unit]
  omega

/-- Every incident port of the single role is one specified exterior stub. -/
def singlePortEquiv (v : Unit) : LocalPort (singleRole direction) v ≃ B where
  toFun
    | .inl p => nomatch p.val.1
    | .inr s => s.val
  invFun s := .inr ⟨s,show () = v from Subsingleton.elim _ _⟩
  left_inv
    | .inl p => nomatch p.val.1
    | .inr _ => rfl
  right_inv _ := rfl

/-- Number the stub ports in their prescribed linear order. -/
def singleNumbering {b : ℕ} (order : B ≃ Fin b) (v : Unit) :
    LocalPort (singleRole direction) v ≃ Fin b := (singlePortEquiv direction v).trans order

@[simp] theorem singleNumbering_stub {b : ℕ} (order : B ≃ Fin b) (v : Unit)
    (s : {s : B // (singleRole direction).attach s = v}) :
    singleNumbering direction order v (.inr s) = order s.val := rfl

/-- This vertex owns the mark exactly when the old patch contained the root. -/
def singleRoleType {b : ℕ} (order : B ≃ Fin b) (hb : b ≤ 3) (marked : Bool) : MapType where
  degree := ⟨b, by omega⟩
  root := marked
  direction i := direction (order.symm i)

@[simp] theorem singleRoleType_root {b : ℕ} (order : B ≃ Fin b) (hb : b ≤ 3) (marked : Bool) :
    (singleRoleType direction order hb marked).root = marked := rfl

@[simp] theorem singleRoleType_direction {b : ℕ} (order : B ≃ Fin b) (hb : b ≤ 3) (marked : Bool)
    (s : B) : (singleRoleType direction order hb marked).direction (order s) = direction s := by
  exact congrArg direction (order.symm_apply_apply s)

end PortGraph.ReplacementTemplate

end

end SpectralBooks
end LinearAlgebra
end OAI
