import OAI.Hierarchy.DescentPackedOperand

namespace OAI
/-! Encoding a captured donor by its measured walk rank and an inherited donor by
its compressed resident rank preserves equality of all live private words. -/
namespace Hierarchy.DescentOrdinaryNativeNames
open DescentPackedOperand
open scoped Classical
noncomputable section
variable {U : Type} {d n:ℕ} (old:U↪Fin d) (newName:U↪Fin n)

def renumber (a:ℕ) : ℕ :=
  if found:∃u,(old u).val=a then (newName found.choose).val else n+a

theorem renumber_at (u:U) : renumber old newName (old u).val=(newName u).val :=by
  have found:∃t,(old t).val=(old u).val:=⟨u,rfl⟩
  rw [renumber,dite_eq_left found,old.injective (Fin.ext found.choose_spec)]

def donorEmbedding : ℕ↪ℕ where
  toFun:=renumber old newName
  inj':=by
    intro a b eqn
    by_cases fa:∃u,(old u).val=a
    · obtain ⟨u,rfl⟩:=fa
      rw [renumber_at] at eqn
      by_cases fb:∃v,(old v).val=b
      · obtain ⟨v,rfl⟩:=fb
        rw [renumber_at] at eqn
        exact congrArg (fun t=>(old t).val) (newName.injective (Fin.ext eqn))
      · rw [renumber,dite_eq_right fb] at eqn
        have:= (newName u).isLt
        omega
    · rw [renumber,dite_eq_right fa] at eqn
      by_cases fb:∃v,(old v).val=b
      · obtain ⟨v,rfl⟩:=fb
        rw [renumber_at] at eqn
        have:= (newName v).isLt
        omega
      · rw [renumber,dite_eq_right fb] at eqn
        omega

def captures (root:ℕ↪ℕ) : Key↪Key where
  toFun
    | .first d v s k=>.first (root d) v s k
    | .second d v s k=>.second (root d) v s k
    | other=>other
  inj':=by
    intro x y equal
    cases x <;> cases y <;> simp_all [root.injective.eq_iff]

theorem capture_fields (root:ℕ↪ℕ) (x:Key) : ((captures root) x).fields 0=x.fields 0 := by
  cases x <;> rfl

theorem captured_root (native:ℕ↪ℕ) (cut:Bool) (root peer seat piece:ℕ) :
    captures native ((if cut then Key.second else Key.first) root peer seat piece)=
      (if cut then Key.second else Key.first) (native root) peer seat piece :=by
  cases cut <;> rfl

theorem capture_at (cut:Bool) (u:U) (peer seat piece:ℕ) :
    captures (donorEmbedding old newName) ((if cut then Key.second else Key.first) (old u).val peer seat piece)=
      (if cut then Key.second else Key.first) (newName u).val peer seat piece :=by
  exact (captured_root (donorEmbedding old newName) cut (old u).val peer seat piece).trans
    (congrArg (fun d => (if cut then Key.second else Key.first) d peer seat piece)
      (renumber_at old newName u))

end
end Hierarchy.DescentOrdinaryNativeNames

end OAI
