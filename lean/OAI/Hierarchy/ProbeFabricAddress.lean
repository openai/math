import OAI.Hierarchy.ProbePayloadFabric

namespace OAI
/-! # Stage and port coordinates for the columns of a recursively joined permutation fabric -/
namespace Hierarchy.ProbeStage
noncomputable section

abbrev Shape.Socket (s : Shape) := s.Group × (Fin s.span ⊕ Fin s.span)
abbrev Fabric.SocketKey := ℕ × (Σ s : Shape, s.Socket)

def Fabric.shiftSocket (offset : ℕ) (k : Fabric.SocketKey) : Fabric.SocketKey :=
  (offset+k.1,k.2)

def Fabric.socketKey : {X Y : Type} → (f : Fabric X Y) → f.Column → Fabric.SocketKey
  | _,_,.step s => fun (c : s.shape.Port ⊕ s.shape.Port) =>
    match c with
    | .inl (g,i) => (0,⟨s.shape,g,.inl i⟩)
    | .inr (g,o) => (0,⟨s.shape,g,.inr o⟩)
  | _,_,.seq a b => fun (c : a.Column ⊕ b.Column) =>
    match c with
    | .inl i => a.socketKey i
    | .inr i => shiftSocket a.shapes.length (b.socketKey i)

theorem Fabric.socket_stage_lt {X Y : Type} (f : Fabric X Y) (c : f.Column) :
    (f.socketKey c).1 < f.shapes.length := by
  induction f with
  | step s => rcases c with ⟨_,_⟩|⟨_,_⟩ <;> exact Nat.zero_lt_succ 0
  | seq a b ia ib =>
    cases c with
    | inl u =>
      simpa only [socketKey,shapes,List.length_append] using
        (Nat.lt_of_lt_of_le (ia u) (Nat.le_add_right _ b.shapes.length))
    | inr v =>
      simpa only [socketKey,shiftSocket,shapes,List.length_append] using
        (Nat.add_lt_add_left (ib v) a.shapes.length)

theorem Fabric.socketKey_injective {X Y : Type} (f : Fabric X Y) : Function.Injective f.socketKey := by
  induction f with
  | step s =>
    rintro (⟨g,i⟩|⟨g,i⟩) (⟨h,j⟩|⟨h,j⟩) e <;>
      have pair := congrArg Prod.snd e <;> dsimp only [socketKey] at pair <;>
      have slots := eq_of_heq (Sigma.mk.inj_iff.mp pair).2
    · exact congrArg Sum.inl (Prod.ext (congrArg (fun z : s.shape.Socket=>z.1) slots) (Sum.inl.inj (congrArg Prod.snd slots)))
    · exact (Sum.inl_ne_inr (congrArg Prod.snd slots)).elim
    · exact (Sum.inr_ne_inl (congrArg Prod.snd slots)).elim
    · exact congrArg Sum.inr (Prod.ext (congrArg (fun z : s.shape.Socket=>z.1) slots) (Sum.inr.inj (congrArg Prod.snd slots)))
  | seq a b ia ib =>
    rintro (u|v) (u'|v') e
    · exact congrArg Sum.inl (ia e)
    · have n:=congrArg Prod.fst e
      change (a.socketKey u).1=a.shapes.length+(b.socketKey v').1 at n
      have:=a.socket_stage_lt u
      omega
    · have n:=congrArg Prod.fst e
      change a.shapes.length+(b.socketKey v).1=(a.socketKey u').1 at n
      have:=a.socket_stage_lt u'
      omega
    · apply congrArg Sum.inr
      apply ib
      have he:=congrArg Prod.fst e
      have hz:=congrArg Prod.snd e
      change a.shapes.length+(b.socketKey v).1=a.shapes.length+(b.socketKey v').1 at he
      change (b.socketKey v).2=(b.socketKey v').2 at hz
      exact Prod.ext (Nat.add_left_cancel he) hz

theorem Fabric.exists_socket {X Y : Type} (f : Fabric X Y) (i : ℕ) (s : Shape)
    (hs : f.shapes[i]?=some s) (z : s.Socket) :
    ∃ c : f.Column, f.socketKey c=(i,⟨s,z⟩) := by
  induction f generalizing i s with
  | step node =>
    cases i with
    | zero =>
      obtain rfl : node.shape=s := Option.some.inj hs
      rcases z with ⟨g,u|v⟩
      · exact ⟨.inl (g,u),rfl⟩
      · exact ⟨.inr (g,v),rfl⟩
    | succ i => simp [shapes] at hs
  | seq a b ia ib =>
    change (a.shapes++b.shapes)[i]?=some s at hs
    by_cases left : i<a.shapes.length
    · rw [List.getElem?_append_left left] at hs
      obtain ⟨c,eq⟩:=ia i s hs z
      exact ⟨.inl c,eq⟩
    · rw [List.getElem?_append_right (Nat.le_of_not_gt left)] at hs
      obtain ⟨c,eq⟩:=ib _ s hs z
      refine ⟨.inr c,?_⟩
      change shiftSocket a.shapes.length (b.socketKey c)=_
      rw [eq]
      exact Prod.ext (by dsimp [shiftSocket];omega) rfl

abbrev Fabric.FlatColumns {X Y : Type} (f : Fabric X Y) :=
  Σ t : Fin f.shapes.length, (f.shapes.get t).Socket

def Fabric.flatKey {X Y : Type} (f : Fabric X Y) (z : f.FlatColumns) : Fabric.SocketKey :=
  (z.1.val,⟨_,z.2⟩)

theorem Fabric.flatKey_injective {X Y : Type} (f : Fabric X Y) : Function.Injective f.flatKey := by
  rintro ⟨t,u⟩ ⟨s,v⟩ eq
  have ts : t=s := Fin.ext (congrArg Prod.fst eq)
  subst s
  exact congrArg (Sigma.mk t) (eq_of_heq (Sigma.mk.inj_iff.mp (congrArg Prod.snd eq)).2)

private theorem Fabric.exists_flat {X Y : Type} (f : Fabric X Y) (z : f.FlatColumns) :
    ∃ c, f.socketKey c=f.flatKey z :=
  f.exists_socket z.1.val _ (List.getElem?_eq_getElem z.1.isLt) z.2

def Fabric.unflatten {X Y : Type} (f : Fabric X Y) : f.FlatColumns ↪ f.Column where
  toFun z := Classical.choose (f.exists_flat z)
  inj' u v eq := f.flatKey_injective (((Classical.choose_spec (f.exists_flat u)).symm.trans
    (congrArg f.socketKey eq)).trans (Classical.choose_spec (f.exists_flat v)))

@[simp] theorem Fabric.socketKey_unflatten {X Y : Type} (f : Fabric X Y) (z : f.FlatColumns) :
    f.socketKey (f.unflatten z)=f.flatKey z := Classical.choose_spec (f.exists_flat z)

end
end Hierarchy.ProbeStage

end OAI
