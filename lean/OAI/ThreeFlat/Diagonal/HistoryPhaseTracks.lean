import OAI.ThreeFlat.Diagonal.GuardedTransfer

namespace OAI
/-! # Logical rows of physical transitions with a shared auxiliary register -/

namespace ThreeFlat.Diagonal.GuardedTransfer

open scoped Classical BigOperators
noncomputable section

variable {F X Y U A H : Type*} [CommSemiring F] [Fintype X] [Fintype Y] [Fintype U]

omit [Fintype X] in
theorem tracks_of_support (e : X → U) (f : Y ↪ U) (M : Matrix U U F) (K : Matrix X Y F)
    (onImage : ∀ x y, M (e x) (f y) = K x y)
    (offImage : ∀ x u, (∀ y, f y ≠ u) → M (e x) u = 0) : Tracks e f M K := by
  apply tracks_of_entries
  intro x u
  by_cases mem : ∃ y, f y = u
  · obtain ⟨y,rfl⟩ := mem
    simp [f.injective.eq_iff,onImage]
  · have outside : ∀ y, f y ≠ u := fun y eq => mem ⟨y,eq⟩
    simp [outside,offImage x u outside]

def fixedAux (a : A) : X ↪ X × A := ⟨fun x => (x,a),fun _ _ e => congrArg Prod.fst e⟩

def withAux (f : H ↪ A) : X × H ↪ X × A :=
  ⟨fun x => (x.1,f x.2),fun _ _ h =>
    Prod.ext (congrArg (fun p : X × A => p.1) h) (f.injective (congrArg (fun p : X × A => p.2) h))⟩

variable [Fintype A] [Fintype H] [DecidableEq X] [DecidableEq H]

omit [DecidableEq X] in
theorem tracks_fixed (a b : A) (M : Matrix (X × A) (X × A) F) (K : Matrix X X F)
    (entry : ∀ x y d, M (x,a) (y,d) = if d=b then K x y else 0) :
    Tracks (fixedAux a) (fixedAux b) M K := by
  apply tracks_of_support
  · intro x y
    change M (x,a) (y,b) = K x y
    simpa using entry x y b
  · rintro x ⟨y,d⟩ h
    have ne : d ≠ b := by rintro rfl; exact h y rfl
    exact (entry x y d).trans (ite_eq_right ne)

omit [DecidableEq H] in
theorem tracks_propose (a : A) (f : H ↪ A) (M : Matrix (X × A) (X × A) F)
    (entry : ∀ x y d, M (x,a) (y,d) = if (∃ h, f h=d) ∧ x=y then 1 else 0) :
    Tracks (fixedAux a) (withAux f) M (openHistory (H:=H)) := by
  apply tracks_of_support
  · rintro x ⟨y,h⟩
    change M (x,a) (y,f h) = _
    rw [entry]
    simp [openHistory,Matrix.one_apply]
  · rintro x ⟨y,d⟩ outside
    have ne : ¬∃ h, f h = d := by rintro ⟨h,rfl⟩; exact outside (y,h) rfl
    change M (x,a) (y,d)=0
    simpa only [ne,false_and,ite_false] using entry x y d

omit [DecidableEq H] [Fintype H] in
theorem tracks_clear (a : A) (f : H ↪ A) (M : Matrix (X × A) (X × A) F)
    (entry : ∀ x h y d, M (x,f h) (y,d) = if d=a ∧ x=y then 1 else 0) :
    Tracks (withAux f) (fixedAux a) M (openHistory (H:=H)).transpose := by
  apply tracks_of_support
  · rintro ⟨x,h⟩ y
    change M (x,f h) (y,a) = _
    rw [entry]
    simp [Matrix.transpose_apply,openHistory,Matrix.one_apply,eq_comm]
  · rintro ⟨x,h⟩ ⟨y,d⟩ outside
    have ne : d ≠ a := by rintro rfl; exact outside y rfl
    change M (x,f h) (y,d)=0
    simpa only [ne,false_and,ite_false] using entry x h y d

omit [DecidableEq X] in
/-- The pair-count and the register encoding may vary over the retained
history because the group product can be verified independently on each row. -/
theorem tracks_fibres (e f : X × H → U) (M : Matrix U U F) (K : H → Matrix X X F)
    (row : ∀ h, Tracks (fun x => e (x,h)) (fun y => f (y,h)) M (K h)) :
    Tracks e f M (Matrix.blockDiagonal K) := by
  ext xh u
  obtain ⟨x,h⟩ := xh
  have one := congrArg (fun A : Matrix X U F => A x u) (row h)
  change (rows (fun y : X => e (y,h)) * M : Matrix X U F) x u =
    (K h * rows (fun y : X => f (y,h)) : Matrix X U F) x u at one
  rw [rows_mul,Matrix.mul_apply] at one
  rw [rows_mul,one,Matrix.mul_apply,Fintype.sum_prod_type]
  simp [Matrix.blockDiagonal_apply,ite_mul]
  rfl


end
end ThreeFlat.Diagonal.GuardedTransfer

end OAI
