import OAI.Computability.IntegerMultiplication.Loom.Image
import OAI.Computability.IntegerMultiplication.Net.Launch

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Loom
open Strip Dims Optic IntegerMultiplication.Port Adic Net Net.Shuttle
open Matrix
variable {J : Type} [DecidableEq J] [Fintype J] {p j : ℕ} [NeZero p] {P G B : Tape}

noncomputable section
abbrev Audience (P G B : Tape) := Pin P × Pin G × Pin B
def liftBack (z : Audience P G B) (x : Duplex J (Tower p j)) :
    Keys P G B J (Block p j) :=
  (z.1,(index p j).symm ∘ x.1,z.2.1,(index p j).symm ∘ x.2,z.2.2)
def square :
    Lens (Keys P G B J (Block p j)) (Duplex J (Tower p j)) (Audience P G B) where
  toFun x := (chase x,watcher x)
  invFun x := liftBack x.2 x.1
  left_inv := by
    rintro ⟨a,f,c,g,b⟩
    have e (k : J→Block p j) : (index p j).symm ∘ (index p j) ∘ k = k :=
      funext fun i => (index p j).symm_apply_apply _
    change (a,(index p j).symm ∘ (index p j) ∘ f,c,(index p j).symm ∘ (index p j) ∘ g,b)=_
    rw [e f,e g]
  right_inv := by
    rintro ⟨⟨f,g⟩,a,c,b⟩
    have e (k : J→Tower p j) : (index p j) ∘ (index p j).symm ∘ k=k :=
      funext fun i => (index p j).apply_symm_apply _
    change (((index p j) ∘ (index p j).symm ∘ f,(index p j) ∘ (index p j).symm ∘ g),a,c,b)=_
    rw [e f,e g]

-- abelian group of address actions
variable (M N : Matrix J J (Tower p j))
def waving (M : Matrix J J (Tower p j)) : (Duplex J (Tower p j)) ≃ (Duplex J (Tower p j)) where
  toFun x := Rank.shear M x
  invFun x := Rank.shear (-M) x
  left_inv x := by dsimp only; rw [Rank.sheen]; simp [Rank.shear]
  right_inv x := by dsimp only; rw [Rank.sheen]; simp [Rank.shear]
def tide (P G B : Tape) : Equiv.Perm (Keys P G B J (Block p j)) :=
  Optic.field square (waving M)
omit [DecidableEq J] in
theorem turnAround : (tide M P G B).symm = tide (-M) P G B := by
  ext x : 1
  dsimp only [tide,Optic.field,waving,Equiv.symm_trans_apply,Equiv.trans_apply]
  rfl
omit [DecidableEq J] in
theorem forward (x : Keys P G B J (Block p j)) :
    square (tide M P G B x) = ((Rank.shear M (chase x)), watcher x) := by
  unfold tide Optic.field
  simp only [Equiv.trans_apply,Equiv.apply_symm_apply,Equiv.prodCongr_apply]
  rfl
omit [DecidableEq J] in
theorem windy :
    (tide M P G B).trans (tide N P G B)=tide (M+N) P G B := by
  apply Equiv.ext
  intro x
  apply square.injective
  rw [Equiv.trans_apply,forward, forward]
  -- query chase & watcher
  have h := forward M x
  change (chase _,watcher _)=_ at h
  have d : chase ((tide M P G B) x)=Rank.shear M (chase x) := (Prod.ext_iff.mp h).1
  have e : watcher ((tide M P G B) x)=watcher x := (Prod.ext_iff.mp h).2
  rw [d,e,Rank.sheen]

-- pullback of VALUES by address actions.
def ship {O R : Type} (z : Equiv.Perm O) : (O→R) ≃ (O→R) where
  toFun := travel z
  invFun := travel z.symm
  left_inv f := by ext i; simp [travel]
  right_inv f := by ext i; simp [travel]

def breath {L : Type} {p} (z : L→Matrix J J (Tower p j)) (P G B : Tape) (R : Type)
    [NeZero p] [Ring R] :
    Hop.Frames L (Keys P G B J (Block p j)) R where
  act l := ship (tide (z l) P G B)
  add _ _ _ := rfl
  scale _ _ _ := rfl

variable {R L : Type} [Ring R]
omit [DecidableEq J] in
theorem undulate (z : L→Matrix J J (Tower p j)) (l k : L)
    (x : Keys P G B J (Block p j)→R) :
    (breath z _ _ _ R).act k (((breath z _ _ _ R).act l).symm x) =
    travel (tide (z k-z l) ..) x := by
  change travel (tide _ ..) (travel (tide _ ..).symm x) = _
  rw [succession,turnAround,windy,add_comm,sub_eq_add_neg]
variable {n : ℕ} (f : J ≃ Fin n)

def recreation (P G B : Tape) (j : ℕ) :
    (l : List (Lag J p)) → (h : ∀ i∈l,i.legal (ranking f)) →
      Equiv.Perm (Keys P G B J (Block p j))
| [],_ => Equiv.refl _
| r::l,h =>
  (reflect f r (h _ List.mem_cons_self) _ _ _ _).trans
    (recreation _ _ _ _ l (fun i ih => h i (List.mem_cons_of_mem _ ih)))
omit [Fintype J] in
theorem fore (l : List (Lag J p)) (h : ∀ i∈l,i.legal (ranking f))
    (x : Keys P G B J (Block p j)) :
    square (recreation f _ _ _ _ l h x) = (l.foldl (Lag.fire j) (chase x),watcher x) := by
  induction l generalizing x with
  | nil => rfl
  | cons r l ih =>
    rw [recreation, Equiv.trans_apply, ih, List.foldl_cons]
    rw [(walk f r _ x).2,(walk f r _ x).1]

theorem outward (l : List (Lag J p)) (h : ∀ i∈l,i.legal (ranking f))
    (flight : ∀ x,l.foldl (Lag.fire j) x=Rank.shear M x) :
    recreation f P G B j l h = tide M P G B := by
  apply Equiv.ext
  intro x
  apply square.injective
  rw [fore,forward,flight]
end
end Loom

end IntegerMultiplication
end Computability
end OAI
