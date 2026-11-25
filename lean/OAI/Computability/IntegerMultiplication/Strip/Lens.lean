import OAI.Computability.IntegerMultiplication.Strip.Order

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Strip
/-! Math interface. Lens orders a selected address relative to the
contiguous tape address Ω. Does not by itself encode any complexity assumptions. -/
open Matrix Finset
abbrev Lens (O I K : Type) := O ≃ I × K

namespace Optic
variable {A B O I K J L M R : Type}
def fiber (o : Lens O I K) (x : O→A) (k : K) : I → A :=
  fun i => x (o.symm (i,k))
def attach (o : Lens O I K) (x : K→I→A) : O → A :=
  fun w => x (o w).2 (o w).1
@[simp] theorem beam (o : Lens O I K) (x : K→I→A) :
    fiber o (attach o x) = x := by ext; simp [fiber, attach]
@[simp] theorem same (o : Lens O I K) (x : O→A) :
    attach o (fiber o x) = x := by ext; simp [fiber, attach]

def beamAll (o : Lens O I K) (m : K → (I → A) → (I → B)) (x : O→A) : O→B :=
  attach o (fun k => m k (fiber o x k))

theorem beam_each (o : Lens O I K) (m : K → (I → A) → (I → B)) (x : O→A) :
    fiber o (beamAll o m x) = fun k => m k (fiber o x k) := beam o _

theorem beam_after {C} (o : Lens O I K) (n : K → (I → B) → (I → C)) (m : K → (I → A) → (I → B))
    (x : O→A) :
    beamAll o n (beamAll o m x) = beamAll o (fun k => n k ∘ m k) x := by
  unfold beamAll; rw [beam]; rfl

abbrev everywhere (o : Lens O I K) (f : (I→A)→(I→B)) :=
  beamAll o (fun _ => f)
@[simp] theorem none (o : Lens O I K) :
    everywhere o (@id (I→A)) = id := by ext; simp [everywhere, beamAll, attach, fiber]

/-- Move entries by an address permutation. -/
def travel (e : O ≃ O) (x : O→A) : O→A :=
  x ∘ e.symm

theorem completed (e : O ≃ O) (x : O→A) (i : O) :
    travel e x (e i) = x i := by simp [travel]
theorem succession (d e : O ≃ O) (x : O→A) :
    travel d (travel e x) = travel (e.trans d) x := rfl

def field (o : Lens O I K) (e : I ≃ I) : O ≃ O :=
  (o.trans (e.prodCongr (.refl K))).trans o.symm

@[simp] theorem field_go (o : Lens O I K) (e : I ≃ I) (i : I) (k : K) :
    field o e (o.symm (i,k)) = o.symm (e i,k) := by simp [field, Equiv.prodCongr]

@[simp] theorem field_land (o : Lens O I K) (e : I ≃ I) (i : I) (k : K) :
    (field o e).symm (o.symm (i,k)) = o.symm (e.symm i,k) := by
  simp [field, Equiv.prodCongr]
theorem inside (o : Lens O I K) (e : I ≃ I) (x : O→A) :
    travel (field o e) x = everywhere o (travel e) x := by
  funext w
  obtain ⟨⟨i,k⟩, rfl⟩ := o.symm.surjective w
  simp [travel,everywhere, beamAll,attach,fiber]

/-- focus on a subfield (spectator extends on left) -/
def dig (o : Lens O I K) (d : Lens I J L) : Lens O J (L × K) :=
  (o.trans (d.prodCongr (.refl K))).trans (Equiv.prodAssoc _ _ _)
theorem focus (o : Lens O I K) (d : Lens I J L)
    (m : (J→A)→(J→B)) :
    everywhere o (everywhere d m) = everywhere (dig o d) m := rfl

def part (I : Type) : Lens I I Unit :=
  Equiv.prodPUnit I |>.symm -- unknown
theorem principal (f : (I→A)→(I→B)) :
    everywhere (part I) f=f := rfl

variable [Fintype I] [CommRing R]
def operate (o : Lens O I K) (T : Matrix I I R) := everywhere o (T *ᵥ ·)
theorem dot (o : Lens O I K) (T S : Matrix I I R) (x : O→R) :
    operate o T (operate o S x) = operate o (T*S) x := by
  rw [operate,operate,everywhere,everywhere,beam_after]
  congr
  funext k y
  exact Matrix.mulVec_mulVec y _ _

@[simp] theorem one [DecidableEq I] (o : Lens O I K) :
    operate o (1 : Matrix I I R) = id := by
  rw [operate,show ((1: Matrix I I R) *ᵥ ·) = id by funext (v : I → R); exact Matrix.one_mulVec v,none]
theorem diag [DecidableEq I] (o : Lens O I K) (p : I→R) (x : O→R) (u) :
    operate o (Matrix.diagonal p) x u = p (o u).1 * x u := by
  have d (i : I) : ∀ (w : I→R), (Matrix.diagonal p *ᵥ w) i = p i*w i :=
    fun _ => diagonal_dotProduct ..
  simp [operate,everywhere,beamAll,attach,d,fiber]
theorem scale (o : Lens O I K) (r : R) (T : Matrix I I R) (x : O→R) :
    operate o (r • T) x = r • operate o T x := by
  funext u
  exact congrFun (Matrix.smul_mulVec _ _ _) _
end Optic
end Strip

end IntegerMultiplication
end Computability
end OAI
