import OAI.Computability.NearSquareRoot.InterchangeConfiguredBatch
import OAI.Computability.NearSquareRoot.InterchangePayloadBank
import OAI.Computability.NearSquareRoot.InterchangeBatchFrame

/-!
# Identifying the packed lanes with the native ordered bank

Use the physical enumeration of the lane and label pair to number the
independent rows. Every admissible packed tree can be decoded at this
enumeration and at every address. Applying a common address permutation to
each lane then gives exactly the same permutation of the original tree rows.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange.FinBank

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip InterchangePayloadBank

variable {I R E : Type} {D X : I → Type} {W : ℕ}

/-- Position in the actual physical row enumeration. -/
noncomputable def position (rows : Series R) (h : rows.count = W) : R → Fin W :=
  fun u => Fin.cast h (rows.index u)

theorem stripe_position (rows : Series R) (h : rows.count = W) (y : Fin W → Tree) :
    stripe rows (y ∘ position rows h) = stripe (Series.natural W) y := by
  rw [stripe_eq,stripe_eq]
  apply congrArg send
  apply List.ext_getElem (by simp [h])
  intro i hi hi'
  let j : Fin rows.count := ⟨i, by simpa using hi⟩
  let k := Fin.cast h j
  rw [rows.get _ j, (Series.natural W).get _ ⟨i, by simpa using hi'⟩]
  simp only [Function.comp_apply,position,Equiv.apply_symm_apply]
  apply congrArg y
  exact (Series.get_natural W k _).symm

/-- One physically ordered sequence of fat rows for a bank of ordinary record
functions. -/
def packet (records : (i : I) → Series (X i)) (v : Fin W → (i : I) → X i → Tree) (i : I) :=
  stripe (Series.natural W) fun u => stripe (records i) (v u i)

/-- Every compiled packed-register computation of a given common record
action yields exactly that action on the raw ordered tree rows. -/
theorem lift_rows (records : (i : I) → Series (X i)) (payload : (i : I) → Series (D i))
    (src : E → Tree) (rows : Series R) (width : rows.count = W)
    (relation : (I → Tree) → (I → Tree) → Prop)
    (action : (i : I) → X i → X i)
    (machine : ∀ v : (i : I) → R → X i × D i → E,
      relation (render records payload rows src v)
        (render records payload rows src fun i u k => v i u (action i k.1,k.2)))
    (v : Fin W → (i : I) → X i → Tree) (good : ∀ u i x, Good payload src i (v u i x)) :
    relation (packet records v) (packet records fun u i => v u i ∘ action i) := by
  classical
  choose read hread using good
  let y (i : I) (row : R) (z : X i × D i) := read (position rows width row) i z.1 z.2
  have bank (act : (i : I) → X i → X i) :
      render records payload rows src (fun i u k => y i u (act i k.1,k.2)) =
      packet records (fun u i => v u i ∘ act i) := by
    funext i
    dsimp only [render,packet]
    rw [← stripe_position rows width]
    apply congrArg (stripe rows)
    funext u
    apply congrArg (stripe (records i))
    funext x
    exact (hread (position rows width u) i (act i x)).symm
  have h₁ : render records payload rows src y = packet records v := bank fun _ => id
  rw [← h₁,← bank]
  exact machine y

end Interchange.FinBank

end NearSquareRoot
end Computability
end OAI
