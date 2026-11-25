import OAI.ThreeFlat.Diagonal.ShrinkDemands
import OAI.ThreeFlat.Diagonal.CompressorIncidences

namespace OAI
/-! # Width and rank sums obtained by the two local bundle scans -/

namespace ThreeFlat.Diagonal.CompressorPacking
open Computability.VPVNP.Compression
open scoped Classical BigOperators
variable {V H Tag L : Type*} {c d : ℕ}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
variable (P : PackingData V H Tag L d c)

private theorem sum_test {A : Type*} [Fintype A] (p : A → Prop) [DecidablePred p] [Fintype (Subtype p)] (f : A → ℕ) :
    (∑ a : Subtype p, f a.val) = ∑ a, if p a then f a else 0 := by
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by simp) f).symm

def ttAt (p : Site V Tag L × Fin d) (u : BitWord c × H) : Prop :=
  P.thick (sourcePosition (p,u)) ∧ P.thick (sourcePosition (P.actual (p,u)))

def thickFiber (p : Site V Tag L × Fin d) : ThickAt P p ≃ Subtype (ttAt P p) where
  toFun a := ⟨a.val.2,by
    rcases a with ⟨⟨q,u⟩,hp,ok⟩
    change q=p at hp
    subst q
    exact ok⟩
  invFun u := ⟨(p,u.val),rfl,u.property⟩
  left_inv a := Subtype.ext (Prod.ext a.property.1.symm rfl)
  right_inv _ := rfl

theorem tt_scan (w : Arc V H Tag L d c → ℕ) (p : Site V Tag L × Fin d) :
    thickWidth P w p = ∑ u : BitWord c × H, if ttAt P p u then w (p,u) else 0 := by
  calc
    _ = ∑ u : Subtype (ttAt P p), w (p,u.val) :=
      Fintype.sum_equiv (thickFiber P p) _ _ fun z => congrArg w (Prod.ext z.property.1 rfl)
    _ = _ := sum_test (ttAt P p) (fun u => w (p,u))

def atCenter (p : Site V Tag L × Fin d) (incoming : Bool) (i : Fin d) (u : BitWord c) :
    Arc V H Tag L d c :=
  let z := center P p i u
  if incoming then P.actual.symm z else z

def acceptedCenter (p : Site V Tag L × Fin d) (incoming : Bool) (i : Fin d) (u : BitWord c) : Prop :=
  ¬P.thick (sourcePosition (center P p i u)) ∧
    (incoming = true → P.thick (sourcePosition (P.actual.symm (center P p i u))))

/-- The sum over original CD wires whose bundle is fixed becomes two bounded
port/word loops, with exactly one accepting direction per old CD incidence. -/
theorem cd_scan (w : Arc V H Tag L d c → ℕ) (p : Site V Tag L × Fin d) :
    (∑ q : {m : P.Motif // P.bundle m = p}, w q.val.val) =
      ∑ dir : Bool, ∑ i : Fin d, ∑ u : BitWord c,
        if acceptedCenter P p dir i u then w (atCenter P p dir i u) else 0 := by
  let g := fun s : Choices P p => w ((bundleFiberEquiv P p).symm s).val.val
  have eq : (∑ q : {m : P.Motif // P.bundle m = p}, w q.val.val) = ∑ s, g s :=
    Fintype.sum_equiv (bundleFiberEquiv P p) _ _ (fun q => by simp [g])
  rw [eq]
  change _ = _
  dsimp only [Choices] at g ⊢
  rw [Fintype.sum_sum_type,Fintype.sum_sigma,Fintype.sum_sigma,Fintype.sum_bool]
  conv_rhs => rw [add_comm]
  simp only [acceptedCenter,atCenter,Bool.false_eq_true,false_implies,true_implies,
    and_true,ite_false,ite_true]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    exact sum_test (fun u => ¬P.thick (sourcePosition (center P p i u))) (fun u => w (center P p i u))
  · apply Finset.sum_congr rfl
    intro i _
    exact sum_test (fun u => ¬P.thick (sourcePosition (center P p i u)) ∧
      P.thick (sourcePosition (P.actual.symm (center P p i u)))) (fun u => w (P.actual.symm (center P p i u)))

end ThreeFlat.Diagonal.CompressorPacking

end OAI
