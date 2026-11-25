import OAI.Computability.IntegerMultiplication.Olive.Pawn

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Olive
open Well Larch Bureau Halo Moira Param Scale Strip Code
open Rivulet Dusk Grid Echo Cone Cap Brief Staff IntegerMultiplication.Fourier
open Finset
variable (L:ℕ)
abbrev Radius:=2*L+1
def shift (i:Fin (Radius L)):ℤ:=i.val-L
theorem opportunity : Function.Injective (shift L):=by
  intro i j h; apply Fin.ext
  unfold shift at h; omega
theorem forge : Finset.image (shift L) univ=rad L:=by
  ext v
  rw [mem_rad,mem_image]; simp only [mem_univ,true_and]
  constructor
  · intro ⟨x,h⟩; have i:=x.isLt; unfold shift Radius at *; omega
  intro ⟨h,q⟩
  refine ⟨⟨(v+L).toNat,?_⟩,?_⟩
  · unfold Radius; omega
  change ((v+L).toNat:ℤ)-(L:ℤ)=v; omega
theorem project {X:Type}[AddCommMonoid X](f:ℤ→X):
    ∑ i∈rad L,f i=∑ i:Fin (Radius L),f (shift L i):=by rw [← forge,sum_image (Function.Injective.injOn (opportunity L))]

variable {I:Type}(n:I→ℕ){r:Regime I}(T:Origin n r)
variable (a:(i:I)→Direction (n i))(A:Realizes r (fun i=> (a i).val))
variable (w:Faculty n)
variable (h:∀i,Season (n i))
noncomputable section
abbrev hotN_ (o:I→ℤ)(x:(i:I)→Farm (n i)):=(grow n a (seln n a o h) (strokeA n a w o) x)
abbrev pale (b:Bool)(o:I→ℤ)(x:(i:I)→Farm (n i)):=(grow n a (end_ n a o h) (strokeB n a w o b) x)
private theorem empty_r (k:ℕ): Grid.aspect (0:Grain k)=0 := by unfold Grid.aspect; ext <;> simp [Grid.lift]
private theorem empty_p {n} (x:G n): punch x 0=0:= by
  have g: divA (Scale.F n) (Grid.aspect x * Grid.aspect (0:G n))=0:= by
    rw [empty_r,mul_zero]
    unfold divA; unfold slash; ext <;> simp
  have e:= faithful (Scale.F n) x 0 (show focus (Scale.W n) _ from by rw [g]; unfold focus Grid.tiny; simp)
  change Grid.aspect (punch x 0)=_ at e
  rw [← back (punch x 0),e,g,map_zero]
variable (x:(i:I)→Farm (n i))
theorem visitA (i:I): (∑ y∈rad (Scale.L (n i)),(hotN_ n a w h (fun _=>y) x i))=
    Echo.street (a i) (Cone.extend_ n w i (h i) (a i)) (x i):= by
  funext j
  rw [Finset.sum_apply]
  rfl
abbrev briefL (n:ℕ):= (Scale.K n)*(Scale.J n)
theorem visitB (b:Bool)(i:I): (∑ y∈rad (briefL (n i)),pale n a w h b (fun _=>y) x i) =
    Echo.street (a i) (Cone.close_ n w i (h i) (a i) b) (x i):= by
  funext j
  rw [Finset.sum_apply]
  simp only [pale,grow,give,strokeB,Echo.street,Cone.close_]
  unfold hair
  by_cases H:(j (a i)).val< modN n a i
  · rw [dite_eq_left H]; simp_rw [dite_eq_left H]
    change _=∑ y∈rad _, _
    refine sum_congr rfl fun y _=>?_
    rfl
  rw [dite_eq_right H]
  simp_rw [dite_eq_right H,empty_p]; simp
-- remainder class tally for offset z ∈ radius
include A T
variable (m:I→ℕ) (q:Realizes r m) (p:∀ i,m i≤ modN n a i)
    (j:(i:I)→ Fin (Radius (m i)))(g:Realizes r (fun i=> (j i).val))
include q g p
theorem radius_ :
    Realizes r (fun i=> (wrap (modN n a i) (shift (m i) (j i))).val) := by
  have S:=RoomLine.sourceSize a (show RoomLine r n a from ⟨T.toCalendar,A⟩)
  have Z:= (((g.plus S).minused q).rem S)
  have e (i:I): ((j i).val + modN n a i - m i)% modN n a i=
      (wrap (modN n a i) (shift (m i) (j i))).val:= by
    specialize p i
    let z:=modN n a i
    let h:=m i
    have U : h≤ (j i).val+z := p.trans (Nat.le_add_left ..)
    change ((j i).val+z-h)%z=_
    zify [U]
    change _=rep (wrap z (shift h (j i)))
    rw [rep_wrap]
    unfold shift
    rw [show (((j i).val:ℤ)+z-h)=((j i).val-h:ℤ)+z by ring] -- typo
    simp
  simp_rw [e] at Z; exact Z
end
end Olive

end IntegerMultiplication
end Computability
end OAI
