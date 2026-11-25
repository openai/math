import OAI.Computability.BorderVNP.ShortenFramedPublicPlacement
import OAI.Computability.BorderVNP.ShortenPublicRelative
import OAI.Computability.BorderVNP.ShortenEpochTerminalChoice

/-!
# Computing a moved terminal site's tile from its stored row

The input is a relative catalog index and the product deck coordinates. Deep
levels use modular quaternion arithmetic. The finitely many shallow levels
use finite residue tables with the same geometric semantics.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Terminal

open Cover Cover.AddressCircuit Shortening Shortening.Catalog Shortening.PublicRelative Epoch
open VPVNP.VerifierNetwork (Frame)
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit
open scoped Classical

variable {I : Type} [Fintype I] {q a : ℕ} (enum : Fin q ≃ I) (S : Finset (HyperbolicHost I))

/-- Stored relative catalog tag and tile coordinates at a lifted site. -/
noncomputable def liftRow (l : ℕ) (x : HyperbolicHost I) (hx : normalize x ∈ S) :
    ↥S ⊕ ProductSlots q l → Bool :=
  Sum.elim (fun t => decide (t=(⟨normalize x,hx⟩ : ↥S))) (tileWord enum l x)

/-- Geometric interpretation of the modular output on all attained rows. -/
def MovesSite {g : I → Cover.Frame.SL} (l : ℕ)
    (f : Frame (↥S ⊕ ProductSlots q (l+2*a)) (ProductSlots q l)) : Prop :=
  ∀ x (hx : normalize x ∈ S), f.eval (liftRow enum S (l+2*a) x hx) =
    tileWord enum l (motion (Equiv.refl I) g x)

private theorem deep_frames {g : I → Cover.Frame.SL} (hg : ∀ i, Cover.Frame.Clears (g i) a) :
    ∃ C k : ℕ, ∀ d : ℕ, 1 ≤ d → ∃ f, MovesSite (a := a) enum S (g := g) (d+2*a) f ∧
      f.size ≤ C*(d+1)^k := by
  let rel (t : ↥S) (i : Fin q) := (t.val (enum i)).toSL2R
  obtain ⟨C,k,h⟩ := geometricPackRow_frames (T := ↥S) (I := Empty) (fun i : Fin q => hg (enum i))
  refine ⟨C+90*q*(6*a+2)+S.card, max 1 k,?_⟩
  intro d hd
  let l := d+2*a
  let X := ↥S ⊕ ProductSlots q (l+2*a)
  obtain ⟨f,hsize,he⟩ := h d hd (Equiv.refl _) rel (fun _ _ j => j.elim)
  let pins : ↥S ⊕ (ProductSlots q l ⊕ ProductSlots q (l+2*a)) → Expr X := Sum.elim
    (fun t => .input (.inl t)) (Sum.elim (fun s => .const (productWires l (fun _ : Fin q => 1) s))
      (fun s => .input (.inr s)))
  let read := (Frame.initial id).step pins
  refine ⟨(f.select Sum.inl).subst read,?_,?_⟩
  · intro x hx
    let t : ↥S := ⟨normalize x,hx⟩
    let one (i : Fin q) : gamma 1 := 1
    let old i := carry x (enum i)
    have hr : read.eval (liftRow enum S _ x hx) =
        rowInput t (fun i => (one i : Deck l)) (fun i => (old i : Deck (l+2*a))) := by
      funext j
      rcases j with u | s | s <;> simp [read,pins,liftRow,rowInput,Expr.eval,one,old,t,tileWord]
    funext j
    rw [Frame.subst_eval,hr,Frame.select_eval,he t one old]
    change deckWires l (Cover.Frame.frameCarry (gammaSL 1 1 * (g (enum j.1) *
      (gammaSL 1 (carry x (enum j.1)) * (normalize x (enum j.1)).toSL2R))) : Deck l) j.2 = _
    rw [map_one,one_mul]
    unfold Cover.Frame.frameCarry
    rw [mul_smul,mul_smul,UpperHalfPlane.toSL2R_smul_I,carry_smul_normalize]
    rfl
  · have hr := Frame.step_size_le (Frame.initial (id : X → X)) pins 1 (by
        rintro (t | s | s) <;> rfl)
    have hout : read.size ≤ S.card + 90*q*(l+1)+90*q*(l+2*a+1) := by
      simpa [read,ProductSlots,StackFrame.Slots,width,Nat.mul_add,Nat.add_mul,Nat.mul_comm,Nat.mul_left_comm,
        Nat.mul_assoc,Nat.add_assoc] using hr
    have hu : (d+1)^k ≤ (d+1)^max 1 k := Nat.pow_le_pow_right (by omega) (le_max_right _ _)
    have hlin : d+1 ≤ (d+1)^max 1 k := (pow_one (d+1)).symm.le.trans
      (Nat.pow_le_pow_right (by omega) (le_max_left _ _))
    rw [Frame.subst_size,Frame.select_size]
    -- Wiring the fixed unit shift uses one gate per field.
    have h1 : S.card ≤ S.card*(d+1)^max 1 k := Nat.le_mul_of_pos_right _ (pow_pos (by omega) _)
    have hl : (l+1)+(l+2*a+1) ≤ (6*a+2)*(d+1)^max 1 k :=
      (show (l+1)+(l+2*a+1) ≤ (6*a+2)*(d+1) by dsimp [l]; nlinarith).trans
        (Nat.mul_le_mul_left _ hlin)
    have h₂ := Nat.mul_le_mul_left (90*q) hl
    have h₃ := Nat.mul_le_mul_left C hu
    rw [Nat.mul_add] at h₂
    rw [Nat.add_mul,Nat.add_mul,Nat.mul_assoc]
    omega

/-- The quotient point represented by a tile and a relative position. -/
private noncomputable def pointFromTile (l : ℕ) (z : UpperHalfPlane) : Deck l → Surface l :=
  Quotient.lift (fun b : gamma 1 => projectPoint l (gammaSL 1 b • z)) (by
    intro a b h
    have h' := QuotientGroup.leftRel_apply.mp h
    have hc : b.val * a.val⁻¹ ∈ gamma l := (gammaNormal _).mem_comm h'
    let c : gamma l := ⟨_,hc⟩
    apply Quotient.sound
    refine ⟨c,?_⟩
    change gammaSL 1 (b*a⁻¹) • (gammaSL 1 a • z) = _
    simp [mul_smul])

private theorem small_frame {g : I → Cover.Frame.SL} (hg : ∀ i, Cover.Frame.Clears (g i) a) (d : ℕ) :
    ∃ f, MovesSite (a := a) enum S (g := g) (d+2) f := by
  let l := d+2
  let z := l+2*a
  let A := ↥S × (Fin q → Deck z)
  let enc (v : A) : ↥S ⊕ ProductSlots q z → Bool :=
    Sum.elim (fun t => decide (t=v.1)) (productWires z v.2)
  let point (v : A) : SurfaceHost I z :=
    WithLp.toLp 2 fun i => pointFromTile z (v.1.val i) (v.2 (enum.symm i))
  let table (v : A) := productWires l fun i => productAddress (d+1)
    (productMotion l (Equiv.refl _) hg (point v)) (enum i)
  have inj : Function.Injective enc := by
    intro x y eqn
    apply Prod.ext
    · have hh := congrFun eqn (.inl x.1)
      simpa [enc] using hh
    · funext i
      apply deckWires_injective z
      exact funext fun j => congrFun eqn (.inr (i,j))
  obtain ⟨f,_,hf⟩ := lookupFrame enc inj table
  refine ⟨f,?_⟩
  intro x hx
  let key : A := (⟨normalize x,hx⟩,fun i => (carry x (enum i) : Deck z))
  have hp : point key = productProjection z x := by
    ext1 i
    change pointFromTile z (normalize x i) (carry x (enum (enum.symm i)) : Deck z) = _
    rw [Equiv.apply_symm_apply]
    change projectPoint z (gammaSL 1 (carry x i) • normalize x i) = _
    rw [carry_smul_normalize]; rfl
  have he : liftRow enum S z x hx = enc key := rfl
  rw [he,hf]
  change productWires l (fun i => productAddress (d+1) (productMotion l (Equiv.refl _) hg (point key)) (enum i)) = _
  rw [hp]; rfl

/-- For every output level at least two the actual rounded site address is
read by a polynomial-size shared circuit. The constants depend only on the
fixed motion and catalog. -/
theorem site_frames {g : I → Cover.Frame.SL} (hg : ∀ i, Cover.Frame.Clears (g i) a) :
    ∃ C k : ℕ, ∀ d, ∃ f, MovesSite (a := a) enum S (g := g) (d+2) f ∧ f.size ≤ C*(d+3)^k := by
  obtain ⟨C,k,hdeep⟩ := deep_frames enum S hg
  choose f hf using fun i : Fin (2*a) => small_frame enum S hg i.val
  let M := Finset.univ.sup (fun i => (f i).size)
  refine ⟨C+M,k,?_⟩
  intro d
  by_cases hd : d+1 < 2*a
  · let i : Fin (2*a) := ⟨d,by omega⟩
    refine ⟨f i,hf i,(Finset.le_sup (f := fun i => (f i).size) (Finset.mem_univ i)).trans ?_⟩
    exact (Nat.le_add_left M C).trans (Nat.le_mul_of_pos_right _ (pow_pos (by omega) _))
  · obtain ⟨u,hu⟩ := Nat.exists_eq_add_of_le (show 2*a ≤ d+1 by omega)
    have hz : d+2 = (u+1)+2*a := by omega
    obtain ⟨y,hy,hs⟩ := hdeep (u+1) (by omega)
    rw [hz]
    refine ⟨y,hy,hs.trans ?_⟩
    exact Nat.mul_le_mul (Nat.le_add_right _ _) (Nat.pow_le_pow_left (by omega) _)

end PackedHistoryCircuit.Terminal

end BorderVNP
end Computability
end OAI
