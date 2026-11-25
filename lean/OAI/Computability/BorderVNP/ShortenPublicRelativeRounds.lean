import OAI.Computability.BorderVNP.ShortenPublicRelative

/-!
# Dynamic motion selection throughout the finite catalog sequence

Each row carries the motion chosen for its pack. Dispatching the finite
candidate list retains the modular cost of the individual site updates.
The bound is chosen once for the prepared rounds, before any cover depth.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicRelative

open Catalog Epoch Crossing Cover.AddressCircuit BorderVNP.StackFrame RationalHitting
open VPVNP.VerifierNetwork (Frame)
open scoped Classical

variable {I : Type*} [Fintype I] {q D m : ℕ} {K : Type*} [Field K]

/-- Semantics when the motion index is supplied on the row's input wires. -/
def MotionRow (enum : Fin q ≃ I) (p : Pattern I D) (e : PaidIdentity K D m)
    (S : Finset (HyperbolicHost I)) (d : ℕ)
    (f : Frame (Fin p.moves ⊕ (↥S ⊕ (ProductSlots q (d+2*p.depth) ⊕
      ProductSlots q (d+2*p.depth+2*p.depth)))) (ProductSlots q (d+2*p.depth) ⊕ ↥(p.nextSites e S))) : Prop :=
  ∀ (n : Fin p.moves) shift x (hx : normalize x ∈ S),
    f.eval (Sum.elim (fun u => decide (u=n)) (siteInput enum S _ _ shift x hx)) =
      Sum.elim (tileWord enum _ (moved p n shift x)) (fun t => decide (t = movedIndex p e S n shift x hx))

/-- A single circuit per depth handles all motions. Every descriptor of a
pack may read the same one-hot motion choice and posttranslation. -/
theorem motionRow_frames (enum : Fin q ≃ I) (p : Pattern I D) (e : PaidIdentity K D m)
    (S : Finset (HyperbolicHost I)) :
    ∃ C k : ℕ, ∀ d : ℕ, 1 ≤ d → ∃ f, MotionRow enum p e S d f ∧ f.size ≤ C*(d+1)^k := by
  choose C k h using siteRow_frames enum p e S
  let M := Finset.univ.sup C
  let u := Finset.univ.sup k
  let l : TimeBound := TimeBound.variable + .const (2*p.depth)
  let Y : TimeBound := .const (90*q) * l + .const (p.nextSites e S).card
  let B : TimeBound := 1 + .const (p.moves*M) * TimeBound.variable^u + Y * .const (4*p.moves+1)
  obtain ⟨A,b,_,_,hB⟩ := B.growth
  refine ⟨A,b,?_⟩
  intro d hd
  choose rows hr hs using fun i => h i d hd
  obtain ⟨f,hf,he⟩ := catalogDispatch rows
  refine ⟨f,?_,?_⟩
  · intro n shift x hx
    rw [he,hr n shift x hx]
  · have hb (i) : (rows i).size ≤ M*(d+1)^u := (hs i).trans (Nat.mul_le_mul
      (Finset.le_sup (Finset.mem_univ i)) (Nat.pow_le_pow_right (by omega) (Finset.le_sup (Finset.mem_univ i))))
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hb i)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
    have hout : Fintype.card (ProductSlots q (d+2*p.depth) ⊕ ↥(p.nextSites e S)) = Y.eval (d+1) := by
      simp [ProductSlots,Slots,width,Y,l,TimeBound.eval_add,TimeBound.eval_mul]
      ring
    have htotal := hB (d+1) (by omega)
    simp only [B,TimeBound.eval_add,TimeBound.eval_mul,TimeBound.eval_pow,TimeBound.eval_const,
      TimeBound.eval_numeral,TimeBound.eval_variable] at htotal
    rw [hout,Fintype.card_fin] at hf
    apply hf.trans
    rw [Nat.mul_assoc] at htotal
    exact (Nat.add_le_add_right (Nat.add_le_add_left hsum 1) _).trans htotal

/-- All chosen rounds have one depth-polynomial gate bound. The catalogs
may be prepared recursively from the preceding relative types. -/
theorem finiteRound_frames (enum : Fin q ≃ I) (e : PaidIdentity K D m)
    (initial : Finset (HyperbolicHost I)) (round : ℕ → Finset (HyperbolicHost I) → Pattern I D)
    (b : ℕ) :
    ∃ C k : ℕ, ∀ (j : Fin b) (d : ℕ), 1 ≤ d →
      let S := siteCatalogs e initial round j
      ∃ f, MotionRow enum (round j S) e S d f ∧ f.size ≤ C*(d+1)^k := by
  choose C k h using fun j : Fin b =>
    motionRow_frames enum (round j (siteCatalogs e initial round j)) e (siteCatalogs e initial round j)
  refine ⟨Finset.univ.sup C,Finset.univ.sup k,?_⟩
  intro j d hd
  obtain ⟨f,hf,hs⟩ := h j d hd
  exact ⟨f,hf,hs.trans (Nat.mul_le_mul (Finset.le_sup (Finset.mem_univ j))
    (Nat.pow_le_pow_right (by omega) (Finset.le_sup (Finset.mem_univ j))))⟩

end Shortening.PublicRelative

end BorderVNP
end Computability
end OAI
