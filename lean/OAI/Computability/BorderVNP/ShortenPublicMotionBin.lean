import OAI.Computability.BorderVNP.ShortenPublicMovedBin

/-!
# Dispatching the selected whole-pack motion for each charged cable

A finite catalog index specifies the factor permutation and the Hecke words.
The common posttranslation remains a dynamic deck word. One Boolean frame
takes these inputs and reports the moved midpoint address and prepared bin.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicMovedBin

open Cover Cover.Frame Cover.AddressCircuit Hecke Epoch Crossing Framed PackMotions
open BorderVNP.StackFrame RationalHitting
open VPVNP.VerifierNetwork (Frame)
open scoped Classical

variable {q D n : ℕ} {S : Finset (HyperbolicHost (Cube D))} {h η : ℝ}
variable (B : PreparedBins D S h η) (enum : Fin q ≃ Cube D)

/-- Reading a finite motion index in addition to the relative segment type
and deck words still has a polynomial gate bound in the cover depth. -/
theorem motionBin_frames {M : Type*} [Fintype M] [DecidableEq M]
    (perm : M → Equiv.Perm (Cube D)) (word : M → ProductSample (lattice 1) elliptic (Cube D) n) :
    ∃ C k : ℕ, ∀ d : ℕ, 1 ≤ d →
      ∃ f : Frame (M ⊕ (↥B.types ⊕ (ProductSlots q (d+2*n) ⊕ ProductSlots q (d+2*n+2*n))))
        (ProductSlots q (d+2*n) ⊕ B.Bin), f.size ≤ C*(d+1)^k ∧
        ∀ (a : M) (t : B.types) (b : Cube D → gamma 1) (shift : Cube D → Deck (d+2*n)),
          f.eval (Sum.elim (fun j => decide (j=a)) (rowInput t (shift ∘ enum)
            (fun j => (sourceTile B t b (enum j) : Deck (d+2*n+2*n))))) =
          binWires B enum (sampleBin B t b (perm a) (word a) shift) := by
  choose C k H using fun a => movedBin_frames B enum (perm a) (word a)
  let A := Finset.univ.sup C
  let e := Finset.univ.sup k
  let l : TimeBound := TimeBound.variable + .const (2*n)
  let out : TimeBound := .const (90*q)*l + .const (Fintype.card B.Bin)
  let cost : TimeBound := 1 + .const (Fintype.card M*A)*TimeBound.variable^e +
    out * .const (4*Fintype.card M+1)
  obtain ⟨c,p,_,_,hc⟩ := cost.growth
  refine ⟨c,p,fun d hd => ?_⟩
  choose rows size sem using fun a => H a d hd
  obtain ⟨f,hf,he⟩ := catalogDispatch rows
  refine ⟨f, ?_, fun a t b shift => (he a _).trans (sem a t b shift)⟩
  have hrow (a : M) : (rows a).size ≤ A*(d+1)^e := (size a).trans
    (Nat.mul_le_mul (Finset.le_sup (Finset.mem_univ a)) (Nat.pow_le_pow_right (by omega)
      (Finset.le_sup (Finset.mem_univ a))))
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => hrow a)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have hout : Fintype.card (ProductSlots q (d+2*n) ⊕ B.Bin) = out.eval (d+1) := by
    simp [ProductSlots, Slots, width, out, l, TimeBound.eval_add, TimeBound.eval_mul]
    ring
  have bound := hc (d+1) (by omega)
  simp only [cost,TimeBound.eval_add,TimeBound.eval_mul,TimeBound.eval_const,TimeBound.eval_pow,
    TimeBound.eval_numeral,TimeBound.eval_variable] at bound
  rw [hout] at hf
  apply hf.trans
  rw [Nat.mul_assoc] at bound
  exact (Nat.add_le_add_right (Nat.add_le_add_left hsum 1) _).trans bound

/-- A dynamic motion choice computes the exact geometric tag of the charged
edge, reading the source tile from its public endpoint row. -/
theorem activeMotionBin_frames {M : Type*} [Fintype M] [DecidableEq M]
    (perm : M → Equiv.Perm (Cube D)) (word : M → ProductSample (lattice 1) elliptic (Cube D) n) :
    ∃ C k : ℕ, ∀ (d : ℕ) (hd : 1 ≤ d),
      ∃ f : Frame (M ⊕ (↥B.types ⊕ (ProductSlots q (d+2*n) ⊕ ProductSlots q (d+2*n+2*n))))
        (ProductSlots q (d+2*n) ⊕ B.Bin), f.size ≤ C*(d+1)^k ∧
        ∀ {copies : ℕ} {P : Type} {bits : P → ℕ} {K : Type*}
          (input : Fin copies → Pack D P bits K) (active : ∀ i, (input i).layout.Edge → Bool)
          (sites : ∀ i, (input i).layout.Site → SurfaceHost (Cube D) (d+2*n+2*n))
          (L : PreparedBins.Labels B input active sites) (w : Active input active)
          (a : M) (shift : Cube D → Deck (d+2*n)),
          ∃ z : (Cube D → Deck (d+2*n)) × B.Bin,
            B.tag (d := d+2*n) input active L.kind L.lift w.1 (perm a,word a,shift) w.2.val = some z ∧
            f.eval (Sum.elim (fun j => decide (j=a)) (rowInput (L.kind w) (shift ∘ enum)
              (fun j => addressAt _ (by omega) ((sites w.1 ((input w.1).layout.src w.2.val)) (enum j))))) =
              binWires B enum z := by
  obtain ⟨C,k,H⟩ := motionBin_frames B enum perm word
  refine ⟨C,k,fun d hd => ?_⟩
  obtain ⟨f,hs,he⟩ := H d hd
  refine ⟨f,hs,fun input active sites L w a shift =>
    ⟨sampleBin B (L.kind w) (L.lift w) (perm a) (word a) shift,
      sampleBin_eq_tag B input active L.kind L.lift w (perm a,word a,shift), ?_⟩⟩
  rw [label_source_address B enum input active sites L w]
  exact he _ _ _ _

end Shortening.PublicMovedBin

end BorderVNP
end Computability
end OAI
