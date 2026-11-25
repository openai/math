import OAI.Computability.BorderVNP.CoverDeckChildFrames
import OAI.Computability.BorderVNP.CoverDeckFrameOperations
import OAI.Computability.BorderVNP.CrossingParallelFrame

/-!
# Translated lookup keys for a digit of a product deck motion

For each candidate translation and residue, modular quaternion multipliers
compute the translated address used by the sparse histogram lookup. The
network uses one multiplication per factor and query row.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover.AddressCircuit

open BorderVNP.StackFrame
open VPVNP.VerifierNetwork (Frame)
open BinPackingGames.Foundations.Complexity.CookLevin

/-- All translated histogram read addresses at one level. Each row is
obtained by left multiplication by its candidate's dynamic translation. -/
theorem translationKeys_frames :
    ∃ C e : ℕ, ∀ q d m : ℕ, ∃ f :
      Frame (Fin m × Fin (keyWidth q d)) (Fin m × (Fin q → Deck d) × Fin (keyWidth q d)),
      f.size ≤ 1 + (m * (Fintype.card (Fin q → Deck d) * q)) * (3 * width d + C * (d+1)^e) ∧
      ∀ (c : Fin m → Fin q → Deck d) j v b,
        f.eval (fun p => keyWord q d (c p.1) p.2) (j,v,b) = keyWord q d (c j * v) b := by
  obtain ⟨C,e,hce⟩ := deckMul_frames
  refine ⟨C,e,?_⟩
  intro q d m
  obtain ⟨mul,hsize,heval⟩ := hce d
  let J := Fin m × (Fin q → Deck d) × Fin q
  let S := Fin m × Fin (keyWidth q d)
  let left (p : J) : Frame S (Slots (width d)) := Frame.initial (fun b => (p.1,keySlots q d (p.2.2,b)))
  let right (p : J) : Frame S (Slots (width d)) :=
    (Frame.initial (Empty.elim : Empty → S)).step fun b => .const (deckWires d (p.2.1 p.2.2) b)
  let single (p : J) := mul.subst (Crossing.parallelFrame (left p) (right p))
  have hs (p : J) : (single p).size ≤ 3*width d + C*(d+1)^e := by
    have hr := Frame.step_size_le (Frame.initial (Empty.elim : Empty → S))
      (fun b : Slots (width d) => .const (deckWires d (p.2.1 p.2.2) b)) 1 (fun _ => le_rfl)
    have hr' : (right p).size ≤ 3*width d := by simpa [right,Slots,mul_comm] using hr
    simpa [single,left] using Nat.add_le_add hr' hsize
  have hev (p : J) (c : Fin m → Fin q → Deck d) :
      (single p).eval (fun z => keyWord q d (c z.1) z.2) =
      deckWires d ((c p.1 * p.2.1) p.2.2) := by
    let x : S → Bool := fun z => keyWord q d (c z.1) z.2
    have hpair : (Crossing.parallelFrame (left p) (right p)).eval x =
        Sum.elim (deckWires d (c p.1 p.2.2)) (deckWires d (p.2.1 p.2.2)) := by
      funext a
      cases a <;> simp [left,right,x,StatementCircuit.Expr.eval]
    funext b
    simpa [single,← show x = (fun z => keyWord q d (c z.1) z.2) from rfl,hpair] using
      congrFun (heval (c p.1 p.2.2) (p.2.1 p.2.2)) b
  obtain ⟨all,ha,hal⟩ := Crossing.exists_parallelFrames (out := fun _ : J => Slots (width d)) single
  let lookup (p : Fin m × (Fin q → Deck d) × Fin (keyWidth q d)) : Σ _ : J, Slots (width d) :=
    let i := (keySlots q d).symm p.2.2
    ⟨(p.1,p.2.1,i.1),i.2⟩
  refine ⟨all.select lookup,?_,?_⟩
  · have h := Finset.sum_le_sum (s := Finset.univ) (fun p _ => hs p)
    simpa [J] using ha.trans (Nat.add_le_add_left h 1)
  · intro c j v b
    simp only [Frame.select_eval,lookup,hal]
    exact congrFun (hev (j,v,((keySlots q d).symm b).1) c) ((keySlots q d).symm b).2

/-- The gate cost of all lookup requests and child outputs, after identifying
the parent once in its table. -/
theorem childRequests_frames :
    ∃ C e : ℕ, ∀ q d : ℕ, ∃ f :
      Frame (Fin (keyWidth q d))
        ((Fin (childCount q d) × Fin (keyWidth q (d+1))) ⊕
        (Fin (childCount q d) × (Fin q → Deck (d+1)) × Fin (keyWidth q (d+1)))),
      f.size ≤ (childrenFrame q d).size + 1 +
        (childCount q d * (Fintype.card (Fin q → Deck (d+1)) * q)) *
          (3 * width (d+1) + C * (d+1+1)^e) ∧
      (∀ u j b, f.eval (keyWord q d u) (.inl (j,b)) = keyWord q (d+1) (childAt q d u j) b) ∧
      ∀ u j v b, f.eval (keyWord q d u) (.inr (j,v,b)) =
        keyWord q (d+1) (childAt q d u j * v) b := by
  obtain ⟨C,e,hce⟩ := translationKeys_frames
  refine ⟨C,e,?_⟩
  intro q d
  obtain ⟨f,hs,h⟩ := hce q (d+1) (childCount q d)
  refine ⟨f.withInput.subst (childrenFrame q d),?_,?_,?_⟩
  · simpa [Nat.add_assoc] using Nat.add_le_add_left hs (childrenFrame q d).size
  · intro u j b
    simp [childrenFrame_eval]
  · intro u j v b
    have hu : (childrenFrame q d).eval (keyWord q d u) =
        (fun p => keyWord q (d+1) (childAt q d u p.1) p.2) :=
      funext fun p => childrenFrame_eval q d u p.1 p.2
    simpa [hu] using h (childAt q d u) j v b

end Cover.AddressCircuit

end BorderVNP
end Computability
end OAI
