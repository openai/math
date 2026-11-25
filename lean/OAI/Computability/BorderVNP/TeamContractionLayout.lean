import OAI.Computability.BorderVNP.DiagonalLayout

/-! # Independent team sums in the signed diagonal contraction

Every exterior variable is shared by the two endpoint teams. Interior variables have a
team coordinate, so at fixed exterior data the interior assignments can be summed
independently. The bit read at every site is the actual `Diagonal.Layout.slots` bit,
including the whole program, the literal tail, the live pin, clamped interior positions
and the final zero padding.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open Diagonal Diagonal.Layout
open scoped BigOperators Classical

variable {R r t d link inner n : ℕ} {Edge : Type}

/-- All exterior wire indices, one variable per physical direct-link bit. -/
abbrev Exterior (R r link : ℕ) := Routing.Block (R+1) × Fin r × Fin link

/-- A concrete input layout for all teams and processors of a diagonal contraction. -/
structure Wiring (R r t d link inner n : ℕ) (Edge : Type) where
  /-- Literal prefix of the common validator. -/
  program : List Bool
  /-- Pinned or otherwise fixed remainder of each processor's literal. -/
  literal : Fin (R+1) → Fin r → Fin t → Bool
  /-- Actual interior wire read at a processor position, or the constant-zero clamp. -/
  interior : Fin r → Fin inner → Option Edge
  /-- The physical fields all fit before zero padding to the common processor length. -/
  fits : 2*(program.length+t) + R*link + inner ≤ n

variable (G : Wiring R r t d link inner n Edge)

/-- The manuscript's physical slot at each input bit of a processor. -/
def Wiring.slot (site : Fin (R+1) × Fin r) : Fin n → InputSlot (Fin d) (Wire R r link Edge) :=
  Layout.slots G.program G.literal G.interior d link G.fits site

/-- Exterior and independently indexed team-local assignments combine to one assignment
on exactly the wires of the diagonal. -/
def assignments (ext : Exterior R r link → Bool) (int : Fin (R+1) → Edge → Bool) :
    Wire R r link Edge → Bool := Sum.elim (fun p => int p.1 p.2) ext

/-- Reindexing the full assignment as exterior bits followed by all independent team
interior bits is a bijection, including when a wire family is empty. -/
def assignmentEquiv : ((Exterior R r link → Bool) × (Fin (R+1) → Edge → Bool)) ≃
    (Wire R r link Edge → Bool) where
  toFun p := assignments p.1 p.2
  invFun f := (fun j => f (.inr j), fun u e => f (.inl (u,e)))
  left_inv _ := rfl
  right_inv f := by funext i; cases i <;> rfl

/-- Local input word, with the interior bits named solely in this team. -/
def Wiring.word (pin : Fin d → Bool) (ext : Exterior R r link → Bool) (int : Edge → Bool)
    (u : Fin (R+1)) (j : Fin r) : Fin n → Bool :=
  fun i => (G.slot (u,j) i).read pin (assignments ext (fun _ => int))

private def exteriorBit (ext : Exterior R r link → Bool) (u : Fin (R+1)) (j : Fin r)
    (i : Fin (R*link)) : Bool :=
  let p := finProdFinEquiv.symm i
  ext (blockOf u (u.succAbove p.1) (u.ne_succAbove p.1),j,p.2)

private def pinBit (pin : Fin d → Bool) (u : Fin (R+1)) (j : Fin r) {m : ℕ} (a : Fin m) : Bool :=
  if u = 0 then
    let p := finProdFinEquiv (j,a)
    if h : p.val < d then pin ⟨p.val,h⟩ else false
  else false

/-- Unmodified sequence of bits inspected by the finite processor table. -/
def Wiring.input (pin : Fin d → Bool) (ext : Exterior R r link → Bool) (int : Edge → Bool)
    (u : Fin (R+1)) (j : Fin r) : List Bool :=
  G.program ++ List.ofFn (G.literal u j) ++ List.ofFn (exteriorBit ext u j) ++
    List.ofFn (fun a : Fin (G.program.length+t) => pinBit pin u j a) ++
    List.ofFn (fun i => (G.interior j i).elim false int) ++
    List.replicate (n-(2*(G.program.length+t)+R*link+inner)) false

/-- Reading the actual physical slots only uses the selected team's interior assignment.
Both endpoints of an exterior bit read the same global exterior variable. -/
theorem Wiring.read_bits (pin : Fin d → Bool) (ext : Exterior R r link → Bool)
    (int : Fin (R+1) → Edge → Bool) (u : Fin (R+1)) (j : Fin r) :
    List.ofFn (fun i => (G.slot (u,j) i).read pin (assignments ext int)) =
      G.input pin ext (int u) u j := by
  have hp (i : Fin (G.program.length+t)) : (pinSlot (Edge := Edge) (link := link) d u j i).read pin
      (assignments ext int) = pinBit pin u j i := by
    by_cases hu : u = 0
    · simp only [pinSlot,pinBit,hu,ite_true]; split <;> rfl
    · simp only [pinSlot,pinBit,hu,ite_false]; rfl
  have hi (i : Fin inner) : ((G.interior j i).elim (.literal false) (fun e => .link (.inl (u,e))) :
      InputSlot (Fin d) (Wire R r link Edge)).read pin (assignments ext int) =
      (G.interior j i).elim false (int u) := by cases G.interior j i <;> rfl
  have he (i : Fin (R*link)) : (exteriorSlot (Edge := Edge) (d := d) u j i).read pin (assignments ext int) =
      exteriorBit ext u j i := rfl
  have hl (b : Bool) : (InputSlot.literal b).read pin (assignments ext int) = b := rfl
  change List.ofFn (InputSlot.read pin (assignments ext int) ∘ G.slot (u,j)) = _
  rw [← List.map_ofFn, Wiring.slot, ofFn_slots, Layout.tail]
  simp only [List.map_append, List.map_ofFn, List.map_replicate, List.map_map,
    Function.comp_def, he, hp, hi, hl, Wiring.input, List.append_assoc]
  rw [show (fun b : Bool => b) = id from rfl, List.map_id]

/-- The local word agrees position by position with the globally wired query. -/
theorem Wiring.read_eq (pin : Fin d → Bool) (ext : Exterior R r link → Bool)
    (int : Fin (R+1) → Edge → Bool) (u : Fin (R+1)) (j : Fin r) :
    (fun i => (G.slot (u,j) i).read pin (assignments ext int)) = G.word pin ext (int u) u j := by
  apply List.ofFn_injective
  exact (G.read_bits pin ext int u j).trans (G.read_bits pin ext (fun _ => int u) u j).symm

variable [Fintype Edge]

/-- Integer value of one team of signed universal processors, after fixing the exterior
inputs and pin. Each physical interior link is summed once. -/
noncomputable def Wiring.value (pin : Fin d → Bool) (ext : Exterior R r link → Bool) (u : Fin (R+1)) : ℤ :=
  ∑ int : Edge → Bool, ∏ j : Fin r, signedCount (G.word pin ext int u j)

/-- Expand the local signed coefficients using their actual canonical `n^100`-tick
witnesses. Distinct processor choices contribute separately even at equal terminal states. -/
theorem Wiring.value_eq_witnesses (pin : Fin d → Bool) (ext : Exterior R r link → Bool) (u : Fin (R+1)) :
    G.value pin ext u = ∑ int : Edge → Bool, ∑ witnesses : Fin r → Fin (n^100) → Bool,
      ∏ j : Fin r, signedWitness (G.word pin ext int u j) (witnesses j) := by
  simp only [Wiring.value,signedCount_eq_sum_witnesses,Fintype.prod_sum]

/-- Exact decomposition of the signed contraction over the paper's actual slot layout:
sum over shared exterior assignments of the product of the independently summed teams. -/
theorem Wiring.contraction_eq (pin : Fin d → Bool) :
    signedContraction G.slot pin = ∑ ext, ∏ u, G.value pin ext u := by
  classical
  let E := assignmentEquiv (R := R) (r := r) (link := link) (Edge := Edge)
  let total := fun links : Wire R r link Edge → Bool =>
    ∏ proc, signedCount (fun j => (G.slot proc j).read pin links)
  have reindex : signedContraction G.slot pin = ∑ p, total (E p) := by
    unfold signedContraction
    apply Finset.sum_equiv E.symm (by simp)
    intro p _
    rw [E.apply_symm_apply]
  rw [reindex, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro ext _
  rw [show (∏ u, G.value pin ext u) = ∑ ints : Fin (R+1) → Edge → Bool,
      ∏ u, ∏ j, signedCount (G.word pin ext (ints u) u j) from Fintype.prod_sum _]
  apply Finset.sum_congr rfl
  intro ints _
  dsimp only [total]
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro u _
  apply Finset.prod_congr rfl
  intro j _
  exact congrArg signedCount (G.read_eq pin ext ints u j)

end TeamContraction

end BorderVNP
end Computability
end OAI
