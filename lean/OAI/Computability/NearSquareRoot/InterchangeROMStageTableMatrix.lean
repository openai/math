import OAI.Computability.NearSquareRoot.InterchangeROMStageTable
import OAI.Computability.NearSquareRoot.InterchangeROMStageRoles
import Mathlib.Computability.Primrec.List

/-! # Physical rectangle matrices in the numbered stage banks -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMStageTable
open InterchangeROMStage

/-- Frame, modulus, lane count, inverse minor, base mixer and indexed query mixers.
Matrices are row-major coefficient lists. -/
abbrev Parameters := Frame × ℕ × ℕ × List ℕ × List ℕ × List (List ℕ)

def read (cols : ℕ) (a : List ℕ) (i j : ℕ) : ℕ := (a[i*cols+j]?).getD 0

def decode (c : Parameters) : Data where
  p := c.2.1
  labels := Frame.labels c.1
  rectangles := Frame.boxes c.1
  queries := Frame.queries c.1
  ranks := (Frame.minor c.1 true).length
  lanes := c.2.2.1
  src b v := Frame.incident c.1 false v b
  dst b v := Frame.incident c.1 true v b
  row i := ((Frame.minor c.1 true)[i]?).getD 0
  col i := ((Frame.minor c.1 false)[i]?).getD 0
  minor := read (Frame.minor c.1 true).length c.2.2.2.1
  base := read c.2.2.1 c.2.2.2.2.1
  query j := read c.2.2.1 ((c.2.2.2.2.2[j]?).getD [])

def expandRoles (roles : List Role) (d : ℕ) : List Ground :=
  roles.flatMap fun role => (List.range d).map fun k => (role,k)

def normalize (p : ℕ) (m : List (List ℕ)) : List (List ℕ) := m.map fun row => row.map (· % p)

def gateMatrix (c : Parameters) (t : Frame.Table) : List (List ℕ) :=
  normalize c.2.1 (matrix (decode c) t.1 (expandRoles t.2.1 c.2.2.1) (expandRoles t.2.2 c.2.2.1))

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip InterchangeROMTable

/-- The generated natural matrix uses canonical residue representatives in the
actual input and output serialization orders. -/
theorem gateMatrix_ordered {A B : Type} (c : Parameters) (t : Frame.Table)
    (inp : Series A) (out : Series B) (u : A → Ground) (v : B → Ground)
    (hi : expandRoles t.2.1 c.2.2.1 = inp.tab u) (ho : expandRoles t.2.2 c.2.2.1 = out.tab v) :
    gateMatrix c t = orderedCoefficients inp out (fun b a =>
      (coefficient (terms (decode c) t.1 (v b)) (u a) : ZMod c.2.1)) := by
  simp [gateMatrix,normalize,matrix,hi,ho,orderedCoefficients,Series.tab,List.map_map,
    Function.comp_def,ZMod.val_natCast]

/-- The finite physical lookup consumes the forest of ground letters and
produces the new forest. -/
theorem gate_lookup {A B : Type} [Fintype A] (c : Parameters) [NeZero c.2.1]
    (t : Frame.Table) (inp : Series A) (out : Series B) (u : A → Ground) (v : B → Ground)
    (hi : expandRoles t.2.1 c.2.2.1 = inp.tab u) (ho : expandRoles t.2.2 c.2.2.1 = out.tab v)
    (inj : Function.Injective u) (covered : ∀ b term, term ∈ terms (decode c) t.1 (v b) →
      ∃ a, u a = term.1) (x : Ground → ZMod c.2.1) :
    let table := matrixTable c.2.1 inp.count (gateMatrix c t)
    let src := stripe inp (fun a => numeral (x (u a)).val)
    let dst := stripe out (fun b => numeral (value x (terms (decode c) t.1 (v b))).val)
    RegisterLookup.read table src = dst ∧ (src,dst) ∈ table := by
  let M : Matrix B A (ZMod c.2.1) := fun b a => coefficient (terms (decode c) t.1 (v b)) (u a)
  have e : M.mulVec (x ∘ u) = fun b => value x (terms (decode c) t.1 (v b)) :=
    funext fun b => coefficient_mulVec _ u inj _ (covered b) x
  have h := ordered_correct inp out M (x ∘ u)
  dsimp only at h ⊢
  rw [e] at h
  rw [gateMatrix_ordered c t inp out u v hi ho]
  exact h

end InterchangeROMStageTable

end NearSquareRoot
end Computability
end OAI
