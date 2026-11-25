import OAI.Hierarchy.DescentSIMDLookup

namespace OAI
/-! # Short relative input and output descriptions for a complete matching neighborhood -/

namespace Hierarchy.DescentPacking.PackedMatch
open DescentSIMDLookup
noncomputable section

structure Shape where
  packs : ℕ
  bins : ℕ
  limit : ℕ
  entries : ℕ
  digit : ℕ

namespace Shape
def pairs (s : Shape) := s.packs*s.limit
def inFields (s : Shape) := s.packs+(s.bins+(s.entries*3+(s.entries*3+s.pairs)))
def outFields (s : Shape) := 1+s.pairs*12
def inputBits (s : Shape) := s.digit*s.inFields
def outputBits (s : Shape) := s.digit*s.outFields
def bits (s : Shape) := max s.inputBits s.outputBits
end Shape

set_option backward.isDefEq.respectTransparency false

/-- Signed old unit rows are local triples of edge, source and target incidence handles. -/
structure Inputs (s : Shape) where
  need : Fin s.packs→Cell s.digit
  cap : Fin s.bins→Cell s.digit
  thin : Fin s.entries→Fin 3→Cell s.digit
  thick : Fin s.entries→Fin 3→Cell s.digit
  profile : Fin s.pairs→Cell s.digit

private def block {b n m : ℕ} (u : Fin n→Cell b) (v : Fin m→Cell b) : Fin (n+m)→Cell b :=
  Fin.addCases u v
private def left {b n m : ℕ} (v : Fin (n+m)→Cell b) (i : Fin n) := v (Fin.castAdd m i)
private def right {b n m : ℕ} (v : Fin (n+m)→Cell b) (i : Fin m) := v (Fin.natAdd n i)

@[simp] private theorem left_block {b n m : ℕ} (u : Fin n→Cell b) (v : Fin m→Cell b) :
    left (block u v)=u := by
  funext i
  simp only [left,block,Fin.addCases_left]
@[simp] private theorem right_block {b n m : ℕ} (u : Fin n→Cell b) (v : Fin m→Cell b) :
    right (block u v)=v := by
  funext i
  simp only [right,block,Fin.addCases_right]

private def flatten {d n k : ℕ} (f : Fin n→Fin k→Cell d) (i : Fin (n*k)) : Cell d :=
  f (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
private def expand {d n k : ℕ} (f : Fin (n*k)→Cell d) (i : Fin n) (j : Fin k) := f (finProdFinEquiv (i,j))
@[simp] private theorem expand_flatten {d n k : ℕ} (f : Fin n→Fin k→Cell d) :
    expand (flatten f)=f := by funext i j;simp [expand,flatten]

def encodeInput {s : Shape} (v : Inputs s) : Cell s.inputBits :=
  encode s.digit s.inFields (block v.need (block v.cap (block (flatten v.thin) (block (flatten v.thick) v.profile))))

def decodeInput (s : Shape) (x : Cell s.inputBits) : Inputs s :=
  let v := (encode s.digit s.inFields).symm x
  let a := right (n:=s.packs) (m:=s.bins+(s.entries*3+(s.entries*3+s.pairs))) v
  let b := right (n:=s.bins) (m:=s.entries*3+(s.entries*3+s.pairs)) a
  let c := right (n:=s.entries*3) (m:=s.entries*3+s.pairs) b
  ⟨left v,left a,expand (left b),expand (left c),right c⟩

@[simp] theorem decode_encode (s : Shape) (v : Inputs s) : decodeInput s (encodeInput v)=v := by
  cases v
  unfold decodeInput encodeInput
  rw [Equiv.symm_apply_apply]
  simp

/-- The first digit is the number of genuine pairs. Each subsequent local
row has twelve digits for validity, relative offsets, old incidences, and the profile. -/
structure Output (s : Shape) where
  count : Cell s.digit
  row : Fin s.pairs→Fin 12→Cell s.digit

def encodeOutput {s : Shape} (o : Output s) : Cell s.outputBits :=
  encode s.digit s.outFields (block (fun _ : Fin 1=>o.count) (flatten o.row))

def decodeOutput (s : Shape) (x : Cell s.outputBits) : Output s :=
  let v := (encode s.digit s.outFields).symm x
  ⟨left (m:=s.pairs*12) v (0:Fin 1),expand (right (n:=1) v)⟩

@[simp] theorem output_inverse (s : Shape) (v : Output s) : decodeOutput s (encodeOutput v)=v := by
  cases v
  unfold decodeOutput encodeOutput
  rw [Equiv.symm_apply_apply]
  simp

theorem count_digit {s : Shape} (v : Output s) : digit s.digit 0 (encodeOutput v).val=v.count.val := by
  let i : Fin 1 := 0
  change digit s.digit (Fin.castAdd (s.pairs*12) i).val (encodeOutput v).val=_
  unfold encodeOutput
  simpa only [Shape.outFields,block,Fin.addCases_left] using
    digit_encode (block (fun _ : Fin 1=>v.count) (flatten v.row)) (Fin.castAdd (s.pairs*12) i)

theorem row_digit {s : Shape} (v : Output s) (i : Fin s.pairs) (j : Fin 12) :
    digit s.digit (1+(finProdFinEquiv (i,j)).val) (encodeOutput v).val=(v.row i j).val := by
  let p := finProdFinEquiv (i,j)
  unfold encodeOutput
  simpa only [Shape.outFields,block,Fin.addCases_right,Fin.val_natAdd,flatten,p,Equiv.symm_apply_apply]
    using digit_encode (block (fun _ : Fin 1=>v.count) (flatten v.row)) (Fin.natAdd 1 p)

end
end Hierarchy.DescentPacking.PackedMatch

end OAI
