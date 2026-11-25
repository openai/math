import OAI.Computability.NearSquareRoot.InterchangeROMTableTagged

/-! # The complete two-output correction on independent packed labels

The raw instruction reads both correction inputs per packed label and computes
both outputs in one physical lookup. Each coordinate is (input/output bit,
label, check row). The slot field above the row bank is the current sign mask.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMTable

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
open InterchangeROMRepair GeneratorSyntax

abbrev CheckRole (D : Type) (s : ℕ) := Bool × D × Fin s
abbrev CheckIndex := Bool × ℕ × ℕ

def checkIndex {s : ℕ} {D : Type} (lane : D → ℕ) (r : CheckRole D s) : CheckIndex :=
  (r.1,lane r.2.1,r.2.2.val)

def correctionMatrix {R D : Type} [Zero R] [DecidableEq D] {s : ℕ}
    (M : Bool → Bool → Matrix (Fin s) (Fin s) R) :
    Matrix (CheckRole D s) (CheckRole D s) R :=
  fun u v => if u.2.1 = v.2.1 then M u.1 v.1 u.2.2 v.2.2 else 0

theorem correctionMatrix_mulVec {R D : Type} [Semiring R] [Fintype D] [DecidableEq D] {s : ℕ}
    (M : Bool → Bool → Matrix (Fin s) (Fin s) R) (x : CheckRole D s → R) (u : CheckRole D s) :
    (correctionMatrix M).mulVec x u =
      (M u.1 false).mulVec (fun j => x (false,u.2.1,j)) u.2.2 +
      (M u.1 true).mulVec (fun j => x (true,u.2.1,j)) u.2.2 := by
  simp [Matrix.mulVec,dotProduct,Fintype.sum_prod_type,correctionMatrix,ite_mul,
    Finset.sum_ite_irrel,add_comm]

/-- Assemble the four row-major slots, repeating their action separately on
each numerical label. -/
def checkEntry (p s m z : ℕ) (t : Raw.Tape) (u v : CheckIndex) : ℕ :=
  if u.2.1 = v.2.1 then
    Raw.atSlot t (correctSlot m z u.1 v.1) s u.2.2 v.2.2 % (p+1)
  else 0

def checkRows (p s m z : ℕ) (t : Raw.Tape) (oi ii : List CheckIndex) :=
  oi.map fun u => ii.map fun v => checkEntry p s m z t u v

def checkTable (p s m : ℕ) (t : Raw.Tape) (oi ii : List CheckIndex) :=
  tagged (List.range (2^m)) numeral fun z => matrixTable (p+1) ii.length (checkRows p s m z t oi ii)

def checkCommand (p s m : ℕ) (t : Raw.Tape) (oi ii : List CheckIndex) : Cmd :=
  RegisterTable.command (checkTable p s m t oi ii)

theorem checkCommand_within (p s m : ℕ) (t : Raw.Tape) (oi ii : List CheckIndex) :
    CommonRegisters.Within 2 (checkCommand p s m t oi ii) :=
  RegisterTable.within (le_refl 2) _

variable {p s w m : ℕ} {D : Type} [Fintype D] [DecidableEq D]

omit [Fintype D] in
theorem checkRows_ordered (η : Fin m → Bool) (t : Raw.Tape) (oi ii : Series (CheckRole D s))
    (lane : D → ℕ) (inj : Function.Injective lane) :
    checkRows p s m (Raw.mask η).val t (oi.tab (checkIndex lane)) (ii.tab (checkIndex lane)) =
      orderedCoefficients ii oi (correctionMatrix ((Raw.decode p w s m t).correct η)) := by
  simp only [checkRows,Series.tab,List.map_map,orderedCoefficients,Function.comp_def]
  apply congrArg (fun f => List.map f oi.explore)
  funext u
  apply congrArg (fun f => List.map f ii.explore)
  funext v
  by_cases he : u.2.1 = v.2.1 <;>
    simp [checkIndex,checkEntry,correctSlot,inj.eq_iff,correctionMatrix,he,Raw.decode,Raw.interpret]

theorem checkTable_correct (η : Fin m → Bool) (t : Raw.Tape) (oi ii : Series (CheckRole D s))
    (lane : D → ℕ) (inj : Function.Injective lane) (x : CheckRole D s → ZMod (p+1)) :
    let T := checkTable p s m t (oi.tab (checkIndex lane)) (ii.tab (checkIndex lane))
    let M := (Raw.decode p w s m t).correct η
    let u := Tree.fork (numeral (Raw.mask η).val) (stripe ii (fun i => numeral (x i).val))
    let y := stripe oi (fun i => numeral
      (((M i.1 false).mulVec (fun j => x (false,i.2.1,j)) i.2.2 +
        (M i.1 true).mulVec (fun j => x (true,i.2.1,j)) i.2.2).val))
    RegisterLookup.read T u = y ∧ (u,y) ∈ T := by
  let M := (Raw.decode p w s m t).correct η
  apply tagged_correct _ numeral numeral_injective _ (Raw.mask η).val _ _ (List.mem_range.mpr (Raw.mask η).isLt)
  rw [checkRows_ordered (w := w) η t oi ii lane inj,Series.card]
  simpa only [correctionMatrix_mulVec] using ordered_correct ii oi (correctionMatrix M) x

/-- A single run of the compiled ROM produces both requested output blocks. -/
theorem checkCommand_run (η : Fin m → Bool) (t : Raw.Tape) (oi ii : Series (CheckRole D s))
    (lane : D → ℕ) (inj : Function.Injective lane) (x : CheckRole D s → ZMod (p+1)) (env : Env) (r : Deck) :
    let T := checkTable p s m t (oi.tab (checkIndex lane)) (ii.tab (checkIndex lane))
    let M := (Raw.decode p w s m t).correct η
    let u := Tree.fork (numeral (Raw.mask η).val) (stripe ii (fun i => numeral (x i).val))
    let y := stripe oi (fun i => numeral
      (((M i.1 false).mulVec (fun j => x (false,i.2.1,j)) i.2.2 +
        (M i.1 true).mulVec (fun j => x (true,i.2.1,j)) i.2.2).val))
    Fits env (checkCommand p s m t (oi.tab (checkIndex lane)) (ii.tab (checkIndex lane)))
      (pile 0 u r) (pile 0 y r) (RegisterTable.cost T) := by
  have h := checkTable_correct (w := w) η t oi ii lane inj x
  exact RegisterTable.run_lookup _ _ _ h.2 h.1 env r

end InterchangeROMTable

end NearSquareRoot
end Computability
end OAI
