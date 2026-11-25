import OAI.ThreeFlat.Diagonal.MotifOrderedValue
import OAI.ThreeFlat.Diagonal.MotifCompactionOrder

namespace OAI
/-! # Physical tile coefficients on the externally packed boundary words -/

namespace ThreeFlat.Diagonal.MotifOrderedCells

open Routing Routing.StableCompaction TraceCircuit MotifBinaryPacking
open scoped BigOperators Classical

variable {F H : Type*} [CommRing F] {r e d b : ℕ}

/-- The only consulted tables are constant-size functions of a single copy's
header and its incident, bounded-width words. -/
structure Tile (F H : Type*) (e d b : ℕ) where
  symbol : (Fin b → Bool) → H
  width : H → Fin e → ℕ
  fits : ∀ h a, width h a ≤ d
  value : ∀ z : Fin b → Bool, (∀ a, Fin (2^width (symbol z) a)) → F

namespace Tile

variable (K : Tile F H e d b)

def rule : Mask r e d b := fun _ z a j => decide (j.val < K.width (K.symbol z) a)

def table : Table F r e d b := fun _ z xs => K.value z fun a =>
  word _ fun j => xs (finProdFinEquiv (a,Fin.castLE (K.fits _ a) j))

noncomputable def network (C : BitNetwork F ((r*d)+(r*d+r*d))) :=
  MotifOrderedCells.network (checkedTile K.rule K.table) C

def lengths (z : Fin r → Fin b → Bool) (a : Fin e) (i : Fin r) := K.width (K.symbol (z i)) a

/-- The parent presents a zero-filled suffix after each packed payload. -/
def packedInput (z : Fin r → Fin b → Bool) (x : ∀ a, Fin (2^∑ i, K.lengths z a i))
    (a : Fin e) (j : Fin (r*d)) : Bool :=
  if h : j.val < ∑ i, K.lengths z a i then (word _).symm (x a) ⟨j.val,h⟩ else false

private def expanded (z : Fin r → Fin b → Bool) (x : ∀ a, Fin (2^∑ i, K.lengths z a i)) : Fields r e d :=
  fun a i j => if h : j.val < K.lengths z a i then
    (word _).symm ((pack (K.lengths z a)).symm (x a) i) ⟨j.val,h⟩ else false

omit [CommRing F] in
private theorem supported (z : Fin r → Fin b → Bool) (x : ∀ a, Fin (2^∑ i, K.lengths z a i)) :
    Supported (observed K.rule z) (K.expanded z x) := by
  intro a i j h
  have miss : ¬j.val < K.lengths z a i := by simpa [observed,rule,lengths] using h
  simp [expanded,miss]

omit [CommRing F] in
private theorem packed (z : Fin r → Fin b → Bool) (x : ∀ a, Fin (2^∑ i, K.lengths z a i)) :
    boundary (observed K.rule z) (K.expanded z x) = K.packedInput z x := by
  funext a j
  let u := K.lengths z a
  let fit : ∀ i, u i ≤ d := fun i => K.fits _ a
  let bits (i : Fin r) := (word (u i)).symm ((pack u).symm (x a) i)
  have mask_eq : blocks r d (observed K.rule z a) = TrackData.mask finProdFinEquiv.symm u := by
    funext k
    obtain ⟨⟨i,t⟩,rfl⟩ := finProdFinEquiv.surjective k
    simp [observed,rule,TrackData.mask,u,lengths]
  have data_eq : blocks r d (K.expanded z x a) = TrackData.padded finProdFinEquiv.symm u bits := by
    funext k
    obtain ⟨⟨i,t⟩,rfl⟩ := finProdFinEquiv.surjective k
    let value (it : Fin r × Fin d) :=
      if h : it.2.val < u it.1 then bits it.1 ⟨it.2.val,h⟩ else false
    change (blocks r d (K.expanded z x a)) (finProdFinEquiv (i,t)) =
      value (finProdFinEquiv.symm (finProdFinEquiv (i,t)))
    rw [blocks_at,Equiv.symm_apply_apply]
    rfl
  rw [boundary,mask_eq,data_eq,packedInput]
  by_cases h : j.val < ∑ i, u i
  · rw [dite_eq_left h]
    let l : Fin (∑ i, u i) := ⟨j.val,h⟩
    have stream := congrFun (stream_eq_flatten u fit bits) l
    change compact _ _ j = (word _).symm (x a) l
    change compact _ _ j = flatten u bits l at stream
    rw [stream]
    obtain ⟨⟨i,t⟩,hl⟩ := (finSigmaFinEquiv (n := u)).surjective l
    rw [←hl,←unpack_bit]
    exact congrArg (fun g : (i : Fin r) → Fin (u i) → Bool => g i t)
      ((flatten u).symm_apply_apply bits)
  · rw [dite_eq_right h]
    exact TrackData.compact_after _ u fit bits j (Nat.le_of_not_gt h)

omit [CommRing F] in
private theorem table_at (z : Fin r → Fin b → Bool) (x : ∀ a, Fin (2^∑ i, K.lengths z a i)) (i : Fin r) :
    K.table i (z i) (copyPayload (K.expanded z x) i) =
      K.value (z i) (fun a => (pack (K.lengths z a)).symm (x a) i) := by
  apply congrArg (K.value (z i))
  funext a
  apply (word _).symm.injective
  funext j
  simp [copyPayload,expanded,lengths]; rfl

/-- The concrete finite trivalent network returns the product of tile
coefficients on the literal slices of the packed parent words. -/
theorem eval_packed (C : BitNetwork F ((r*d)+(r*d+r*d)))
    (hC : ∀ M X Y, C.eval (Fin.append M (Fin.append X Y)) = if Y = compact M X then 1 else 0)
    (z : Fin r → Fin b → Bool) (x : ∀ a, Fin (2^∑ i, K.lengths z a i)) :
    (K.network C).eval (arguments z (K.packedInput z x)) =
      ∏ i, K.value (z i) (fun a => (pack (K.lengths z a)).symm (x a) i) := by
  rw [← K.packed z x]
  simpa only [network,K.table_at] using
    network_value K.rule K.table C hC z (K.expanded z x) (K.supported z x)

end Tile
end ThreeFlat.Diagonal.MotifOrderedCells

end OAI
