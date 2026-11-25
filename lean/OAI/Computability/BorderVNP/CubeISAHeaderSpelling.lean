import OAI.Computability.BorderVNP.CubeISAHeaderOffsets
import OAI.Computability.BorderVNP.CubeISASelectorRead
import OAI.Computability.BorderVNP.TransmissionHeaderFields

/-! # The compact physical spelling of the cube declaration

The coordinate is followed by one fixed-width word for each genuine unordered
pair and cut. Dense lower-triangle entries consume no bits. The field positions
in this spelling are those used by the native decoder on the actual copy of
the common header, immediately following the geometry profile.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.DeclarationBits

open Physical RoutingISA RoutingISA.CubeLengths TeamContraction.JointHeader VPVNP.BurstRAM

variable {n d cap w : ℕ}

/-- The little-endian word of one genuine symbol-pair entry at a dense index. -/
def field (f : Broadcast n d cap) (t : Fin (d*d*(n+1))) : Physical.Code (cap+1) :=
  let p := (entryOrder d (n+1)).symm t
  f.2 (Sym2.mk p.1.1 p.1.2) p.2

/-- Bits emitted at one dense index, with an empty block below the diagonal. -/
def chunk (f : Broadcast n d cap) (t : Fin (d*d*(n+1))) : List Bool :=
  if upper d (n+1) t.val then List.ofFn (field f t) else []

/-- The concatenation of the first `k` row-major entry chunks. -/
def rowBits (f : Broadcast n d cap) : ℕ → List Bool
  | 0 => []
  | k+1 => rowBits f k ++ if hk : k < d*d*(n+1) then chunk f ⟨k,hk⟩ else []

/-- Compact bit spelling of one raw cube broadcast. -/
def spelling (f : Broadcast n d cap) : List Bool :=
  List.ofFn f.1 ++ rowBits f (d*d*(n+1))

/-- The prefix bit length counts exactly the genuine upper-triangle fields. -/
theorem length_rowBits (f : Broadcast n d cap) (k : ℕ) (hk : k ≤ d*d*(n+1)) :
    (rowBits f k).length = fieldsBefore d (n+1) k * Nat.clog 2 (cap+1) := by
  induction k with
  | zero => simp [rowBits, fieldsBefore]
  | succ k ih =>
    have hlt : k < d*d*(n+1) := hk
    by_cases h : upper d (n+1) k <;> simp [rowBits,hlt,chunk,h,ih hlt.le,fieldsBefore,Nat.add_mul]

private theorem earlier {f : Broadcast n d cap} {k l : ℕ} (hkl : k ≤ l) {m : Memory w} {base : ℕ}
    (h : FlatAt m base (rowBits f l)) : FlatAt m base (rowBits f k) := by
  induction hkl with
  | refl => exact h
  | step _ ih => exact ih h.left

private theorem ofFn_bit (hw : 0 < w) {m : Memory w} {source len : ℕ} {bits : Fin len → Bool}
    (h : FlatAt m source (List.ofFn bits)) (j : Fin len) :
    readings m (source+j.val) = (bits j).toNat := by
  have e := h ⟨j.val,by simp⟩
  change (m _).val = _
  rw [show m (source+j.val) = DiagonalResidueRAM.word w (bits j).toNat by simpa using e]
  exact DiagonalResidueRAM.word_val w _ ((Bool.toNat_le _).trans_lt (Nat.one_lt_two_pow hw.ne'))

/-- Actual copied physical bits of the leading coordinate field. -/
theorem coordinate_bits (hw : 0 < w) {f : Broadcast n d cap} {m : Memory w} {source : ℕ}
    (h : FlatAt m source (spelling f)) (j : Fin (Nat.clog 2 (n+1))) :
    readings m (source+j.val) = (f.1 j).toNat :=
  ofFn_bit hw h.left j

/-- Actual copied physical bits of a row field, read by the native cursor. -/
theorem row_bits (hw : 0 < w) {f : Broadcast n d cap} {m : Memory w} {source : ℕ}
    (h : FlatAt m source (spelling f)) (t : Fin (d*d*(n+1))) (hu : upper d (n+1) t.val)
    (j : Fin (Nat.clog 2 (cap+1))) :
    readings m (fieldStart source d (n+1) (Nat.clog 2 (n+1)) (Nat.clog 2 (cap+1)) t.val+j.val) =
      (field f t j).toNat := by
  have hrows : FlatAt m (source+Nat.clog 2 (n+1)) (rowBits f (d*d*(n+1))) := by
    simpa only [List.length_ofFn] using (FlatAt.right (xs := List.ofFn f.1) (ys := rowBits f _) h)
  have hp := earlier (k := t.val+1) t.isLt hrows
  rw [rowBits, dite_eq_left t.isLt] at hp
  have hc := FlatAt.right hp
  simpa only [chunk,ite_eq_left hu,length_rowBits f t.val t.isLt.le,fieldStart] using ofFn_bit hw
    (show FlatAt m ((source+Nat.clog 2 (n+1))+(rowBits f t.val).length) (List.ofFn (field f t)) by
      simpa only [chunk,ite_eq_left hu] using hc) j

/-- The native unsigned decoder recovers exactly the corresponding raw code. -/
theorem read_bits {mem : ℕ → ℕ} {source limit : ℕ} {code : Physical.Code limit}
    (h : ∀ j, mem (source+j.val) = (code j).toNat) :
    (SelectorRead.decoded mem source (Nat.clog 2 limit)).val = readCode limit code := by
  have e : (fun j : Fin (Nat.clog 2 limit) => decide (mem (source+j.val) = 1)) = code := by
    funext j
    rw [h]
    cases code j <;> rfl
  simp only [SelectorRead.decoded,readCode,e]

/-- The dynamic bit decoder is reading the copied evaluation-mode header after
the geometry prefix and before the terminal subtotal fields. -/
theorem from_common_header {f : Broadcast n d cap} {m : Memory w} {base : ℕ} (geometry : List Bool)
    (claims : List (List Bool)) (extra : ℕ)
    (h : FlatAt m base (TeamContraction.JointHeader.padded
      (TeamContraction.JointHeader.spelling (geometry++spelling f) claims) extra)) :
    FlatAt m (base+1+geometry.length) (spelling f) := by
  have h₁ := FlatAt.left (xs := TeamContraction.JointHeader.spelling (geometry++spelling f) claims) h
  have h₂ : FlatAt m (base+1) ((geometry++spelling f)++claims.flatten) :=
    FlatAt.right (xs := [true]) h₁
  exact h₂.left.right

end Cube.DeclarationBits

end BorderVNP
end Computability
end OAI
