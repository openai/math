import OAI.Computability.NearSquareRoot.InterchangeOpcodeCompute
import OAI.Computability.NearSquareRoot.InterchangeRomEquality

/-! # Correctness of the numeric two-wing address checker -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Opcode
open IntegerMultiplication.Port Interchange.AddressROM

variable {n b : ℕ}

private def position (s : Spot (Fin n)) := index n (eraseSpot s)

private theorem position_lt (s : Spot (Fin n)) : position s < 2*n := by
  rcases s with ⟨_ | _,i⟩ <;> simp [position,index,eraseSpot] <;> omega

private theorem position_injective : Function.Injective (position (n:=n)) := by
  rintro ⟨_ | _,i⟩ ⟨_ | _,j⟩ h <;> simp [position,index,eraseSpot] at h ⊢ <;> omega

private theorem position_surj (i : ℕ) (hi : i < 2*n) : ∃ a : Spot (Fin n), position a = i := by
  by_cases h : i < n
  · exact ⟨(false,⟨i,h⟩),rfl⟩
  · exact ⟨(true,⟨i-n,by omega⟩),by change n + (i-n) = i; omega⟩

private def Agrees (v : List Scalar) (x : Spot (Fin n) → ℚ) : Prop :=
  v.length = 2*n ∧ ∀ a, Scalar.val (v.getD (position a) Scalar.zero) = x a

private theorem agrees_set {v : List Scalar} {x : Spot (Fin n) → ℚ} (h : Agrees v x)
    (a : Spot (Fin n)) (d : Scalar) : Agrees (v.set (position a) d) (Function.update x a (Scalar.val d)) := by
  refine ⟨by simpa using h.1,fun t => ?_⟩
  rw [List.getD_eq_getElem _ _ (by simp [h.1,position_lt]), List.getElem_set]
  by_cases e : a=t
  · subst t; simp
  · have he : position a ≠ position t := position_injective.ne e
    simp only [he,ite_false,Function.update_of_ne (Ne.symm e)]
    rw [← List.getD_eq_getElem _ _ (by rw [h.1]; exact position_lt t)]
    exact h.2 t

private theorem scalar_span (a : Span b) :
    Scalar.val (Scalar.ofRaw a.neg a.top.count a.down.count) = ratio a :=
  Scalar.val_ofRaw _ _ _ (Nat.pos_of_ne_zero a.down.pos)

private theorem agrees_step {v : List Scalar} {x : Spot (Fin n) → ℚ} (h : Agrees v x)
    (op : Lag (Fin n) b) : Agrees (step n v (encode op)) (fire x op) := by
  cases op with
  | width a s =>
    have g := agrees_set h a (Scalar.mul (Scalar.ofRaw s.neg s.top.count s.down.count)
      (v.getD (position a) Scalar.zero))
    simp only [Scalar.val_mul,scalar_span,h.2] at g
    exact g
  | gather a k s =>
    rcases s with _ | s
    · have g := agrees_set h a (Scalar.add (v.getD (position a) Scalar.zero)
        (Scalar.mul (Scalar.ofRaw false 0 1) (v.getD (position k) Scalar.zero)))
      have zero : Scalar.val (Scalar.ofRaw false 0 1) = 0 := by
        rw [Scalar.val_ofRaw _ _ _ (by decide)]; norm_num
      simp only [Scalar.val_add,Scalar.val_mul,zero,h.2] at g
      exact g
    · have g := agrees_set h a (Scalar.add (v.getD (position a) Scalar.zero)
        (Scalar.mul (Scalar.ofRaw s.neg s.top.count s.down.count) (v.getD (position k) Scalar.zero)))
      simp only [Scalar.val_add,Scalar.val_mul,scalar_span,h.2] at g
      exact g
  | pivot i j =>
    let a : Spot (Fin n) := (false,i)
    let k : Spot (Fin n) := (true,j)
    have ak : a ≠ k := by simp [a,k]
    have g := agrees_set (agrees_set h a (v.getD (position k) Scalar.zero)) k
      (v.getD (position a) Scalar.zero)
    rw [h.2,h.2] at g
    have eq : Function.update (Function.update x a (x k)) k (x a) = fun t => x ((Equiv.swap a k) t) := by
      funext t
      by_cases e : t = a
      · subst t; simp [ak]
      by_cases e' : t = k
      · subst t; simp
      simp [e,e',Equiv.swap_apply_of_ne_of_ne e e']
    rw [eq] at g
    exact g

private theorem agrees_word (w : List (Lag (Fin n) b)) {v : List Scalar} {x : Spot (Fin n) → ℚ}
    (h : Agrees v x) : Agrees ((w.map encode).foldl (step n) v) (applyWord w x) := by
  induction w generalizing v x with
  | nil => exact h
  | cons o w ih => exact ih (agrees_step h o)

private theorem basis_agrees (j : Spot (Fin n)) : Agrees (basis n (position j)) (Pi.single j 1) := by
  refine ⟨by simp [basis],fun t => ?_⟩
  have ht := position_lt t
  rw [List.getD_eq_getElem _ _ (by simpa [basis] using ht)]
  simp only [basis,List.getElem_map,List.getElem_range]
  by_cases e : j=t
  · subst t; simp
  · simp [position_injective.ne e,Ne.symm e]

private theorem cell (w : List (Lag (Fin n) b)) (i j : Spot (Fin n)) :
    Scalar.val ((column n (w.map encode) (position j)).getD (position i) Scalar.zero) = columns w i j :=
  (agrees_word w (basis_agrees j)).2 i

/-- The raw list computation reads precisely the matrices of the typed address words. -/
theorem equal_encode (p q : List (Lag (Fin n) b)) :
    equal n (p.map encode) (q.map encode) = Interchange.AddressROM.equal p q := by
  apply Bool.eq_iff_iff.mpr
  simp only [equal,List.all_eq_true,List.mem_range,Scalar.eqb_eq_true,
    Interchange.AddressROM.equal,decide_eq_true_eq]
  constructor
  · intro h
    ext i j
    exact ((cell p i j).symm.trans (h (position j) (position_lt j) (position i) (position_lt i))).trans (cell q i j)
  · intro h j hj i hi
    obtain ⟨i,rfl⟩ := position_surj i hi
    obtain ⟨j,rfl⟩ := position_surj j hj
    rw [cell,cell,h]

/-- The primitive-recursive checker validates universal field-width equality. -/
theorem equal_encode_iff (hb : 1 < b) (p q : List (Lag (Fin n) b)) :
    equal n (p.map encode) (q.map encode) = true ↔
      ∀ (f : ℕ) (x : Duplex (Fin n) (Tower b f)), p.foldl (Lag.fire f) x = q.foldl (Lag.fire f) x := by
  rw [equal_encode,Interchange.AddressROM.equal_iff hb]

end Opcode

end NearSquareRoot
end Computability
end OAI
