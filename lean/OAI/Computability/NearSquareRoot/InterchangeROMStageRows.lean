import OAI.Computability.NearSquareRoot.InterchangeROMStageMoves
import OAI.Computability.NearSquareRoot.InterchangeROMStageVerifyIndex

/-! # Addressing the packed ground components of an interchange stage -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMStage
open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip

/-- The physical row associated to every role and ground component. -/
def blocks {A : Type} (roles : List Role) (lanes : ℕ) (x : Role → ℕ → A) : List A :=
  roles.flatMap fun r => (List.range lanes).map (x r)

theorem length_blocks {A : Type} (roles : List Role) (d : ℕ) (x : Role → ℕ → A) :
    (blocks roles d x).length = roles.length*d := by
  induction roles with
  | nil => simp [blocks]
  | cons a l ih =>
    change (((List.range d).map _ ) ++ blocks l d x).length = _
    simp [ih,Nat.succ_mul,Nat.add_comm]

theorem blocks_get {A : Type} (roles : List Role) (d : ℕ) (x : Role → ℕ → A)
    (v : Role) (hv : v ∈ roles) (j : ℕ) (hj : j < d) :
    (blocks roles d x)[roles.idxOf v*d+j]? = some (x v j) := by
  induction roles with
  | nil => cases hv
  | cons a l ih =>
    change (((List.range d).map (x a)) ++ blocks l d x)[(a::l).idxOf v*d+j]? = _
    by_cases e : a = v
    · subst a
      simp [List.getElem?_append_left (show j < ((List.range d).map (x v)).length by simpa),
        List.getElem?_eq_getElem (show j < ((List.range d).map (x v)).length by simpa)]
    · have hh : v ∈ l := (List.mem_cons.mp hv).resolve_left (Ne.symm e)
      rw [List.idxOf_cons_ne _ e,Nat.succ_mul,List.getElem?_append_right (by simp; omega)]
      simp only [List.length_map,List.length_range]
      convert ih hh using 2
      omega

theorem source_blocks (roles : List Role) (d : ℕ) (x : Role → ℕ → Tree)
    (v : Role) (hv : v ∈ roles) (j : ℕ) (hj : j < d) :
    InterchangeROM.source (blocks roles d x) (roles.idxOf v*d+j) = x v j := by
  simp [InterchangeROM.source,blocks_get roles d x v hv j hj]

namespace Frame.Realization

variable {g : Frame} (r : Realization g) {n d : ℕ}
  {src : r.Boundary (n+1) → r.Boundary n} {mv : r.Boundary (n+1) → r.NativeMove}

private theorem route_map {A : Type} (f : ℕ × Frame.Move → A) :
    ((Frame.route g d n).map f) = blocks (Frame.bank g (n+1)) d (fun v j =>
      f ((Frame.bank g n).idxOf (Frame.leg g n v).1*d+j,(Frame.leg g n v).2)) := by
  simp [Frame.route,blocks,List.map_flatMap,List.map_map,Function.comp_def]

/-- The numerical source rank retrieves the whole typed ground row at every
stage boundary, including when the input and output bank sizes differ. -/
theorem route_rows (ok : r.CorrectRoute n src mv) (act : Frame.Move → Tree → Tree)
    (x y : Role → ℕ → Tree) (h : ∀ (b : r.Boundary (n+1)) (k : Fin d),
      act (r.operand (mv b)) (x (r.code n (src b)) k.val) = y (r.code (n+1) b) k.val) :
    let rows := blocks (Frame.bank g n) d x
    ((Frame.route g d n).map (fun (a,m) => act m (InterchangeROM.source rows a))) =
      blocks (Frame.bank g (n+1)) d y := by
  dsimp only
  rw [route_map]
  apply List.flatMap_congr
  intro v hv
  obtain ⟨b,rfl⟩ := ((r.code_codec (n+1)).image v).mp hv
  apply List.map_congr_left
  intro k hk
  have hk' := List.mem_range.mp hk
  simp only [ok b]
  rw [source_blocks _ _ _ _ (r.code_mem n _) _ hk']
  exact h b ⟨k,hk'⟩

/-- Every emitted route instruction satisfies its physical domain contract
as soon as every typed row instruction satisfies it. -/
theorem valid_route {T : Type} (model : InterchangeROM.Model T Frame.Move)
    (ok : r.CorrectRoute n src mv) (x : Role → ℕ → Tree)
    (h : ∀ (b : r.Boundary (n+1)) (k : Fin d),
      model.moveDomain (r.operand (mv b)) (x (r.code n (src b)) k.val)) :
    model.Valid (blocks (Frame.bank g n) d x) (.inr (Frame.route g d n)) := by
  intro c hc
  obtain ⟨v,hv,hs⟩ := List.mem_flatMap.mp hc
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hs
  obtain ⟨b,rfl⟩ := ((r.code_codec (n+1)).image v).mp hv
  have hk' := List.mem_range.mp hk
  change ((Frame.bank g n).idxOf (Frame.leg g n (r.code (n+1) b)).1*d+k <
      (blocks (Frame.bank g n) d x).length) ∧ model.moveDomain (Frame.leg g n (r.code (n+1) b)).2
        (InterchangeROM.source _ ((Frame.bank g n).idxOf (Frame.leg g n (r.code (n+1) b)).1*d+k))
  rw [ok b]
  constructor
  · rw [length_blocks]
    change (Frame.bank g n).idxOf (r.code n (src b))*d+k < (Frame.bank g n).length*d
    have lt := r.physRank_lt n (src b)
    have bound := Nat.mul_le_mul_right d (Nat.succ_le_of_lt lt)
    rw [Nat.succ_mul] at bound
    omega
  · rw [source_blocks _ _ _ _ (r.code_mem n _) _ hk']
    exact h b ⟨k,hk'⟩

end Frame.Realization
end InterchangeROMStage

end NearSquareRoot
end Computability
end OAI
