import OAI.ThreeFlat.Diagonal.TraceSlotComparator
import OAI.Computability.VPVNP.RAMSortReplay

namespace OAI
/-! # Computing the selected output slot of a comparator stage -/

namespace ThreeFlat.Diagonal.TraceSortSite

open Computability.VPVNP.BurstRAM Computability.VPVNP.RAMSerialization Computability.VPVNP.RAMSort
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr)
open TraceSlots TraceWords

variable {σ : Type*} {w d : ℕ}

abbrev SlotAddr (w : ℕ) (σ : Type*) := Fin 7 → Fin w → σ
abbrev Narrow (w : ℕ) := Option (WordRecord w)
def ReadSlot (hw : 2 ≤ w) (x : σ → Bool) (a : SlotAddr w σ) (r : Narrow w) : Prop :=
  ∀ f j, x (a f j) = bits (fields hw r f) j

private def pairPort (a b : SlotAddr w σ) (i : Pin w) : σ :=
  if i.1 = 0 then a i.2.1 i.2.2 else b i.2.1 i.2.2

def ltPort (a b : SlotAddr w σ) : Expr σ := (lexCheck 0 1 keyIndices).rename (pairPort a b)
def eqPort (a b : SlotAddr w σ) : Expr σ := (sameSlot 0 1).rename (pairPort a b)

private theorem pairPort_congr {τ : Type*} {a b : SlotAddr w σ} {c d : SlotAddr w τ}
    {x : σ → Bool} {y : τ → Bool}
    (ha : ∀ f j, x (a f j) = y (c f j)) (hb : ∀ f j, x (b f j) = y (d f j)) :
    x ∘ pairPort a b = y ∘ pairPort c d := by
  funext i
  dsimp [pairPort]
  split
  · exact ha _ _
  · exact hb _ _

theorem ltPort_congr {τ : Type*} {a b : SlotAddr w σ} {c d : SlotAddr w τ}
    {x : σ → Bool} {y : τ → Bool}
    (ha : ∀ f j, x (a f j) = y (c f j)) (hb : ∀ f j, x (b f j) = y (d f j)) :
    (ltPort a b).eval x = (ltPort c d).eval y := by
  simp only [ltPort, Expr.eval_rename]
  exact congrArg (fun t => (lexCheck (w := w) 0 1 keyIndices).eval t) (pairPort_congr ha hb)

theorem eqPort_congr {τ : Type*} {a b : SlotAddr w σ} {c d : SlotAddr w τ}
    {x : σ → Bool} {y : τ → Bool}
    (ha : ∀ f j, x (a f j) = y (c f j)) (hb : ∀ f j, x (b f j) = y (d f j)) :
    (eqPort a b).eval x = (eqPort c d).eval y := by
  simp only [eqPort, Expr.eval_rename]
  exact congrArg (fun t => (sameSlot (w := w) 0 1).eval t) (pairPort_congr ha hb)

theorem ltPort_eval (hw : 2 ≤ w) (x : σ → Bool) (a b : SlotAddr w σ) (u v : Narrow w)
    (ha : ReadSlot hw x a u) (hb : ReadSlot hw x b v) :
    (ltPort a b).eval x = true ↔ toOrdered u < toOrdered v := by
  rw [ltPort, Expr.eval_rename]
  exact (lexCheck_true hw _ 0 1 u v (by simpa [ReadSlot,Represents,pairPort] using ha)
    (by simpa [ReadSlot,Represents,pairPort] using hb) keyIndices).trans (keyLess_iff _ _ _)

theorem eqPort_eval (hw : 2 ≤ w) (x : σ → Bool) (a b : SlotAddr w σ) (u v : Narrow w)
    (ha : ReadSlot hw x a u) (hb : ReadSlot hw x b v) :
    (eqPort a b).eval x = true ↔ u = v := by
  rw [eqPort, Expr.eval_rename, sameSlot_at hw _ 0 1 v (by simpa [ReadSlot, Represents,pairPort] using hb)]
  change (∀ f j, x (a f j) = bits (fields hw v f) j) ↔ u = v
  constructor
  · intro h
    apply fields_injective hw
    funext f
    apply bits_injective
    funext j
    exact (ha f j).symm.trans (h f j)
  · rintro rfl
    exact ha

def pickSlot (lo : Bool) (a b : Narrow w) : Narrow w :=
  if toOrdered a < toOrdered b then (if lo then a else b) else (if lo then b else a)

def pick (lo : Bool) (a b : SlotAddr w σ) (f : Fin 7) (j : Fin w) : Expr σ :=
  Expr.mux (ltPort a b) (.input (if lo then a f j else b f j))
    (.input (if lo then b f j else a f j))

theorem pick_congr {τ : Type*} {a b : SlotAddr w σ} {c d : SlotAddr w τ}
    {x : σ → Bool} {y : τ → Bool}
    (ha : ∀ f j, x (a f j) = y (c f j)) (hb : ∀ f j, x (b f j) = y (d f j))
    (lo : Bool) (f : Fin 7) (j : Fin w) :
    (pick lo a b f j).eval x = (pick lo c d f j).eval y := by
  cases lo <;> simp [pick, Expr.eval_mux, Expr.eval, ltPort_congr ha hb, ha, hb]

theorem pick_eval (hw : 2 ≤ w) (x : σ → Bool) (lo : Bool) (a b : SlotAddr w σ) (u v : Narrow w)
    (ha : ReadSlot hw x a u) (hb : ReadSlot hw x b v) (f : Fin 7) (j : Fin w) :
    (pick lo a b f j).eval x = bits (fields hw (pickSlot lo u v) f) j := by
  have h := ltPort_eval hw x _ _ _ _ ha hb
  cases lo <;> by_cases hlt : toOrdered u < toOrdered v <;>
    simp [pick, pickSlot, h, hlt, Expr.eval, ha f j, hb f j]

theorem pick_ordered (lo : Bool) (a b : Narrow w) :
    toOrdered (pickSlot lo a b) =
      (if lo then min (toOrdered a) (toOrdered b) else max (toOrdered a) (toOrdered b)) := by
  by_cases h : toOrdered a < toOrdered b
  · cases lo <;> simp [pickSlot, h, min_eq_left h.le, max_eq_right h.le]
  · have hb := le_of_not_gt h
    cases lo <;> simp [pickSlot, h, min_eq_right hb, max_eq_left hb]

theorem pick_size (lo : Bool) (a b : SlotAddr w σ) (f : Fin 7) (j : Fin w) :
    (pick lo a b f j).size ≤ 500*(w+1) := by
  have h := lexCheck_size (w := w) 0 1 keyIndices
  change _ ≤ 7*(34*w+4)+1 at h
  simp only [pick, Expr.mux, Expr.size, ltPort, Expr.size_rename]
  omega

theorem eqPort_size (a b : SlotAddr w σ) : (eqPort a b).size ≤ 80*(w+1) := by
  have h := sameSlot_size (w := w) 0 1
  simp only [eqPort, Expr.size_rename]
  omega

/-- Single-stage addresses depend only on the phase, stride and local offset. -/
def other {α : Type*} (s : Stage (1+d)) (v : Fin (2^d)) (send : Sends 1 d s α)
    (cur : Fin 2 → α) (i : Fin 2) : α :=
  if hc : 1 ≤ s.stride then send hc (sourceSite s hc v) i
  else cur ⟨partner s.stride i, partner_lt i.isLt (Nat.lt_of_not_ge hc)⟩

def lowOutput (s : Stage (1+d)) (v : Fin (2^d)) (i : Fin 2) : Bool :=
  let g := v.val*2 + i.val
  if g < partner s.stride g then phaseDirection s.phase g else !(phaseDirection s.phase g)

def next (s : Stage (1+d)) (v : Fin (2^d)) (send : Sends 1 d s (Narrow w))
    (cur : Fin 2 → Narrow w) (i : Fin 2) : Narrow w :=
  pickSlot (lowOutput s v i) (cur i) (other s v send cur i)

theorem next_ordered (s : Stage (1+d)) (v : Fin (2^d)) (send : Sends 1 d s (Narrow w))
    (cur : Fin 2 → Narrow w) :
    toOrdered ∘ next s v send cur =
      localLayer s (fun h u j => toOrdered (send h u j)) v (toOrdered ∘ cur) := by
  funext i
  have ho : toOrdered (other s v send cur i) =
      other s v (fun h u j => toOrdered (send h u j)) (toOrdered ∘ cur) i := by
    unfold other
    split <;> rfl
  change toOrdered (pickSlot _ _ _) = _
  rw [pick_ordered, ho]
  change (if lowOutput s v i then min _ _ else max _ _) =
      (if v.val*2+i.val < partner s.stride (v.val*2+i.val) then lower _ _ _ else upper _ _ _)
  by_cases h : v.val*2+i.val < partner s.stride (v.val*2+i.val) <;>
    cases e : phaseDirection s.phase (v.val*2+i.val) <;>
    simp [h,e,lowOutput,lower,upper,min_comm,max_comm,other]

end ThreeFlat.Diagonal.TraceSortSite

end OAI
