import OAI.Computability.VPVNP.PrimedStackRAMIndex

/-!
# External memory and the preorder stack

The two frame planes store the stack from bottom to top. The pointer cell
contains its length, so the degree and state of the top frame have index
one less than the pointer. The typed scratch addresses give the frame rules
for the other words in the rectangle.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedStackRAM

open BurstRAM
open scoped Fin.CommRing

variable {R n m H w : ℕ}

/-- Typed parser scratch cells for two groups of `R` input rows, `n` frame slots, `m`
positions, and a histogram indexed by the grammar’s production labels. -/
abbrev Locations (R n m H : ℕ) := Cell R n m (labelCount n m H)

/-- Classical decidable equality on typed parser locations for updating one cell in the
scratch-memory view. -/
noncomputable local instance : DecidableEq (Locations R n m H) := Classical.decEq _

/-- Cell in the degree plane that stores degree minus one for the frame at stack slot `i`. -/
def degCell (i : Fin n) : Locations R n m H := .inr (.inl i)
/-- Cell in the state plane that stores the nonterminal state for the frame at stack slot `i`. -/
def stateCell (i : Fin n) : Locations R n m H := .inr (.inr (.inl i))
/-- Mark for input position `i`, used to detect a repeated position during a parse. -/
def markCell (i : Fin m) : Locations R n m H := .inr (.inr (.inr (.inl i)))
/-- Histogram cell counting uses of the production with dense label index `i`. -/
def countCell (i : Fin (labelCount n m H)) : Locations R n m H := .inr (.inr (.inr (.inr (.inl i))))
/-- Single scratch word holding the current stack length, which also indexes the next free
frame slot. -/
def depthCell : Locations R n m H := .inr (.inr (.inr (.inr (.inr 0))))

/-- Runtime public word table. The input base is the start of the assembled rows. -/
def publicData (w base R n m H : ℕ) : Fin 11 → Word w :=
  let deg := base + 2*R*m
  let sta := deg + n
  let mark := sta + n
  let hist := mark + m
  let T := labelCount n m H
  ![↑deg, ↑sta, ↑mark, ↑hist, ↑(hist+T), ↑n, ↑m, ↑H, ↑base, ↑(H*m*2), ↑T]

/-- Read a typed parser location from external memory using the scratch layout based at `base`. -/
def view (base : ℕ) (mem : Memory w) (c : Locations R n m H) : Word w := mem (address base c)

/-- Write to a typed cell. All other scratch coordinates retain their previous values. -/
def store (base : ℕ) (mem : Memory w) (c : Locations R n m H) (v : Word w) :=
  writeMemory mem (address base c : Word w) v

theorem view_store (base : ℕ) (mem : Memory w) (c : Locations R n m H) (v : Word w)
    (hf : base + size R n m (labelCount n m H) ≤ 2^w) :
    view base (store base mem c v) = Function.update (view base mem) c v := by
  funext a
  have hv : (↑(address base c) : Word w).val = address base c :=
    (Fin.val_natCast ..).trans (Nat.mod_eq_of_lt (address_lt hf c))
  by_cases h : a = c
  · subst a
    simp [view, store, writeMemory, hv]
  · simp [view, store, writeMemory, hv, Function.update_of_ne h,
      show address base a ≠ address base c from fun he => h (address_injective base he)]

theorem view_store_apply (base : ℕ) (mem : Memory w) (c a : Locations R n m H) (v : Word w)
    (hf : base + size R n m (labelCount n m H) ≤ 2^w) :
    view base (store base mem c v) a = if a = c then v else view base mem a := by
  rw [view_store _ _ _ _ hf]
  by_cases ha : a = c
  · subst a
    simp
  · simp [ha]

theorem public_degree (base : ℕ) (i : Fin n) :
    publicData w base R n m H 0 + (i.val : Word w) = ↑(address base (degCell i : Locations R n m H)) := by
  rw [degCell, address_degree, Nat.cast_add]
  rfl

theorem public_state (base : ℕ) (i : Fin n) :
    publicData w base R n m H 1 + (i.val : Word w) = ↑(address base (stateCell i : Locations R n m H)) := by
  rw [stateCell, address_state, Nat.cast_add]
  rfl

theorem public_depth (base : ℕ) :
    publicData w base R n m H 4 = ↑(address base (depthCell : Locations R n m H)) := by
  rw [depthCell, address_depth]
  change (↑(base+2*R*m+n+n+m+labelCount n m H) : Word w) = _
  congr 1
  omega

theorem public_mark (base : ℕ) (i : Fin m) :
    publicData w base R n m H 2 + (i.val : Word w) = ↑(address base (markCell i : Locations R n m H)) := by
  rw [markCell, address_mark, Nat.cast_add]
  change ↑(base+2*R*m+n+n) + (i.val : Word w) = _
  rw [show base+2*R*m+n+n = base+2*R*m+2*n by omega]

theorem public_count (base : ℕ) (i : Fin (labelCount n m H)) :
    publicData w base R n m H 3 + (i.val : Word w) = ↑(address base (countCell i : Locations R n m H)) := by
  rw [countCell, address_hist, Nat.cast_add]
  change ↑(base+2*R*m+n+n+m) + (i.val : Word w) = _
  rw [show base+2*R*m+n+n+m = base+2*R*m+2*n+m by omega]

theorem public_depth_val (base : ℕ) (hf : base + size R n m (labelCount n m H) ≤ 2^w) :
    (publicData w base R n m H 4).val = address base (depthCell : Locations R n m H) := by
  rw [public_depth, Fin.val_natCast, Nat.mod_eq_of_lt (address_lt hf depthCell)]

theorem capacity_fit (base : ℕ) (hf : base + size R n m (labelCount n m H) ≤ 2^w) : n < 2^w := by
  unfold size at hf
  omega

/-- Stack representation for a list of frames in preorder (top first). -/
structure Represents (base : ℕ) (mem : Memory w) (stack : List (Word w × Word w)) : Prop where
  fits : stack.length ≤ n
  depth : (view base mem (depthCell : Locations R n m H)).val = stack.length
  degrees (i : Fin stack.length) :
    view base mem (degCell (i.castLE fits) : Locations R n m H) = stack.reverse[i.val].1
  states (i : Fin stack.length) :
    view base mem (stateCell (i.castLE fits) : Locations R n m H) = stack.reverse[i.val].2

theorem len_word {base : ℕ} {mem : Memory w} {stack : List (Word w × Word w)}
    (hr : Represents (R := R) (n := n) (m := m) (H := H) base mem stack) :
    view base mem (depthCell : Locations R n m H) = (stack.length : Word w) :=
  hr.depth ▸ (Fin.cast_val_eq_self _).symm

/-- Storing a frame in the first free slot and incrementing the depth represents a push. -/
private theorem represents_push {base : ℕ} {mem : Memory w} {stack : List (Word w × Word w)}
    (hr : Represents (R := R) (n := n) (m := m) (H := H) base mem stack)
    (hf : base + size R n m (labelCount n m H) ≤ 2^w) (hc : stack.length < n)
    (d h : Word w) :
    let i : Fin n := ⟨stack.length, hc⟩
    Represents (R := R) (n := n) (m := m) (H := H) base
      (store base (store base (store base mem (degCell i : Locations R n m H) d)
        (stateCell i : Locations R n m H) h) (depthCell : Locations R n m H) (stack.length+1 : ℕ))
      ((d,h) :: stack) := by
  dsimp only
  have hw : stack.length + 1 < 2^w := (Nat.succ_le_of_lt hc).trans_lt (capacity_fit base hf)
  refine ⟨by simpa using hc, ?_, ?_, ?_⟩
  · rw [view_store _ _ _ _ hf, Function.update_self, Fin.val_natCast, Nat.mod_eq_of_lt hw]
    rfl
  all_goals
    intro i
    rcases i with ⟨j, hj⟩
    simp only [view_store_apply _ _ _ _ _ hf, List.reverse_cons]
    by_cases hi : j = stack.length
    · simp [degCell, stateCell, depthCell, Fin.castLE, hi]
    · have hlt : j < stack.length := by simp at hj; omega
      rw [List.getElem_append_left (by simpa using hlt)]
      simp [degCell, stateCell, depthCell, Fin.castLE, hi]
      first | simpa [degCell, Fin.castLE] using hr.degrees ⟨j,hlt⟩ | simpa [stateCell, Fin.castLE] using hr.states ⟨j,hlt⟩

/-- The compiled push inserts the two actual words and preserves every
older pending frame. -/
theorem push_rep {base : ℕ} {mem : Memory w} {stack : List (Word w × Word w)}
    (state : Word w) (regs : Regs w 16)
    (hr : Represents (R := R) (n := n) (m := m) (H := H) base mem stack)
    (hf : base + size R n m (labelCount n m H) ≤ 2^w) (hc : stack.length < n) :
    ∃ es rs mem', trace (publicData w base R n m H) state push regs mem = some (es, rs, mem') ∧
      countProbes es = 4 ∧ Represents (R := R) (n := n) (m := m) (H := H) base mem'
        ((regs 0, regs 1) :: stack) := by
  let pub := publicData w base R n m H
  have hp : (pub 4).val = _ := public_depth_val base hf
  have hw : mem (pub 4).val = (stack.length : Word w) := hp ▸ len_word hr
  have hdepth : (mem (pub 4).val).val = stack.length := hp ▸ hr.depth
  have hcap : mem (pub 4).val < pub 5 := by
    change (mem (pub 4).val).val < (n : Word w).val
    simpa only [hdepth, Fin.val_natCast, Nat.mod_eq_of_lt (capacity_fit base hf)] using hc
  obtain ⟨es, rs, ht, hp', _⟩ := push_spec pub state regs mem hcap
  refine ⟨es, rs, _, ht, hp', ?_⟩
  let i : Fin n := ⟨stack.length, hc⟩
  change Represents base (writeMemory (writeMemory (writeMemory mem (pub 0 + mem (pub 4).val) _)
    (pub 1 + mem (pub 4).val) _) (pub 4) _) _
  rw [hw, show pub 0 + ↑stack.length = _ from public_degree base i,
    show pub 1 + ↑stack.length = _ from public_state base i, show pub 4 = _ from public_depth base]
  simpa only [store, Nat.cast_add, Nat.cast_one] using represents_push hr hf hc (regs 0) (regs 1)

private theorem represents_pop {base : ℕ} {mem : Memory w} {stack : List (Word w × Word w)}
    {d h : Word w} (hr : Represents (R := R) (n := n) (m := m) (H := H) base mem ((d,h)::stack))
    (hf : base + size R n m (labelCount n m H) ≤ 2^w) :
    let mem' := store base mem (depthCell : Locations R n m H) (stack.length : Word w)
    let i : Fin n := ⟨stack.length, hr.fits⟩
    Represents (R := R) (n := n) (m := m) (H := H) base mem' stack ∧
      view base mem' (degCell i : Locations R n m H) = d ∧
      view base mem' (stateCell i : Locations R n m H) = h := by
  dsimp only
  have hc : stack.length < n := hr.fits
  have hw := hc.trans (capacity_fit base hf)
  refine ⟨⟨hc.le, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [view_store_apply _ _ _ _ _ hf, ite_eq_left rfl, Fin.val_natCast, Nat.mod_eq_of_lt hw]
  · rintro ⟨i, hi⟩
    have hd := hr.degrees ⟨i, by simp; omega⟩
    rw [view_store_apply _ _ _ _ _ hf, ite_eq_right (by simp [degCell, depthCell])]
    simp only [List.reverse_cons] at hd
    rw [List.getElem_append_left (by simpa using hi)] at hd
    exact hd
  · rintro ⟨i, hi⟩
    have hs := hr.states ⟨i, by simp; omega⟩
    rw [view_store_apply _ _ _ _ _ hf, ite_eq_right (by simp [stateCell, depthCell])]
    simp only [List.reverse_cons] at hs
    rw [List.getElem_append_left (by simpa using hi)] at hs
    exact hs
  · rw [view_store_apply _ _ _ _ _ hf, ite_eq_right (by simp [degCell, depthCell])]
    simpa [List.reverse_cons, Fin.castLE] using hr.degrees ⟨stack.length, by simp⟩
  · rw [view_store_apply _ _ _ _ _ hf, ite_eq_right (by simp [stateCell, depthCell])]
    simpa [List.reverse_cons, Fin.castLE] using hr.states ⟨stack.length, by simp⟩

/-- The compiled pop returns the abstract top frame in the two destination
registers and represents the exact remaining preorder stack. -/
theorem pop_rep {base : ℕ} {mem : Memory w} {stack : List (Word w × Word w)} {d h : Word w}
    (state : Word w) (regs : Regs w 16)
    (hr : Represents (R := R) (n := n) (m := m) (H := H) base mem ((d,h) :: stack))
    (hf : base + size R n m (labelCount n m H) ≤ 2^w) :
    ∃ es rs mem', trace (publicData w base R n m H) state pop regs mem = some (es, rs, mem') ∧
      countProbes es = 4 ∧ Represents (R := R) (n := n) (m := m) (H := H) base mem' stack ∧
      rs 0 = d ∧ rs 1 = h := by
  let pub := publicData w base R n m H
  let i : Fin n := ⟨stack.length, hr.fits⟩
  let top := mem (pub 4).val - 1
  have hp : (pub 4).val = _ := public_depth_val base hf
  have hdepth : (mem (pub 4).val).val = stack.length+1 := hp ▸ hr.depth
  have hpos : 0 < mem (pub 4).val := by change 0 < (mem _).val; omega
  have htop : top.val = stack.length := by
    rw [show top = mem (pub 4).val - 1 from rfl, Fin.val_sub_one_of_ne_zero hpos.ne', hdepth]
    omega
  have hw : top = (i.val : Word w) := by
    change top = (stack.length : Word w)
    rw [← htop, Fin.cast_val_eq_self]
  obtain ⟨es, rs, ht, hc, _, hd, hs⟩ := pop_spec pub state regs mem hpos
  refine ⟨es, rs, _, ht, hc, ?_⟩
  let mem' := writeMemory mem (pub 4) top
  have hm : mem' = store base mem (depthCell : Locations R n m H) (stack.length : Word w) := by
    rw [show mem' = writeMemory mem (pub 4) top from rfl, hw, show pub 4 = _ from public_depth base]
    rfl
  change Represents base mem' stack ∧ _ ∧ _
  rw [hd, hs]
  change _ ∧ mem' (pub 0 + top).val = d ∧ mem' (pub 1 + top).val = h
  rw [hm, hw, show pub 0 + ↑i.val = _ from public_degree base i,
    show pub 1 + ↑i.val = _ from public_state base i, Fin.val_natCast, Fin.val_natCast,
    Nat.mod_eq_of_lt (address_lt hf (degCell i)), Nat.mod_eq_of_lt (address_lt hf (stateCell i))]
  exact represents_pop hr hf

/-- The location test reads its own mark and succeeds with exactly that mark set. -/
theorem mark_cell {base : ℕ} (mem : Memory w) (state : Word w) (regs : Regs w 16) (j : Fin m)
    (hj : regs 2 = (j.val : Word w)) (hf : base + size R n m (labelCount n m H) ≤ 2^w)
    (hnew : view base mem (markCell j : Locations R n m H) = 0) :
    ∃ es rs, trace (publicData w base R n m H) state mark regs mem =
      some (es, rs, store base mem (markCell j : Locations R n m H) 1) ∧ countProbes es = 2 := by
  let pub := publicData w base R n m H
  have hm : m < 2^w := by unfold size at hf; omega
  have hjm : regs 2 < pub 6 := by
    rw [hj]
    change (j.val : Word w).val < (m : Word w).val
    simpa only [Fin.val_natCast, Nat.mod_eq_of_lt (j.isLt.trans hm), Nat.mod_eq_of_lt hm] using j.isLt
  have he : pub 2 + regs 2 = (address base (markCell j : Locations R n m H) : Word w) :=
    hj ▸ public_mark base j
  have hmem : mem (pub 2 + regs 2).val = 0 := by
    rw [he, Fin.val_natCast, Nat.mod_eq_of_lt (address_lt hf (markCell j))]
    exact hnew
  obtain ⟨es, rs, ht, hc, _⟩ := mark_spec pub state regs mem hjm hmem
  rw [he] at ht
  exact ⟨es, rs, ht, hc⟩

/-- A valid counter increment writes only the indexed production's cell. -/
theorem increment_cell {base : ℕ} (mem : Memory w) (state : Word w) (regs : Regs w 16)
    (j : Fin (labelCount n m H)) (hj : regs 7 = (j.val : Word w))
    (hf : base + size R n m (labelCount n m H) ≤ 2^w)
    (hcount : (view base mem (countCell j : Locations R n m H)).val + 1 < 2^w) :
    ∃ es rs, trace (publicData w base R n m H) state increment regs mem =
      some (es, rs, store base mem (countCell j : Locations R n m H)
        (view base mem (countCell j : Locations R n m H) + 1)) ∧ countProbes es = 2 := by
  let pub := publicData w base R n m H
  have ht : labelCount n m H < 2^w := by unfold size at hf; omega
  have hjt : regs 7 < pub 10 := by
    rw [hj]
    change (j.val : Word w).val < (labelCount n m H : Word w).val
    simpa only [Fin.val_natCast, Nat.mod_eq_of_lt (j.isLt.trans ht), Nat.mod_eq_of_lt ht] using j.isLt
  have he : pub 3 + regs 7 = (address base (countCell j : Locations R n m H) : Word w) :=
    hj ▸ public_count base j
  have hval : mem (pub 3 + regs 7).val = view base mem (countCell j : Locations R n m H) := by
    rw [he, Fin.val_natCast, Nat.mod_eq_of_lt (address_lt hf (countCell j))]
    rfl
  obtain ⟨es, rs, hx, hc, _⟩ := increment_spec pub state regs mem hjt (hval ▸ hcount)
  rw [hval, he] at hx
  exact ⟨es, rs, hx, hc⟩

end PrimedStackRAM

end VPVNP
end Computability
end OAI
