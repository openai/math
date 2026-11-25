import OAI.Computability.BorderVNP.CubeScatterLayout
import OAI.Computability.BorderVNP.CubePhysicalDeclaration

/-! # The selector and crossing streams consumed by a physical packet

The per-packet crossing stream visits the directed edges in bank order and copies
exactly the selected prefix of every edge in the chosen direction. The length
is the packet's contribution to its broadcast row.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Scatter

open RoutingISA VPVNP.BurstRAM VPVNP.MotifBase DiagonalResidueRAM Tally

/-- A bit in the routed selector prefix, if this is a selector position. -/
def Position.selectorBit : Position → Option Bool
  | .selector b => some b | _ => none

/-- A bit in the routed crossing suffix, if this position lies on the chosen cut. -/
def Position.crossBit : Position → Option Bool
  | .crossing b => some b | _ => none

/-- Values of the two routed input streams in memory. -/
def BitsAt {w : ℕ} (m : Memory w) (addr : ℕ) (bs : List Bool) : Prop :=
  ∀ j : Fin bs.length, m (addr+j.val) = wordBit w bs[j]

/-- The head of a routed word is the bit at its incoming cursor. -/
theorem BitsAt.head {w : ℕ} {m : Memory w} {addr : ℕ} {b : Bool} {bs : List Bool}
    (h : BitsAt m addr (b::bs)) : m addr = wordBit w b := by simpa using h 0

/-- Reading one routed word exposes the remaining stream at the next address. -/
theorem BitsAt.tail {w : ℕ} {m : Memory w} {addr : ℕ} {b : Bool} {bs : List Bool}
    (h : BitsAt m addr (b::bs)) : BitsAt m (addr+1) bs := by
  intro j
  simpa [Nat.add_assoc,Nat.add_comm 1] using h j.succ

/-- The physical cursor counters after this scatter. -/
theorem advance_counts (ps : List Position) (c : Cursor) :
    advance ps c = ⟨c.selector+(ps.filterMap Position.selectorBit).length,
      c.crossing+(ps.filterMap Position.crossBit).length,c.dest+ps.length⟩ := by
  induction ps generalizing c with
  | nil => simp [advance]
  | cons p ps ih =>
    rw [advance,ih]
    cases p <;> simp [List.filterMap_cons,Cursor.next,Position.selectorBit,Position.crossBit,Nat.add_assoc,Nat.add_comm 1]

/-- The two actual routed lists in their disjoint source region supply the hypotheses of the native image theorem. -/
theorem prepared_of_streams {w : ℕ} (src : Set ℕ) (ps : List Position) (c : Cursor) (m : Memory w)
    (sels : BitsAt m c.selector (ps.filterMap Position.selectorBit))
    (cross : BitsAt m c.crossing (ps.filterMap Position.crossBit))
    (selIn : ∀ j < (ps.filterMap Position.selectorBit).length, c.selector+j ∈ src ∧ c.selector+j < 2^w)
    (crossIn : ∀ j < (ps.filterMap Position.crossBit).length, c.crossing+j ∈ src ∧ c.crossing+j < 2^w)
    (destOut : ∀ j < ps.length, c.dest+j ∉ src ∧ c.dest+j < 2^w) : Prepared src ps c m := by
  induction ps generalizing c with
  | nil => trivial
  | cons p ps ih =>
    have dest := destOut 0 (by simp)
    simp only [Nat.add_zero] at dest
    have dest' (j : ℕ) (hj : j < ps.length) := destOut (j+1) (by simpa using hj)
    cases p with
    | selector b =>
      simp only [List.filterMap_cons,Position.selectorBit,Position.crossBit,List.length_cons] at sels cross selIn crossIn
      have hdr := selIn 0 (by omega)
      refine ⟨⟨dest.1,dest.2,by simpa using hdr.1,by simpa using hdr.2,sels.head⟩,?_⟩
      exact ih (c.next (.selector b)) sels.tail cross
        (fun j hj => by simpa [Cursor.next,Nat.add_assoc,Nat.add_comm 1] using selIn (j+1) (by omega))
        crossIn (fun j hj => by simpa [Cursor.next,Nat.add_assoc,Nat.add_comm 1] using dest' j hj)
    | crossing b =>
      simp only [List.filterMap_cons,Position.selectorBit,Position.crossBit,List.length_cons] at sels cross selIn crossIn
      have hdr := crossIn 0 (by omega)
      refine ⟨⟨dest.1,dest.2,by simpa using hdr.1,by simpa using hdr.2,cross.head⟩,?_⟩
      exact ih (c.next (.crossing b)) sels cross.tail selIn
        (fun j hj => by simpa [Cursor.next,Nat.add_assoc,Nat.add_comm 1] using crossIn (j+1) (by omega))
        (fun j hj => by simpa [Cursor.next,Nat.add_assoc,Nat.add_comm 1] using dest' j hj)
    | localBit b | unused =>
      refine ⟨⟨dest.1,dest.2,trivial⟩,?_⟩
      exact ih _ sels cross selIn crossIn (fun j hj => by simpa [Cursor.next,Nat.add_assoc,Nat.add_comm 1] using dest' j hj)

variable {n b h K s : ℕ}

private theorem filterMap_length {α β : Type*} (xs : List α) (f : α → Option β) :
    (xs.filterMap f).length = (xs.map fun x => (f x).isSome.toNat).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases hx : f x <;> simp [hx,ih, Nat.add_comm]

private theorem prefix_count {m k : ℕ} (hk : k ≤ m) :
    (∑ j : Fin m, (if j.val < k then 1 else 0 : ℕ)) = k := by
  rw [Fin.sum_univ_eq_sum_range (fun j => if j < k then 1 else 0)]
  have cut : (Finset.range m).filter (· < k) = Finset.range k := by ext j; simp; omega
  rw [← Finset.sum_filter,cut]
  simp

/-- The number of copied crossing bits is independent of which of the two endpoint groups performs the scatter. -/
theorem body_cross_length (u : Selector n K h) (i : Fin (n+1)) (bit : Bool)
    (x : Ends n → Fin (h*b) → Bool) (z : (e : Edge (n+1)) → Fin (payload (onEdge s) u.2 e) → Bool) :
    ((bodyPositions u i bit x z).filterMap Position.crossBit).length =
      ∑ v : Vertex (n+1), payload (onEdge s) u.2 (v,i) := by
  classical
  rw [filterMap_length]
  simp only [bodyPositions,List.map_ofFn,List.sum_ofFn,Function.comp_def]
  rw [← Equiv.sum_comp (bodyOrder n b h s)]
  simp only [Equiv.symm_apply_apply,Fintype.sum_sum_type,Fintype.sum_prod_type]
  have hd (e : Ends n) (j : Fin (h*b)) :
      (Position.crossBit (ownedPosition u i bit x z (.inl (e,j)))).isSome.toNat = 0 := by
    simp only [ownedPosition]
    split_ifs <;> rfl
  have he (e : Edge (n+1)) (j : Fin (h*s)) :
      (Position.crossBit (ownedPosition u i bit x z (.inr (e,j)))).isSome.toNat =
        (if e.2 = i then (if j.val < payload (onEdge s) u.2 e then 1 else 0) else 0) := by
    simp only [ownedPosition]
    split_ifs <;> rfl
  simp only [hd,he,Finset.sum_const_zero,zero_add]
  simp [Finset.sum_ite_irrel,prefix_count (supplyWidth_le u _ s)]

/-- An owned physical packet consumes precisely its contribution to the verified declaration row. -/
theorem body_crossCount {d blocks : ℕ} (select : Packet n d blocks → Selector n K h)
    (p : Packet n d blocks) (i : Fin (n+1)) (bit : Bool)
    (x : Ends n → Fin (h*b) → Bool) (z : (e : Edge (n+1)) → Fin (payload (onEdge s) (select p).2 e) → Bool) :
    ((bodyPositions (select p) i bit x z).filterMap Position.crossBit).length =
      Physical.crossCount b s select (.inl p) i := body_cross_length ..

end Cube.Scatter

end BorderVNP
end Computability
end OAI
