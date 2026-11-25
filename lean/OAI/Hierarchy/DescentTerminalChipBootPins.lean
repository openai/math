import OAI.Hierarchy.DescentTerminalChipBootWords
import OAI.Hierarchy.DescentTerminalChipPins
import OAI.Hierarchy.ProtocolRAMStaticSlabs

namespace OAI
/-! # The physical suffix of four shared proposal views and six public tables -/
namespace Hierarchy.DescentTerminalChipBootWords
open DescentTerminalChipPins Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.Diagonal
open scoped BigOperators Classical Fin.CommRing
noncomputable section

variable {K W q p : ℕ}

private theorem separated (K W q p codes : ℕ) {i j : Fin 10} (before : i < j) :
    «begin» K W q p codes i + 2^(bits K W q p codes i) ≤ «begin» K W q p codes j := by
  let size := fun c : Fin 10 => 2^(bits K W q p codes c)
  have bound : (∑ c : Fin 10, ((if c < i then size c else 0) +
      (if c = i then size i else 0))) ≤ ∑ c : Fin 10, if c < j then size c else 0 := by
    apply Finset.sum_le_sum
    intro c _
    by_cases eqn : c = i
    · subst c
      simp [before]
    · by_cases earlier : c < i
      · simp [earlier,eqn,earlier.trans before]
      · simp [earlier,eqn]
  simpa [«begin»,size,Finset.sum_add_distrib] using bound

private def inside (K W q p codes a : ℕ) (c : Fin 10) : Prop :=
  «begin» K W q p codes c ≤ a ∧ a < «begin» K W q p codes c + 2^(bits K W q p codes c)

theorem bank_lt_total (K W q p codes : ℕ) (col : Fin 10) {i : ℕ}
    (live : i < 2^(bits K W q p codes col)) : «begin» K W q p codes col+i < total K W q p codes := by
  let size := fun c : Fin 10 => 2^(bits K W q p codes c)
  have bound : (∑ c : Fin 10, ((if c < col then size c else 0) +
      (if c = col then size col else 0))) ≤ ∑ c : Fin 10, size c := by
    apply Finset.sum_le_sum
    intro c _
    by_cases eqn : c = col
    · subst c
      simp
    · by_cases earlier : c < col <;> simp [earlier,eqn]
  apply (Nat.add_lt_add_left live _).trans_le
  simpa [«begin»,total,size,Finset.sum_add_distrib] using bound

private def owner (K W q p codes : ℕ) : ℕ → Option (Fin 10) :=
  ProtocolRAMStaticSlabs.owner («begin» K W q p codes)
    (fun c => «begin» K W q p codes c + 2^(bits K W q p codes c))

private theorem owner_eq (K W q p codes a : ℕ) (i : Fin 10) (live : inside K W q p codes a i) :
    owner K W q p codes a = some i :=
  ProtocolRAMStaticSlabs.owner_of_inside (lo := «begin» K W q p codes)
    (hi := fun c => «begin» K W q p codes c + 2^(bits K W q p codes c))
    (ProtocolRAMStaticSlabs.disjoint_of_order (fun _ _ before => separated K W q p codes before)) live

/-- A relative initial memory read selects one of the ten consecutive dyadic banks. -/
def back (z : Inputs K W q p → Bool) (w codes : ℕ) : Memory w := fun a =>
  match owner K W q p codes a with
  | some c => words z w codes c (a-«begin» K W q p codes c)
  | none => 0

theorem back_read (z : Inputs K W q p → Bool) (w codes : ℕ) (col : Fin 10) (i : ℕ)
    (live : i < 2^(bits K W q p codes col)) :
    back z w codes («begin» K W q p codes col+i) = words z w codes col i := by
  have hit : inside K W q p codes («begin» K W q p codes col+i) col :=
    ⟨Nat.le_add_right ..,Nat.add_lt_add_left live _⟩
  simp only [back,owner_eq K W q p codes _ col hit,Nat.add_sub_cancel_left]

theorem back_read_need (z : Inputs K W q p → Bool) (w codes : ℕ) (col : Fin 10) (i : ℕ)
    (live : i < need K W q p codes col) :
    back z w codes («begin» K W q p codes col+i) = words z w codes col i :=
  back_read z w codes col i (live.trans_le (Nat.le_pow_clog (by decide : 1 < 2) _))

private def cellPin (K W q p w codes : ℕ) (col : Fin 10) (i : ℕ) (b : Fin (w+1)) :
    Inputs K W q p ⊕ Bool :=
  if col.val < 4 then
    DescentTerminalChipPins.pin (decide (2 ≤ col.val)) (decide (col.val % 2 = 1)) i b
  else
    .inr (TraceWords.bits (TraceBanks.wide (words (K:=K) (W:=W) (q:=q) (p:=p)
      (fun _ => false) w codes col i)) b)

private theorem cellPin_read (z : Inputs K W q p → Bool) (w codes : ℕ) (room : q*(W*p) ≤ w)
    (col : Fin 10) (i : ℕ) (b : Fin (w+1)) :
    (cellPin K W q p w codes col i b).elim z id =
      TraceWords.bits (TraceBanks.wide (words z w codes col i)) b := by
  fin_cases col <;> first
    | exact DescentTerminalChipPins.pin_read room z false false i b
    | exact DescentTerminalChipPins.pin_read room z false true i b
    | exact DescentTerminalChipPins.pin_read room z true false i b
    | exact DescentTerminalChipPins.pin_read room z true true i b
    | rfl

/-- A literal table cell supplies its own bit. The proposal views retain the shared input pin names. -/
def pin (K W q p w codes a : ℕ) (b : Fin (w+1)) : Inputs K W q p ⊕ Bool :=
  match owner K W q p codes a with
  | some c => cellPin K W q p w codes c (a-«begin» K W q p codes c) b
  | none => .inr false

theorem pin_read (z : Inputs K W q p → Bool) (w codes : ℕ) (room : q*(W*p) ≤ w)
    (a : ℕ) (b : Fin (w+1)) :
    (pin K W q p w codes a b).elim z id = TraceWords.bits (TraceBanks.wide (back z w codes a)) b := by
  unfold pin back
  cases h : owner K W q p codes a with
  | some c => exact cellPin_read z w codes room c _ b
  | none => simp [TraceBanks.wide,TraceWords.bits]

/-- Pins for appending this physical memory immediately after the original header. -/
def backPin (K W q p w codes : ℕ) (x : Fin (total K W q p codes) × Fin (w+1)) :
    Inputs K W q p ⊕ Bool := pin K W q p w codes x.1.val x.2

theorem backPin_read (z : Inputs K W q p → Bool) (w codes : ℕ) (room : q*(W*p) ≤ w)
    (x : Fin (total K W q p codes) × Fin (w+1)) :
    (backPin K W q p w codes x).elim z id =
      TraceWords.bits (TraceBanks.wide (back z w codes x.1.val)) x.2 :=
  pin_read z w codes room x.1.val x.2

/-- Retaining the original suffix suffices for every live cell, including
the terminal scalar pointer table. -/
theorem boot_of_suffix (z : Inputs K W q p → Bool) (w codes : ℕ) (L : DescentTerminalEmitter.Layout)
    (base empty : ℕ) (m : Memory w)
    (kept : ∀ j < total K W q p codes, m (base+j) = back z w codes j) :
    let B := chipBanks (K:=K) (W:=W) (q:=q) (p:=p) codes L base empty
    DescentTerminalEmitter.Boot B m z ∧ ∀ j : Fin (codes+1), m (B.scalar.pointer.base+j.val) =
      ((DescentTerminalScalarDispatch.pointers (fun a : Fin codes => a.val*2^(q*(W*p))))[j.val]'(by
        simpa [DescentTerminalScalarDispatch.pointers] using j.isLt) : Word w) := by
  have read (col : Fin 10) (i : ℕ) (live : i < need K W q p codes col) :
      m ((bank K W q p codes base col).base+i) = words z w codes col i := by
    have padded : i < 2^(bits K W q p codes col) :=
      live.trans_le (Nat.le_pow_clog (by decide : 1 < 2) _)
    change m ((base+«begin» K W q p codes col)+i) = _
    rw [Nat.add_assoc, kept _ (bank_lt_total K W q p codes col padded)]
    exact back_read_need z w codes col i live
  exact ⟨source (codes:=codes) (L:=L) (base:=base) (empty:=empty) z m read,
    scalar_table (codes:=codes) (L:=L) (base:=base) (empty:=empty) z m
      (fun j => read 9 j.val j.isLt)⟩

end
end Hierarchy.DescentTerminalChipBootWords

end OAI
