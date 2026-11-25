import OAI.Computability.BorderVNP.CubePhysicalDeclaration

/-! # Fixed binary words for the physical length declaration

Before reading any selectors, all parties know a uniform upper bound on every
advertised row length. The coordinate and all row entries are encoded by
fixed-width words. Every selector tuple admits exactly one passing broadcast
bit assignment, even when the available code space exceeds the legal range.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical

open VPVNP.MotifBase VPVNP.RAMSerialization
open scoped Classical

variable {n d blocks K h : ℕ}

/-- Public bound on any column, independent of the choices of summands. -/
def declarationCap (n d blocks b h s : ℕ) : ℕ :=
  Fintype.card (Packet n d blocks)*(h*s) + Fintype.card (SingleSlot n d blocks (h*b))

/-- Every directional width is bounded by the sum of all selected supply-edge
widths and all retained singleton slots. The latter upper bound is public. -/
theorem cutWidth_le_cap (b s : ℕ) (select : Packet n d blocks → Selector n K h) (j : Fin (n+1)) :
    cutWidth b s select j ≤ declarationCap n d blocks b h s := by
  have packet (p : Packet n d blocks) : crossCount b s select (.inl p) j ≤ h*s := by
    rw [packet_crossCount]
    calc
      _ ≤ ∑ e, payload (onEdge s) (select p).2 e :=
        Finset.sum_le_sum fun _ _ => by split <;> omega
      _ = h*s := by unfold payload; rw [Finset.sum_comm]; simp [onEdge]
  have single (z : SingleSlot n d blocks (h*b)) : crossCount b s select (.inr z) j ≤ 1 :=
    Bool.toNat_le _
  rw [cutWidth, Fintype.sum_sum_type]
  simpa only [declarationCap, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id, Nat.mul_one] using
    Nat.add_le_add (Finset.sum_le_sum (s := (Finset.univ : Finset (Packet n d blocks))) (fun p _ => packet p))
      (Finset.sum_le_sum (s := (Finset.univ : Finset (SingleSlot n d blocks (h*b)))) (fun z _ => single z))

/-- One raw fixed-width binary word for a public range of size `limit`. -/
abbrev Code (limit : ℕ) := Fin (Nat.clog 2 limit) → Bool

/-- Decode a raw public word, including the integers outside the intended range. -/
def readCode (limit : ℕ) (a : Code limit) : ℕ := ((wordBits _).symm a).val

/-- Encode an in-range integer in the fixed number of binary places. -/
def writeCode (limit x : ℕ) (hx : x < limit) : Code limit :=
  wordBits _ ⟨x, hx.trans_le (Nat.le_pow_clog (by decide : 1 < 2) limit)⟩

private theorem read_write (limit x : ℕ) (hx : x < limit) :
    readCode limit (writeCode limit x hx) = x := by simp [readCode, writeCode]

private theorem read_injective (limit : ℕ) : Function.Injective (readCode limit) :=
  Fin.val_injective.comp (wordBits (Nat.clog 2 limit)).symm.injective

/-- A broadcast of one coordinate and one word for each symbol row and each cut. -/
abbrev Broadcast (n d cap : ℕ) :=
  Code (n+1) × (Sym2 (Fin d) → Fin (n+1) → Code (cap+1))

/-- Check the coordinate's range, decode all row entries, and run the genuine
physical declaration checks. Those checks reject surplus row codes as well. -/
def passesBroadcast (b s : ℕ) (select : Packet n d blocks → Selector n K h)
    (a : Broadcast n d (declarationCap n d blocks b h s)) : Prop :=
  ∃ i : Fin (n+1), readCode _ a.1 = i.val ∧
    passesLengths b s select (i,fun r j => readCode _ (a.2 r j))

/-- The unique candidate that the local row checks and least-minimizer check
accept. The width and position of every field are fixed before the selectors. -/
def broadcast (b s : ℕ) (select : Packet n d blocks → Selector n K h) :
    Broadcast n d (declarationCap n d blocks b h s) :=
  let i := chosen b s select
  let D : LengthDeclaration n d := (i,subtotals itemRow (crossCount b s select) i)
  have hp : passesLengths b s select D := (passesLengths_iff ..).mpr rfl
  (writeCode _ i.val i.isLt, fun r j => writeCode _ (D.2 r j)
    (Nat.lt_succ_of_le ((declared_entry_le b s select D hp r j).trans (cutWidth_le_cap b s select j))))

/-- Equality of raw broadcasts follows from the values of every checked word. -/
theorem passesBroadcast_iff (b s : ℕ) (select : Packet n d blocks → Selector n K h)
    (a : Broadcast n d (declarationCap n d blocks b h s)) :
    passesBroadcast b s select a ↔ a = broadcast b s select := by
  constructor
  · rintro ⟨i,hi,hp⟩
    have he := (passesLengths_iff b s select _).mp hp
    have hrow := congrArg Prod.snd he
    have hic : i = chosen b s select := congrArg Prod.fst he
    apply Prod.ext
    · apply read_injective
      simpa only [broadcast,read_write,hic] using hi
    · funext r j
      apply read_injective
      simpa only [broadcast,read_write] using congrFun (congrFun hrow r) j
  · rintro rfl
    refine ⟨chosen b s select, ?_, ?_⟩
    · simp only [broadcast,read_write]
    · apply (passesLengths_iff ..).mpr
      simp only [broadcast,read_write]

/-- Precisely one passing raw bit assignment exists, including for singleton
or empty row ranges and non-power-of-two numbers of groups. -/
theorem unique_passing_broadcast (b s : ℕ) (select : Packet n d blocks → Selector n K h) :
    ∃! a : Broadcast n d (declarationCap n d blocks b h s), passesBroadcast b s select a :=
  ⟨broadcast b s select, (passesBroadcast_iff ..).mpr rfl,
    fun _ ha => (passesBroadcast_iff ..).mp ha⟩

/-- Guessing all physical declaration words and rejecting invalid broadcasts
preserves every original path weight exactly once. -/
theorem sum_passing_broadcast {R : Type*} [AddCommMonoid R]
    (b s : ℕ) (select : Packet n d blocks → Selector n K h) (w : R) :
    (∑ a : Broadcast n d (declarationCap n d blocks b h s),
      if passesBroadcast b s select a then w else 0) = w := by
  simp [passesBroadcast_iff]

end Cube.Physical

end BorderVNP
end Computability
end OAI
