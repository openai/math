import OAI.Computability.BorderVNP.DiagonalNative
import OAI.Computability.BorderVNP.RoutingMessages

/-!
# Literal, pin and link positions of the border diagonal

The first field of each physical processor is the literal, beginning with the
same program. The extra field of team zero carries the matrix pin consecutively
across its processors. Exterior blocks join equal processor numbers in the
two teams. The interior communication layout can be supplied independently.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.Layout

open VPVNP.UniversalMachine

variable {R r t d link inner n : ℕ} {Edge : Type}

/-- An internal edge name belongs to one team. An exterior bit belongs to an
unordered team pair, one processor number, and one slot of its direct link. -/
abbrev Wire (R r link : ℕ) (Edge : Type) :=
  (Fin (R + 1) × Edge) ⊕ (Routing.Block (R + 1) × Fin r × Fin link)

/-- Both ends of a direct physical link name the same unordered block. -/
def blockOf (u v : Fin (R + 1)) (hne : u ≠ v) : Routing.Block (R + 1) :=
  if huv : u < v then ⟨(u, v), huv⟩ else ⟨(v, u), lt_of_le_of_ne (le_of_not_gt huv) hne.symm⟩

/-- Reading a paired exterior slot at the opposite endpoint uses the same
summation variable. -/
theorem blockOf_swap (u v : Fin (R + 1)) (hne : u ≠ v) :
    blockOf u v hne = blockOf v u hne.symm := by
  rcases lt_or_gt_of_ne hne with h | h <;> simp [blockOf, h, not_lt_of_gt h]

/-- The designated team reads the first `d` available pin bits in processor
order. All later slots and all other teams' pin fields are fixed zeros. -/
def pinSlot (d : ℕ) (u : Fin (R + 1)) (j : Fin r) (a : Fin t) : InputSlot (Fin d) (Wire R r link Edge) :=
  if u = 0 then
    let position := finProdFinEquiv (j, a)
    if h : position.val < d then .pin ⟨position.val, h⟩ else .literal false
  else .literal false

/-- Each supplied pin bit occurs at exactly its processor-field position in team zero. -/
theorem pinSlot_at (hfit : d ≤ r * t) (i : Fin d) :
    let p := finProdFinEquiv.symm (i.castLE hfit)
    pinSlot (Edge := Edge) (link := link) d (0 : Fin (R + 1)) p.1 p.2 = .pin i := by
  dsimp only
  simp [pinSlot, Nat.mod_add_div, i.isLt]

/-- The exterior slot is ordered by the rank of the other team among those
different from the current one, then by its direct-link bit. -/
def exteriorSlot (u : Fin (R + 1)) (j : Fin r) (offset : Fin (R * link)) :
    InputSlot (Fin d) (Wire R r link Edge) :=
  let ij := finProdFinEquiv.symm offset
  .link (.inr (blockOf u (u.succAbove ij.1) (u.ne_succAbove ij.1), j, ij.2))

/-- The tail following the program literal. It includes the remaining
literal values, live pin field, exterior blocks, interior links and padding. -/
def tail (programBits : List Bool) (tailBits : Fin (R + 1) → Fin r → Fin t → Bool)
    (interior : Fin r → Fin inner → Option Edge) (d link pad : ℕ)
    (u : Fin (R + 1)) (j : Fin r) : List (InputSlot (Fin d) (Wire R r link Edge)) :=
  (List.ofFn fun a => InputSlot.literal (tailBits u j a)) ++
    (List.ofFn fun a : Fin (R * link) => exteriorSlot u j a) ++
    (List.ofFn fun a : Fin (programBits.length + t) => pinSlot d u j a) ++
    (List.ofFn fun a => (interior j a).elim (.literal false) fun e => .link (.inl (u, e))) ++
    List.replicate pad (.literal false)

/-- The two literal-width fields use precisely their declared lengths. -/
theorem length_raw (programBits : List Bool) (tailBits : Fin (R + 1) → Fin r → Fin t → Bool)
    (interior : Fin r → Fin inner → Option Edge) (d link pad : ℕ)
    (u : Fin (R + 1)) (j : Fin r) :
    (programBits.map InputSlot.literal ++ tail programBits tailBits interior d link pad u j).length =
      2 * (programBits.length + t) + R * link + inner + pad := by
  simp [tail]
  omega

/-- Each of the `n` inputs is an actual slot, even if it is only fixed padding. -/
def slots (programBits : List Bool) (tailBits : Fin (R + 1) → Fin r → Fin t → Bool)
    (interior : Fin r → Fin inner → Option Edge) (d link : ℕ)
    (fit : 2 * (programBits.length + t) + R * link + inner ≤ n)
    (site : Fin (R + 1) × Fin r) : Fin n → InputSlot (Fin d) (Wire R r link Edge) :=
  let pad := n - (2 * (programBits.length + t) + R * link + inner)
  let raw : List (InputSlot (Fin d) (Wire R r link Edge)) := programBits.map InputSlot.literal ++ tail programBits tailBits interior d link pad site.1 site.2
  have hr : raw.length = n := (length_raw ..).trans (Nat.add_sub_of_le fit)
  fun j => raw.get (j.cast hr.symm)

/-- The actual `n`-bit layout starts with the common program and delivers
exactly the displayed literal tail to the stack interpreter. -/
theorem ofFn_slots (programBits : List Bool) (tailBits : Fin (R + 1) → Fin r → Fin t → Bool)
    (interior : Fin r → Fin inner → Option Edge) (d link : ℕ)
    (fit : 2 * (programBits.length + t) + R * link + inner ≤ n)
    (site : Fin (R + 1) × Fin r) :
    List.ofFn (slots programBits tailBits interior d link fit site) =
      programBits.map InputSlot.literal ++ tail programBits tailBits interior d link
        (n - (2 * (programBits.length + t) + R * link + inner)) site.1 site.2 := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, length_raw]
    omega
  · intros
    rw [List.getElem_ofFn]
    rfl

end Diagonal.Layout

end BorderVNP
end Computability
end OAI
