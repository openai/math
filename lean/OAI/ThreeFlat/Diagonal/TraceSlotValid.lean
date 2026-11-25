import OAI.ThreeFlat.Diagonal.TraceSortSelect
import OAI.ThreeFlat.Diagonal.TraceSlotFormat

namespace OAI
/-! # Canonicality gates for the bit representation of a sorting message -/

namespace ThreeFlat.Diagonal.TraceSortSite

open Computability.VPVNP.BurstRAM Computability.VPVNP.RAMSerialization Computability.VPVNP.RAMMemory
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr)
open TraceSlots TraceWords

variable {σ : Type*} {w : ℕ}

def pinWords (x : σ → Bool) (a : SlotAddr w σ) : Fin 7 → Word w :=
  fun f => (wordBits w).symm fun j => x (a f j)

theorem bits_pinWords (x : σ → Bool) (a : SlotAddr w σ) (f : Fin 7) (j : Fin w) :
    bits (pinWords x a f) j = x (a f j) := by
  change (pinWords x a f).val.testBit j = _
  rw [Computability.VPVNP.LiveHeader.testBit_wordBits]
  exact congrFun ((wordBits w).apply_symm_apply _) j

private def fill (k : Option Kind) (v : Fin 7 → Word w) : Narrow w :=
  k.map fun t => ⟨t,v 1,v 6,v 3,v 4⟩

private def candidate (hw : 2 ≤ w) (k : Option Kind) (a : SlotAddr w σ)
    (f : Fin 7) (j : Fin w) : Expr σ :=
  if k.isSome ∧ (f = 1 ∨ f = 3 ∨ f = 4 ∨ f = 6) then .input (a f j)
  else .const (bits (fields hw (fill k (fun _ => 0)) f) j)

private theorem candidate_eval (hw : 2 ≤ w) (k : Option Kind) (a : SlotAddr w σ)
    (x : σ → Bool) (f : Fin 7) (j : Fin w) :
    (candidate hw k a f j).eval x = bits (fields hw (fill k (pinWords x a)) f) j := by
  cases k <;> fin_cases f <;> simp [candidate, fill, fields, Expr.eval, bits_pinWords]

private def acceptKind (hw : 2 ≤ w) (k : Option Kind) (a : SlotAddr w σ) : Expr σ :=
  allBits fun f => sameWord (fun j => .input (a f j)) (candidate hw k a f)

private theorem acceptKind_at (hw : 2 ≤ w) (k : Option Kind) (a : SlotAddr w σ) (x : σ → Bool) :
    (acceptKind hw k a).eval x = true ↔ ReadSlot hw x a (fill k (pinWords x a)) := by
  simp [acceptKind, sameWord_true, Expr.eval, ReadSlot, candidate_eval]

def valid (hw : 2 ≤ w) (a : SlotAddr w σ) : Expr σ :=
  Expr.disjoin ([none,some .init,some .read,some .write].map fun k => acceptKind hw k a)

theorem valid_at (hw : 2 ≤ w) (a : SlotAddr w σ) (x : σ → Bool) :
    (valid hw a).eval x = true ↔ ∃ r, ReadSlot hw x a r := by
  rw [valid, Expr.eval_disjoin_true]
  constructor
  · rintro ⟨e,he,hx⟩
    obtain ⟨k,_,rfl⟩ := List.mem_map.mp he
    exact ⟨_, (acceptKind_at ..).mp hx⟩
  · rintro ⟨r, hr⟩
    let k := r.map WordRecord.kind
    have hm : k ∈ [none,some .init,some .read,some .write] := by
      cases r with
      | none => simp [k]
      | some r => cases hk : r.kind <;> simp [k,hk]
    refine ⟨_, List.mem_map.mpr ⟨k,hm,rfl⟩, (acceptKind_at ..).mpr ?_⟩
    have hwds : pinWords x a = fields hw r := by
      funext f
      apply bits_injective
      funext j
      exact (bits_pinWords x a f j).trans (hr f j)
    have hf : fill k (pinWords x a) = r := by
      rw [hwds]
      cases r with
      | none => rfl
      | some r => cases r; rfl
    rwa [hf]

theorem valid_size (hw : 2 ≤ w) (a : SlotAddr w σ) : (valid hw a).size ≤ 320*(w+1) := by
  have hb (k : Option Kind) : (acceptKind hw k a).size ≤ 7*(w*(2*1+2*1+6)+2)+1 := by
    apply allBits_size_le (s := w*(2*1+2*1+6)+1)
    intro f
    apply sameWord_size_le _ _ (s := 1) (t := 1) (fun j => le_rfl)
    intro j
    unfold candidate
    split <;> rfl
  have h := Expr.size_disjoin_le ([none,some .init,some .read,some .write].map fun k =>
      acceptKind hw k a) (7*(w*(2*1+2*1+6)+2)+1) (by
    intro e he
    obtain ⟨k,_,rfl⟩ := List.mem_map.mp he
    exact hb k)
  change (valid hw a).size ≤ 4*((7*(w*(2*1+2*1+6)+2)+1)+1)+1 at h
  omega

end ThreeFlat.Diagonal.TraceSortSite

end OAI
