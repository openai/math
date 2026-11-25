import OAI.Computability.NearSquareRoot.CRTControlledFlatSwaps
import OAI.Computability.NearSquareRoot.CRTControlledReserve

/-! # Orientation of disjoint address transpositions -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled

/-- Both endpoints of every move, interleaved in descriptor order. -/
def moveEndpoints {A : Type*} (xs : List (A × A)) : List A := xs.flatMap fun z => [z.1,z.2]

private theorem fix_outside {A : Type*} [DecidableEq A] (xs : List (A × A)) (x : A)
    (h : x ∉ moveEndpoints xs) : positionExchanges xs x = x := by
  induction xs with
  | nil => rfl
  | cons p l ih =>
    rcases p with ⟨a,b⟩
    change x ∉ a :: b :: moveEndpoints l at h
    simp only [List.mem_cons,not_or] at h
    change Equiv.swap a b (positionExchanges l x) = x
    rw [ih h.2.2,Equiv.swap_apply_of_ne_of_ne h.1 h.2.1]

/-- Disjoint exchanges give an involution wherever they occur in the descriptor list. -/
theorem positionExchanges_involutive {A : Type*} [DecidableEq A] (xs : List (A × A))
    (hn : (moveEndpoints xs).Nodup) : Function.Involutive (positionExchanges xs) := by
  induction xs with
  | nil => exact fun _ => rfl
  | cons p l ih =>
    rcases p with ⟨a,b⟩
    change (a :: b :: moveEndpoints l).Nodup at hn
    simp only [List.nodup_cons,List.mem_cons,not_or] at hn
    let q := positionExchanges l
    have qa : q a = a := fix_outside l a hn.1.2
    have qb : q b = b := fix_outside l b hn.2.1
    have comm (z : A) : q (Equiv.swap a b z) = Equiv.swap a b (q z) := by
      by_cases ha : z = a
      · subst z; simp [qa,qb]
      by_cases hb : z = b
      · subst z; simp [qa,qb]
      have nqa : q z ≠ a := fun h => ha (q.injective (h.trans qa.symm))
      have nqb : q z ≠ b := fun h => hb (q.injective (h.trans qb.symm))
      rw [Equiv.swap_apply_of_ne_of_ne ha hb,Equiv.swap_apply_of_ne_of_ne nqa nqb]
    intro x
    change Equiv.swap a b (q (Equiv.swap a b (q x))) = x
    rw [comm,Equiv.swap_apply_self]
    exact ih hn.2.2 x

theorem positionExchanges_symm_of_nodup {A : Type*} [DecidableEq A] (xs : List (A × A))
    (hn : (moveEndpoints xs).Nodup) : (positionExchanges xs).symm = positionExchanges xs := by
  ext x
  apply (positionExchanges xs).injective
  rw [Equiv.apply_symm_apply,positionExchanges_involutive xs hn x]

open IntegerMultiplication.Adic

theorem swapsFlat_disjoint_prefixBit {k : ℕ} (xs : List (Fin k × Fin k))
    (hn : (moveEndpoints xs).Nodup) (y : Block 2 k) (j : Fin k) :
    prefixBit (swapsFlat xs y) j = prefixBit y (positionExchanges xs j) := by
  rw [swapsFlat_prefixBit,positionExchanges_symm_of_nodup xs hn]

private theorem mem_zip_endpoints {A : Type*} (ls rs : List A) (x : A)
    (h : x ∈ moveEndpoints (ls.zip rs)) : x ∈ ls ∨ x ∈ rs := by
  induction ls generalizing rs with
  | nil => simp [moveEndpoints] at h
  | cons a as ih =>
    cases rs with
    | nil => simp [moveEndpoints] at h
    | cons b bs =>
      change x ∈ a :: b :: moveEndpoints (as.zip bs) at h
      rcases List.mem_cons.mp h with rfl | h
      · exact Or.inl List.mem_cons_self
      rcases List.mem_cons.mp h with rfl | h
      · exact Or.inr List.mem_cons_self
      exact (ih bs h).imp (List.mem_cons_of_mem _) (List.mem_cons_of_mem _)

/-- Pairing two disjoint lists without repetitions uses each endpoint at most once,
including when `zip` truncates a longer list. -/
theorem moveEndpoints_zip_nodup {A : Type*} (ls rs : List A) (hl : ls.Nodup) (hr : rs.Nodup)
    (hsep : ∀ a ∈ ls, a ∉ rs) : (moveEndpoints (ls.zip rs)).Nodup := by
  induction ls generalizing rs with
  | nil => simp [moveEndpoints]
  | cons a as ih =>
    cases rs with
    | nil => simp [moveEndpoints]
    | cons b bs =>
      obtain ⟨ha,hl⟩ := List.nodup_cons.mp hl
      obtain ⟨hb,hr⟩ := List.nodup_cons.mp hr
      have ab := hsep a List.mem_cons_self
      have sep (x : A) (h : x ∈ as) : x ∉ b::bs := hsep x (List.mem_cons_of_mem a h)
      change (a :: b :: moveEndpoints (as.zip bs)).Nodup
      simp only [List.nodup_cons,List.mem_cons,not_or] at ab ⊢
      refine ⟨⟨ab.1, fun hm => (mem_zip_endpoints _ _ _ hm).elim ha ab.2⟩, ?_, ?_⟩
      · intro hm
        exact (mem_zip_endpoints _ _ _ hm).elim (fun h => sep b h List.mem_cons_self) hb
      · exact ih bs hl hr (fun x h m => sep x h (List.mem_cons_of_mem _ m))

theorem reserveMoves_endpoints_nodup {k : ℕ} (p : Equiv.Perm (Fin k)) (lo hi : ℕ) :
    (moveEndpoints (reserveMoves p lo hi)).Nodup :=
  moveEndpoints_zip_nodup _ _ ((List.nodup_finRange k).filter _) ((List.nodup_finRange k).filter _)
    (fun x hx hy => (mem_misplaced p lo hi x |>.mp hx).2 (mem_available p lo hi x |>.mp hy).2)

theorem reserveMoves_flat_prefixBit {k : ℕ} (p : Equiv.Perm (Fin k)) (lo hi : ℕ)
    (y : Block 2 k) (j : Fin k) :
    prefixBit (swapsFlat (reserveMoves p lo hi) y) j =
      prefixBit y (positionExchanges (reserveMoves p lo hi) j) :=
  swapsFlat_disjoint_prefixBit _ (reserveMoves_endpoints_nodup p lo hi) y j

end Controlled

end NearSquareRoot
end Computability
end OAI
