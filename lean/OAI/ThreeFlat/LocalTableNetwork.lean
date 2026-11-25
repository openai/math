import OAI.ThreeFlat.BitNetwork
import OAI.ThreeFlat.PrefixFlags
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.EquivFin

namespace OAI
/-! # Realizing an arbitrary local coefficient table with three-bit factors

For each row, a chain of flags tests agreement with successive prefixes of the
input. Exactly one assignment of all the flags satisfies these tests. Its final
flags select the coefficient of the matching row.
-/

namespace ThreeFlat.TableCompiler

noncomputable section

variable {F : Type*} {p : ℕ}

private abbrev Pattern (p : ℕ) := Fin p → Bool
private abbrev Flag (p : ℕ) := Pattern p × Fin (p + 1)
private abbrev Step (p : ℕ) := Option (Option (Fin p))
private abbrev Gate (p : ℕ) := Pattern p × Step p

private def flagId (x : Pattern p) (i : Fin (p + 1)) : Fin (Fintype.card (Flag p)) :=
  Fintype.equivFin (Flag p) (x, i)

private def gateId (x : Pattern p) (step : Step p) : Fin (Fintype.card (Gate p)) :=
  Fintype.equivFin (Gate p) (x, step)

private def sources (x : Pattern p) : Step p → Fin 3 → BitSource (Fintype.card (Flag p)) p
  | none => fun _ => .hidden (flagId x (Fin.last p))
  | some none => fun _ => .hidden (flagId x 0)
  | some (some i) => ![.hidden (flagId x i.castSucc), .pin i, .hidden (flagId x i.succ)]

private def table [Zero F] [One F] (w : Pattern p → F) (x : Pattern p) :
    Step p → (Fin 3 → Bool) → F
  | none, b => if b 0 then w x else 1
  | some none, b => if b 0 then 1 else 0
  | some (some i), b => if b 2 = (b 0 && (b 1 == x i)) then 1 else 0

/-- One trivalent cell for each prefix transition, initialization, and coefficient. -/
def localTableNetwork [Zero F] [One F] (w : (Fin p → Bool) → F) : BitNetwork F p where
  internal := Fintype.card (Flag p)
  cells := Fintype.card (Gate p)
  source k := let g := (Fintype.equivFin (Gate p)).symm k; sources g.1 g.2
  table k := let g := (Fintype.equivFin (Gate p)).symm k; table w g.1 g.2

theorem localTableNetwork_cells [Zero F] [One F] (w : (Fin p → Bool) → F) :
    (localTableNetwork w).cells = 2 ^ p * (p + 2) := by
  simp [localTableNetwork, Gate, Step, Pattern]

theorem localTableNetwork_internal [Zero F] [One F] (w : (Fin p → Bool) → F) :
    (localTableNetwork w).internal = 2 ^ p * (p + 1) := by
  simp [localTableNetwork, Flag, Pattern]

private def flags (pin : Pattern p) (k : Fin (Fintype.card (Flag p))) : Bool :=
  let f := (Fintype.equivFin (Flag p)).symm k
  prefixMatch f.1 pin f.2

@[simp] private theorem flags_flagId (pin x : Pattern p) (i : Fin (p + 1)) :
    flags pin (flagId x i) = prefixMatch x pin i := by simp [flags, flagId]

variable [CommSemiring F] (w : (Fin p → Bool) → F)

private theorem factor_gate (pin : Pattern p) (h : Fin (Fintype.card (Flag p)) → Bool)
    (x : Pattern p) (s : Step p) :
    (localTableNetwork w).factor pin h (gateId x s) =
      match s with
      | none => if h (flagId x (Fin.last p)) then w x else 1
      | some none => if h (flagId x 0) then 1 else 0
      | some (some i) =>
        if h (flagId x i.succ) = (h (flagId x i.castSucc) && (pin i == x i)) then 1 else 0 := by
  cases s with
  | none => simp [BitNetwork.factor, gateId, localTableNetwork, table, sources, BitSource.read]
  | some s => cases s <;> simp [BitNetwork.factor, gateId, localTableNetwork, table, sources,
      BitSource.read]

private theorem weight_flags (pin : Pattern p) :
    (localTableNetwork w).weight pin (flags pin) = w pin := by
  classical
  let f : Fin (Fintype.card (Gate p)) → F := (localTableNetwork w).factor pin (flags pin)
  calc
    _ = ∏ g : Gate p, f (Fintype.equivFin (Gate p) g) :=
      ((Fintype.equivFin (Gate p)).prod_comp f).symm
    _ = ∏ x : Pattern p, ∏ s : Step p, (localTableNetwork w).factor pin (flags pin) (gateId x s) :=
      Fintype.prod_prod_type _
    _ = w pin := by
      simp only [Fintype.prod_option, factor_gate, flags_flagId, prefixMatch_zero,
        prefixMatch_succ, prefixMatch_last]
      simp

private theorem weight_other (pin : Pattern p) (h : Fin (Fintype.card (Flag p)) → Bool)
    (hne : h ≠ flags pin) : (localTableNetwork w).weight pin h = 0 := by
  classical
  by_contra hweight
  have nz (x : Pattern p) (s : Step p) : (localTableNetwork w).factor pin h (gateId x s) ≠ 0 :=
    fun hf => hweight (Finset.prod_eq_zero (Finset.mem_univ _) hf)
  apply hne
  funext k
  obtain ⟨⟨x,i⟩, rfl⟩ := (Fintype.equivFin (Flag p)).surjective k
  change h (flagId x i) = flags pin (flagId x i)
  rw [flags_flagId]
  have hb : h (flagId x 0) = true := by
    by_contra hn
    simpa [factor_gate, hn] using nz x (some none)
  have hs (j : Fin p) : h (flagId x j.succ) =
      (h (flagId x j.castSucc) && (pin j == x j)) := by
    by_contra hn
    simpa [factor_gate, hn] using nz x (some (some j))
  exact congrFun (eq_prefixMatch x pin (fun j => h (flagId x j)) hb hs) i

/-- Contracting the network evaluates the specified table in every commutative semiring. -/
theorem localTableNetwork_eval (pin : Fin p → Bool) :
    (localTableNetwork w).eval pin = w pin := by
  classical
  calc
    _ = (localTableNetwork w).weight pin (flags pin) :=
      Finset.sum_eq_single_of_mem (flags pin) (Finset.mem_univ _) fun h _ hne =>
        weight_other w pin h hne
    _ = w pin := weight_flags w pin

end
end ThreeFlat.TableCompiler

end OAI
