import OAI.Computability.VPVNP.PairSimulationMapConsistency
import Mathlib.Data.List.FinRange

/-!
# Port comparisons for the grouped motif map

A party visits the source incidences in a fixed edge order, then the target
incidences in that order. A loop contributes both of its ports. Within each
port the selector copies are consecutive. Agreement of the resulting two
word arrays is the selector test in the motif entry algorithm on page 21.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapPortAgreement

open MotifSelector

variable {J E : Type*} {u bits : ℕ}

/-- The two incidences of a self-loop are distinct ports. -/
abbrev Port (G : Supply J E) (j : J) := {e // j = G.src e} ⊕ {e // j = G.dst e}

/-- Read a half-wire tag through its source or target incidence. -/
def portTag {G : Supply J E} {j : J} (tags : Half G (fun _ => Fin u → Word bits) j) :
    Port G j → Fin u → Word bits
  | .inl e => tags.1 e.val e.property
  | .inr e => tags.2 e.val e.property

variable [DecidableEq J] [Fintype E]

theorem consistent_iff_ports (G : Supply J E) (j : J)
    (tags : Half G (fun _ => Fin u → Word bits) j) :
    MotifEntry.consistent G j tags = true ↔
      ∀ (p : Port G j) (i : Fin u), portTag tags p i = MotifEntry.anchor G j tags i := by
  simp only [MotifEntry.consistent, decide_eq_true_iff]
  constructor
  · intro h p
    cases p with
    | inl e => simpa [e.property, portTag] using (h e.val).1
    | inr e => simpa [e.property, portTag] using (h e.val).2
  · intro h e
    constructor
    · split
      · rename_i he
        exact h (.inl ⟨e, he⟩)
      · trivial
    · split
      · rename_i he
        exact h (.inr ⟨e, he⟩)
      · trivial

private def keep (P : E → Prop) [DecidablePred P] (e : E) : Option {e // P e} :=
  if h : P e then some ⟨e, h⟩ else none

omit [Fintype E] in
private theorem mem_keep {P : E → Prop} [DecidablePred P] {e : E} {t : {e // P e}} :
    t ∈ keep P e ↔ t.val = e := by
  unfold keep
  split
  · simp [Subtype.ext_iff, eq_comm]
  · rename_i he
    have ht : t.val ≠ e := fun h => he (h ▸ t.property)
    simp [ht]

private def incidences (P : E → Prop) [DecidablePred P]
    (order : Fin (Fintype.card E) ≃ E) : List {e // P e} :=
  (List.ofFn order).filterMap (keep P)

private theorem mem_incidences {P : E → Prop} [DecidablePred P]
    (order : Fin (Fintype.card E) ≃ E) (t : {e // P e}) : t ∈ incidences P order := by
  apply List.mem_filterMap.mpr
  exact ⟨t.val, List.mem_ofFn.mpr ⟨order.symm t.val, order.apply_symm_apply _⟩,
    by simp [keep, t.property]⟩

private theorem incidences_nodup (P : E → Prop) [DecidablePred P]
    (order : Fin (Fintype.card E) ≃ E) : (incidences P order).Nodup :=
  List.Nodup.filterMap (fun _ _ _ h h' => (mem_keep.mp h).symm.trans (mem_keep.mp h'))
    (List.nodup_ofFn_ofInjective order.injective)

private theorem length_incidences_le (P : E → Prop) [DecidablePred P]
    (order : Fin (Fintype.card E) ≃ E) : (incidences P order).length ≤ Fintype.card E := by
  simpa [incidences] using List.length_filterMap_le (keep P) (List.ofFn order)

/-- The comparison schedule uses only the party, supply graph and fixed edge numbering. -/
def ports (G : Supply J E) (j : J) (order : Fin (Fintype.card E) ≃ E) : List (Port G j) :=
  (incidences (fun e => j = G.src e) order).map Sum.inl ++
  (incidences (fun e => j = G.dst e) order).map Sum.inr

theorem mem_ports (G : Supply J E) (j : J) (order : Fin (Fintype.card E) ≃ E) (p : Port G j) :
    p ∈ ports G j order := by
  cases p with
  | inl e => exact List.mem_append_left _ (List.mem_map_of_mem (mem_incidences order e))
  | inr e => exact List.mem_append_right _ (List.mem_map_of_mem (mem_incidences order e))

theorem ports_nodup (G : Supply J E) (j : J) (order : Fin (Fintype.card E) ≃ E) :
    (ports G j order).Nodup := by
  apply List.Nodup.append
  · exact (incidences_nodup _ order).map Sum.inl_injective
  · exact (incidences_nodup _ order).map Sum.inr_injective
  · intro p hl hr
    obtain ⟨s, _, rfl⟩ := List.mem_map.mp hl
    obtain ⟨t, _, ht⟩ := List.mem_map.mp hr
    cases ht

theorem ports_length_le (G : Supply J E) (j : J) (order : Fin (Fintype.card E) ≃ E) :
    (ports G j order).length ≤ 2 * Fintype.card E := by
  simpa [ports, two_mul] using Nat.add_le_add (length_incidences_le (fun e => j = G.src e) order)
    (length_incidences_le (fun e => j = G.dst e) order)

/-- The incident-port array in port-major order. -/
def leftTags (G : Supply J E) (j : J) (order : Fin (Fintype.card E) ≃ E)
    (tags : Half G (fun _ => Fin u → Word bits) j) (k : Fin ((ports G j order).length * u)) :
    Word bits :=
  let pi := finProdFinEquiv.symm k
  portTag tags ((ports G j order).get pi.1) pi.2

/-- Each block repeats the anchor's selector sequence. -/
def rightTags (G : Supply J E) (j : J) (order : Fin (Fintype.card E) ≃ E)
    (tags : Half G (fun _ => Fin u → Word bits) j) (k : Fin ((ports G j order).length * u)) :
    Word bits :=
  MotifEntry.anchor G j tags (finProdFinEquiv.symm k).2

/-- Pointwise equality of the two resident arrays computes precisely the
motif selector agreement test, including an empty selector sequence. -/
theorem consistent_iff_scan (G : Supply J E) (j : J) (order : Fin (Fintype.card E) ≃ E)
    (tags : Half G (fun _ => Fin u → Word bits) j) :
    MotifEntry.consistent G j tags = true ↔
      ∀ k, leftTags G j order tags k = rightTags G j order tags k := by
  rw [consistent_iff_ports]
  constructor
  · exact fun h k => h _ _
  · intro h p i
    obtain ⟨a, rfl⟩ := List.mem_iff_get.mp (mem_ports G j order p)
    simpa only [leftTags, rightTags, Equiv.symm_apply_apply] using h (finProdFinEquiv (a, i))

open BurstRAM.PrivateRAM PrimedCounter.GuessWord
open scoped Fin.CommRing

/-- On the two resident tag arrays the fixed native dispatch branches exactly
as the grouped motif entry does. All inputs incur the same instruction count. -/
theorem consistent_native {w p r k : ℕ} {M : Machine w p r k} {pc : Fin 7 → Fin p}
    {reg : Fin 7 ↪ Fin r} {done : Fin p} (G : Supply J E) (j : J)
    (order : Fin (Fintype.card E) ≃ E) (tags : Half G (fun _ => Fin u → Word bits) j)
    (enc : Word bits ↪ BurstRAM.Word w) (hl : MapConsistency.Linked M pc reg done)
    (test yes no : Fin p) (hz : M.code done = .constant (reg 5) 0 test)
    (hj : M.code test = .jumpEq (reg 4) (reg 5) yes no)
    (left right : BurstRAM.Word w) (c : Config w p r) (hc : c.pc = pc 0)
    (hleft : c.reg (reg 0) = left) (hright : c.reg (reg 2) = right)
    (h1 : c.reg (reg 3) = 1) (hzero : c.reg (reg 4) = 0) :
    let n := (ports G j order).length * u
    c.reg (reg 1) = left + (n : BurstRAM.Word w) → n < 2 ^ w →
    (∀ i : Fin n, c.privateMem (left + (i.val : BurstRAM.Word w)) =
      enc (leftTags G j order tags i)) →
    (∀ i : Fin n, c.privateMem (right + (i.val : BurstRAM.Word w)) =
      enc (rightTags G j order tags i)) →
    ∃ out, Prefix M c (List.replicate (7 * n + 3) .tick) out ∧
      out.pc = (if MotifEntry.consistent G j tags then yes else no) ∧
      MapConsistency.Frame reg c out ∧ out.privateMem = c.privateMem ∧
      out.persistent = c.persistent := by
  intro n hend hfit hx hy
  obtain ⟨out, run, hpc, frame, hm, hp⟩ := MapConsistency.compareTags enc hl test yes no hz hj
    (leftTags G j order tags) (rightTags G j order tags) left right c hc hleft hend hright h1 hzero
    hfit hx hy
  exact ⟨out, run, by simpa only [consistent_iff_scan G j order tags] using hpc, frame, hm, hp⟩

end PairSimulation.MapPortAgreement

end VPVNP
end Computability
end OAI
