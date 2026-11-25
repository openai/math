import OAI.Computability.BorderVNP.PackedSewnFragmentSource
import OAI.Computability.BorderVNP.CrossingParallelFrame

/-! # Two-fragment boundary of the sparse coalescing circuit -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField.Fragment

open VPVNP.VerifierNetwork

/-- Decode a candidate slot when it is enabled. -/
def read {w : ℕ} (x : Column w → Bool) : Option Parsed := if x (.inl false) then some (parseRow x) else none

/-- The two exclusive ends of a true descriptor fit the public address width. -/
def Parsed.Fits (w : ℕ) (a : Parsed) : Prop :=
  a.run.oldStart+a.run.width < 2^w ∧ ∀ j, a.run.source = some j → j+a.run.width < 2^w

/-- The endpoints of a joined descriptor are those of its last fragment. -/
theorem Parsed.join_fits {a b : Parsed} (same : a.compatible b) {w : ℕ} (hb : b.Fits w) : (a.join b).Fits w := by
  obtain ⟨_,old,source⟩ := same
  constructor
  · change a.run.oldStart + (a.run.width+b.run.width) < _
    rw [←Nat.add_assoc,old]
    exact hb.1
  · intro j h
    change a.run.source = some j at h
    rw [h,Option.map_some] at source
    exact (Nat.add_assoc j a.run.width b.run.width).symm ▸ hb.2 _ source.symm

/-- The pair update moves a coalesced right-hand run to its true leftmost slot. -/
def absorb (a b : Option Parsed) : Option Parsed × Option Parsed :=
  match a,b with
  | some p,some q => if p.compatible q then (some (p.join q),none) else (a,b)
  | _,_ => (a,b)

/-- Correct observable rows of one pair frame, on every physical in-bounds input. -/
def PairSpec {w : ℕ} (p : Frame (Bool × Column w) (Bool × Column w)) : Prop :=
  ∀ x, (∀ b : Bool, ∀ a ∈ read (fun j => x (b,j)), a.Fits w) →
    let l := read (fun j => x (false,j))
    let r := read (fun j => x (true,j))
    (read (fun j => p.eval x (false,j)),read (fun j => p.eval x (true,j))) = absorb l r

/-- Every maximal run produced by the sparse fold fits when its original fragments fit. -/
theorem coalesce_fits {xs : List Parsed} {w : ℕ} (h : ∀ r ∈ xs, r.Fits w) : ∀ r ∈ coalesce xs, r.Fits w := by
  induction xs with
  | nil => simp [coalesce]
  | cons a xs ih =>
    have ha := h a (List.mem_cons_self ..)
    have ht := ih (fun r hr => h r (List.mem_cons_of_mem _ hr))
    change ∀ r ∈ prepend a (coalesce xs), r.Fits w
    generalize eqn : coalesce xs = bs at ht ⊢
    cases bs with
    | nil => simpa only [prepend,List.mem_singleton,forall_eq] using ha
    | cons b bs =>
      by_cases e : a.compatible b
      · simp only [prepend,ite_eq_left e,List.mem_cons,forall_eq_or_imp]
        exact ⟨Parsed.join_fits e (ht b (List.mem_cons_self ..)),fun r hr => ht r (List.mem_cons_of_mem _ hr)⟩
      · simpa only [prepend,ite_eq_right e,List.mem_cons,forall_eq_or_imp] using And.intro ha ht

end Packing.SewnField.Fragment

end BorderVNP
end Computability
end OAI
