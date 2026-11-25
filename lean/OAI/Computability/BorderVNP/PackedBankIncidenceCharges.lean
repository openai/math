import OAI.Computability.BorderVNP.PackedCellCapacity

/-! # Pointwise and regional charges for local wire gathering

A site can gather each selected incident cable once, including a self-loop,
and each attached external port once. These counts and widths fit in the
network's own local endpoint records. Singleton bounds can be summed for any
tested region of the same network.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.InheritedBank

open Crossing Shortening Finset
open scoped Classical
open private filter_sum from OAI.Computability.BorderVNP.PackedCellCapacity

variable {D : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)

/-- Rows to tie selected incident cables and the site's external ports.
A cable meeting the site at both ends contributes one row. -/
noncomputable def tieRows (keep : N.Edge → Prop) (v : N.Site) : ℕ :=
  Fintype.card {c : N.Edge // keep c ∧ (N.src c = v ∨ N.dst c = v)} +
  Fintype.card {t : P // N.attach t = v}

/-- Unique incident cables and ports with bounded weights fit in the physical
site's charge. The two endpoints of a self-loop are available in that charge. -/
theorem local_incidence_le (ex : Bool) (prior payload : N.Site → ℕ) (v : N.Site)
    (keep : N.Edge → Prop) (cw : N.Edge → ℕ) (pw : P → ℕ)
    (hc : ∀ c, cw c ≤ recordCost ex (N.width c)) (hp : ∀ t, pw t ≤ recordCost ex (bits t)) :
    (∑ c : {c : N.Edge // keep c ∧ (N.src c = v ∨ N.dst c = v)}, cw c.val) +
      (∑ t : {t : P // N.attach t = v}, pw t.val) ≤
      localRecords N ex prior payload (fun u => u = v) := by
  have heq := filter_sum (fun c : N.Edge => keep c ∧ (N.src c = v ∨ N.dst c = v)) cw
  have hpq := filter_sum (fun t : P => N.attach t = v) pw
  have same {I : Type} (a b : Fintype I) (f : I → ℕ) :
      (∑ i ∈ @univ I a, f i) = ∑ i ∈ @univ I b, f i :=
    congrArg (fun t : Fintype I => ∑ i ∈ @univ I t, f i) (Subsingleton.elim a b)
  refine le_trans ((Nat.add_le_add ((same _ _ (fun c : {c : N.Edge // keep c ∧
      (N.src c = v ∨ N.dst c = v)} => cw c.val)).trans heq).le
      hpq.le)) ?_
  unfold localRecords testedWidth
  have he := sum_le_sum (s := (univ : Finset N.Edge)) (f := fun c =>
      if keep c ∧ (N.src c = v ∨ N.dst c = v) then cw c else 0)
    (g := fun c => (if N.src c = v then recordCost ex (N.width c) else 0) +
      (if N.dst c = v then recordCost ex (N.width c) else 0)) (fun c _ => by
      by_cases h : keep c <;> by_cases hs : N.src c = v <;> by_cases hd : N.dst c = v <;>
        simp [h,hs,hd] <;> have := hc c <;> omega)
  have hports := sum_le_sum (s := (univ : Finset P)) (f := fun t => if N.attach t = v then pw t else 0)
    (g := fun t => if N.attach t = v then recordCost ex (bits t) else 0) (fun t _ => by
      by_cases h : N.attach t = v <;> simp [h,hp t])
  rw [sum_add_distrib] at he
  have middle := Nat.add_le_add he hports
  refine le_trans ?_ ((Nat.add_le_add_right (Nat.add_le_add_right (Nat.le_add_left _ _) _) _))
  convert! middle using 1
  congr! 3

/-- The sparse tie list fits in the public or expanded count of the owning site. -/
theorem tieRows_le (ex : Bool) (prior payload : N.Site → ℕ) (keep : N.Edge → Prop) (v : N.Site) :
    tieRows N keep v ≤ localRecords N ex prior payload (fun u => u = v) := by
  have h := local_incidence_le N ex prior payload v keep (fun _ => 1) (fun _ => 1)
    (fun c => Nat.le_add_right 1 _) (fun t => Nat.le_add_right 1 _)
  simpa [tieRows] using h

/-- Every singleton of an actual network includes its own mandatory box record. -/
theorem one_le_siteRecords (ex : Bool) (prior payload : N.Site → ℕ) (v : N.Site) :
    1 ≤ localRecords N ex prior payload (fun u => u = v) := by
  simp [localRecords,testedWidth,boxCost,recordCost]
  omega

/-- Changing only the history and payload at the sites adds exactly the
corresponding local box charge. The incident records coincide pointwise. -/
theorem exchange_site_records (ex : Bool) (prior payload newPrior newPayload : N.Site → ℕ) (v : N.Site) :
    localRecords N ex newPrior newPayload (fun u => u = v) + boxCost ex (prior v) (payload v) =
      localRecords N ex prior payload (fun u => u = v) + boxCost ex (newPrior v) (newPayload v) := by
  simp [localRecords,testedWidth]
  omega

/-- Regional local records inherit any common multiplicative singleton bound. -/
theorem localRecords_of_singletons (ex : Bool) (prior payload newPrior newPayload : N.Site → ℕ)
    (C : ℕ) (h : ∀ v, localRecords N ex newPrior newPayload (fun u => u = v) ≤
      C * localRecords N ex prior payload (fun u => u = v)) (test : N.Site → Prop) :
    localRecords N ex newPrior newPayload test ≤ C * localRecords N ex prior payload test := by
  let near := univ.filter test
  have he : test = fun u => id u ∈ near := by funext u; apply propext; simp [near]
  rw [he,localRecords_near N ex newPrior newPayload id near,localRecords_near N ex prior payload id near,
    mul_sum]
  exact sum_le_sum (fun v _ => h v)

end Packing.InheritedBank

end BorderVNP
end Computability
end OAI
