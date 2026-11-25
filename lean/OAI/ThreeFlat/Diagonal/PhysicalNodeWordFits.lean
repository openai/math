import OAI.ThreeFlat.Diagonal.PhysicalArchiveRows

namespace OAI
/-! # Both integer charge columns fit before every physical node publication -/

noncomputable section
namespace ThreeFlat.Diagonal.PhysicalStage
open HistoryContraction
open scoped Classical BigOperators
variable {F : Type} [Field F]

namespace Run

/-- The numeric invariant on each step of the chosen geometric history.
The pair count is pushed through exactly the same parent fiber as the work. -/
def ArchiveFits (W tariff : ℕ) : {d l : ℕ} → {A : State d l} → (r : Run F A) →
    (h : r.plan.History) → r.Charges → (A.Site→ℕ) → (A.Site→ℕ) → Prop
  | _,_,_,.done _,_,_,start,pay => ∀ a,tariff*start a<2^W ∧ pay a<2^W
  | _,_,_,.step R next,h,C,start,pay =>
    (∀ a,tariff*start a<2^W ∧ pay a<2^W) ∧
    ArchiveFits W tariff (next h.1) (tailHistory R next h) (C.2 h.1)
      (R.push h.1 (C.1 h.1) start) (fun v => ∑ i : {a // R.parent h.1 a=v}, pay i.val)

theorem fits_here {W tariff d l : ℕ} {A : State d l} (r : Run F A) {h : r.plan.History}
    {C : r.Charges} {start pay : A.Site→ℕ} (fit : r.ArchiveFits W tariff h C start pay) :
    ∀ a,tariff*start a<2^W ∧ pay a<2^W := by
  cases r with
  | done A => exact fit
  | step R next => exact fit.1

/-- Positivity lets each intermediate site charge its own work to its
eventual destination, even when many physical sites merge. -/
theorem start_le_destination {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History)
    (C : r.Charges) (start : A.Site→ℕ) (a : A.Site) :
    start a ≤ r.rootArray h C start (r.rawDestination h a) := by
  induction r with
  | done _ => exact le_rfl
  | step R next ih =>
    let t := h.1
    let owner := R.parent t a
    have one : start a ≤ ∑ x : {x // R.parent t x=owner}, start x.val :=
      Finset.single_le_sum (f:=fun x : {x // R.parent t x=owner} => start x.val)
        (fun _ _=>Nat.zero_le _) (Finset.mem_univ ⟨a,rfl⟩)
    have add : start a≤R.push t (C.1 t) start owner := by unfold Move.push;omega
    exact add.trans (ih t (tailHistory R next h) (C.2 t) (R.push t (C.1 t) start) owner)

private theorem here_of_peak {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History)
    (C : r.Charges) (start pay : A.Site→ℕ) (W tariff : ℕ) (covers : ∀ a,pay a≤ start a)
    (finalBound : ∀ z, max 1 tariff * r.rootArray h C start z < 2^W) (a : A.Site) :
    tariff*start a<2^W ∧ pay a<2^W := by
  let z := r.rawDestination h a
  have upper : start a≤r.rootArray h C start z := r.start_le_destination h C start a
  have one : 1 ≤ max 1 tariff := le_max_left _ _
  have peak := finalBound z
  exact ⟨(Nat.mul_le_mul (le_max_right _ _) upper).trans_lt peak,
    ((covers a).trans (upper.trans (Nat.le_mul_of_pos_left _ one))).trans_lt peak⟩

theorem archiveFits_of_peak {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History)
    (C : r.Charges) (start pay : A.Site→ℕ) (W tariff : ℕ) (covers : ∀ a,pay a≤ start a)
    (finalBound : ∀ z, max 1 tariff * r.rootArray h C start z < 2^W) :
    r.ArchiveFits W tariff h C start pay := by
  induction r with
  | done A => exact here_of_peak (.done A) h C start pay W tariff covers finalBound
  | step R next ih =>
    let t := h.1
    let newCost := R.push t (C.1 t) start
    let newPay := fun v => ∑ x : {a // R.parent t a=v}, pay x.val
    have paid (v) : newPay v≤newCost v := by
      change (∑ x : {a // R.parent t a=v}, pay x.val)≤C.1 t v+∑ x : {a // R.parent t a=v}, start x.val
      exact (Finset.sum_le_sum (fun i _=>covers i.val)).trans (Nat.le_add_left ..)
    exact ⟨here_of_peak (.step R next) h C start pay W tariff covers finalBound,
      ih t (tailHistory R next h) (C.2 t) newCost newPay paid finalBound⟩

end Run

open RAM.NavigationNodeRows

/-- At the seed the pure archive invariant bounds both native output operands
for every prior bank, since no child values are read. -/
theorem State.SeedRows.cost_fits {d l W : ℕ} {A : State d l} {O : A.ArchiveSites}
    {data : LayerData O.layer} {b : Banks} {start pay : A.Site→ℕ}
    (seed : State.SeedRows O data b start pay) (fit : ∀ v,b.unitWork*start v<2^W ∧ pay v<2^W)
    (prior : ℕ→Fin 2→ℕ) (j : Fin O.layer.count) (col : Fin 2) :
    data.cost b prior j col<2^W := by
  have val := seed prior (O.ord.symm j) col
  rw [Equiv.apply_symm_apply] at val
  rw [val]
  split
  · exact (fit _).1
  · exact (fit _).2

/-- Only the already-published predecessor columns are required. The range
proof for the new row does not read its stored result. -/
theorem Move.ArchiveStep.cost_fits {d l D L W : ℕ} {A : State d l} {R : Move F A D L}
    {t : Fin R.rules.count} {O : A.ArchiveSites} {charge : (R.next t).Site→ℕ}
    (S : R.ArchiveStep t O charge) (b : Banks) (prior : ℕ→Fin 2→ℕ) (start pay : A.Site→ℕ)
    (previous : ∀ a, prior (O.id a) 0=b.unitWork*start a ∧ prior (O.id a) 1=pay a)
    (fit : ∀ v, b.unitWork*R.push t charge start v<2^W ∧
      (∑ x : {a // R.parent t a=v}, pay x.val)<2^W)
    (j : Fin S.sites.layer.count) (col : Fin 2) : S.data.cost b prior j col<2^W := by
  have val := S.cost_values b prior start pay previous (S.sites.ord.symm j)
  rw [Equiv.apply_symm_apply] at val
  fin_cases col
  · change S.data.cost b prior j (0 : Fin 2) < 2^W
    exact val.1.trans_lt (fit _).1
  · change S.data.cost b prior j (1 : Fin 2) < 2^W
    exact val.2.trans_lt (fit _).2

end ThreeFlat.Diagonal.PhysicalStage
end

end OAI
