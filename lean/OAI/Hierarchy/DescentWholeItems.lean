import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

namespace OAI
/-! # Pairing whole thin packs to thick destinations

All bundles leaving one item go to one thick destination. The lost capacity,
relative to the smaller side of the matching, is bounded by one largest item
per destination bin.
-/

namespace Hierarchy.DescentPacking
open scoped BigOperators Classical
noncomputable section

variable {I V : Type*} [Fintype V] [DecidableEq V]

def assigned (amount : I → ℕ) (v : V) : List (I × Option V) → ℕ
  | [] => 0
  | (i,j)::xs => (if j=some v then amount i else 0) + assigned amount v xs

/-- The list keeps the old item identifier on every decision, including skipped
zero-load or unplaceable items. Remaining capacity is exact at every destination. -/
structure Packing (amount : I → ℕ) (input : List I) (cap : V → ℕ) where
  decisions : List (I × Option V)
  remaining : V → ℕ
  order : decisions.map Prod.fst=input
  account : ∀ v, assigned amount v decisions + remaining v = cap v
  missed : ∀ i, (i,none)∈decisions → ∀v, remaining v < amount i

/-- The destination directory order scanned by the native first-fit allocator. -/
def binOrder (V : Type*) [Fintype V] : List V :=
  (List.finRange (Fintype.card V)).map (Fintype.equivFin V).symm

omit [DecidableEq V] in
@[simp] theorem mem_binOrder (v : V) : v∈binOrder V := by
  exact List.mem_map.mpr ⟨Fintype.equivFin V v,List.mem_finRange _,Equiv.symm_apply_apply _ _⟩

def firstFit (need : ℕ) (cap : V→ℕ) : Option V :=
  (binOrder V).find? (fun v=>decide (need≤cap v))

omit [DecidableEq V] in
theorem firstFit_some {need : ℕ} {cap : V→ℕ} {v : V} (h : firstFit need cap=some v) :
    need≤cap v := of_decide_eq_true (List.find?_some (p:=fun u : V=>decide (need≤cap u)) h)

omit [DecidableEq V] in
theorem firstFit_none {need : ℕ} {cap : V→ℕ} (h : firstFit need cap=none) (v : V) :
    cap v<need :=
  Nat.lt_of_not_ge (fun ok=>(List.find?_eq_none.mp h v (mem_binOrder v)) (decide_eq_true ok))

set_option maxRecDepth 8192 in
/-- Traverse items in order. An item is assigned in its entirety to the first bin
in directory order where it fits and reduces only that bin's capacity. -/
def pack (amount : I → ℕ) : (input : List I) → (cap : V → ℕ) → Packing amount input cap :=
  List.rec (motive:=fun input => (cap : V → ℕ) → Packing amount input cap)
  (fun cap => ⟨[],cap,rfl,fun _ => by simp [assigned],fun _ h => False.elim (List.not_mem_nil h)⟩)
  (fun i rest recurse cap =>
    match fit : firstFit (amount i) cap with
    | some v =>
      let after := Function.update cap v (cap v-amount i)
      let tail := recurse after
      { decisions := (i,some v)::tail.decisions
        remaining := tail.remaining
        order := by simp [tail.order]
        account := by
          intro j
          have used := tail.account j
          by_cases h : v=j
          · subst j
            have fitv : amount i≤cap v := firstFit_some fit
            simp [after] at used
            simp [assigned]
            omega
          · simp [assigned,h]
            simpa [after,Ne.symm h] using used
        missed := by simpa using tail.missed }
    | none =>
      let tail := recurse cap
      { decisions := (i,none)::tail.decisions
        remaining := tail.remaining
        order := by simp [tail.order]
        account := by simpa [assigned] using tail.account
        missed := by
          intro j h v
          rcases List.mem_cons.mp h with eq | old
          · have same := congrArg Prod.fst eq
            change j=i at same
            subst j
            have low : cap v < amount i := firstFit_none fit v
            have bounds := tail.account v
            omega
          · exact tail.missed j old v })

def consume (need : ℕ) (cap : V→ℕ) : Option V → V → ℕ
  | none => cap
  | some v => Function.update cap v (cap v-need)

theorem pack_decisions_cons (amount : I→ℕ) (i : I) (xs : List I) (cap : V→ℕ) :
    (pack amount (i::xs) cap).decisions =
      (i,firstFit (amount i) cap)::(pack amount xs (consume (amount i) cap (firstFit (amount i) cap))).decisions := by
  simp only [pack]
  split <;> rename_i chosen <;> simp_all only [consume] <;> rw [chosen]

theorem pack_remaining_cons (amount : I→ℕ) (i : I) (xs : List I) (cap : V→ℕ) :
    (pack amount (i::xs) cap).remaining =
      (pack amount xs (consume (amount i) cap (firstFit (amount i) cap))).remaining := by
  simp only [pack]
  split <;> rename_i chosen <;> simp_all only [consume] <;> rw [chosen]

private theorem matched_of_complete (amount : I → ℕ) (ds : List (I×Option V))
    (complete : ∀ i, (i,none)∉ds) :
    (∑v, assigned amount v ds) = (ds.map (fun p => amount p.1)).sum := by
  induction ds with
  | nil => simp [assigned]
  | cons p ds ih =>
    obtain ⟨i,_|v⟩ := p
    · exact False.elim (complete i List.mem_cons_self)
    · have complete' (j : I) : (j,none)∉ds := fun h => complete j (List.mem_cons_of_mem _ h)
      simp [assigned,Finset.sum_add_distrib,ih complete']

/-- A bin is too small for every rejected item in the *final* configuration.
Consequently each of the bins has less than one maximum item of capacity left
if any item was skipped. -/
theorem packing_loss (amount : I → ℕ) (input : List I) (cap : V → ℕ) (B : ℕ)
    (small : ∀ i∈input, amount i≤B) :
    let p := pack amount input cap
    min (input.map amount).sum (∑ v, cap v) ≤
      (∑ v, assigned amount v p.decisions) + Fintype.card V*B := by
  let p := pack amount input cap
  change _ ≤ (∑v,assigned amount v p.decisions)+_
  by_cases all : ∀i,(i,none)∉p.decisions
  · have h := matched_of_complete amount p.decisions all
    have total : (p.decisions.map (fun x => amount x.1)).sum = (input.map amount).sum := by
      simpa only [List.map_map,Function.comp_def] using congrArg (fun xs : List I => (xs.map amount).sum) p.order
    rw [h,total]
    omega
  · push Not at all
    obtain ⟨i,hi⟩ := all
    have original : i∈input := p.order ▸ List.mem_map_of_mem (f:=Prod.fst) hi
    have bound (v : V) : p.remaining v≤B := ((p.missed i hi v).trans_le (small i original)).le
    have residual : (∑ v, p.remaining v)≤Fintype.card V*B := by
      simpa using (Finset.sum_le_sum (s:=Finset.univ) fun v _ => bound v)
    have balance : (∑v, assigned amount v p.decisions)+(∑v,p.remaining v)=∑v,cap v := by
      rw [←Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun v _ => p.account v
    omega

end
end Hierarchy.DescentPacking

end OAI
