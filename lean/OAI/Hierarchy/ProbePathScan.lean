import OAI.Hierarchy.ProbeChains
import Mathlib.Data.List.Chain

namespace OAI
/-! # Bounded sampler-path enumeration and the deterministic maximal scan -/

namespace Hierarchy.AdaptiveProbe
noncomputable section
open scoped Classical

variable {V : Type*} [DecidableEq V]

/-- Each level scans the next entry of the fixed output-port adjacency list. -/
def paths (next : V → List V) (start : V) : ℕ → List (List V)
  | 0 => [[start]]
  | n+1 => (next start).flatMap fun x => (paths next x n).map (start :: ·)

omit [DecidableEq V] in
theorem paths_spec (next : V → List V) (x : V) (n : ℕ) (l : List V) :
    l ∈ paths next x n ↔ ∃ tail, l=x::tail ∧ tail.length=n ∧ l.IsChain (fun a b => b∈next a) := by
  induction n generalizing x l with
  | zero =>
    simp [paths]
    rintro rfl; simp
  | succ n ih =>
    constructor
    · intro h
      obtain ⟨y,ey,hm⟩ := List.mem_flatMap.mp h
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hm
      obtain ⟨p,rfl,lp,cp⟩ := (ih y q).mp hq
      exact ⟨_,rfl,by simp [lp],List.isChain_cons_cons.mpr ⟨ey,cp⟩⟩
    · rintro ⟨t,rfl,len,chain⟩
      cases t with
      | nil => simp at len
      | cons y rest =>
        obtain ⟨xy,ys⟩ := List.isChain_cons_cons.mp chain
        refine List.mem_flatMap.mpr ⟨y,xy,List.mem_map.mpr ⟨y::rest,?_,rfl⟩⟩
        exact (ih _ _).mpr ⟨_,rfl,by simpa using len,ys⟩

omit [DecidableEq V] in
theorem paths_count (next : V → List V) (D : ℕ) (bound : ∀ x,(next x).length ≤ D)
    (x : V) (steps : ℕ) : (paths next x steps).length ≤ D^steps := by
  induction steps generalizing x with
  | zero => simp [paths]
  | succ n ih =>
    let f y := (paths next y n).map (x :: ·)
    have count (ys : List V) : (ys.flatMap f).length ≤ ys.length*D^n := by
      induction ys with
      | nil => simp
      | cons y ys h =>
        simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.succ_mul]
        simpa [f,Nat.add_comm] using Nat.add_le_add (ih y) h
    exact (count _).trans (by rw [pow_succ,Nat.mul_comm]; exact Nat.mul_le_mul_left _ (bound x))

/-- The accepted paths are returned in the fixed scan order. A path is purchased only
if all its tiles remain unused. -/
def scanPaths : List (List V) → Finset V → List (List V) × Finset V
  | [], left => ([],left)
  | p::ps,left =>
    if p.toFinset ⊆ left then
      let rest := scanPaths ps (left\p.toFinset)
      (p::rest.1,rest.2)
    else scanPaths ps left

theorem scan_subset (ps : List (List V)) (left : Finset V) : (scanPaths ps left).2⊆left := by
  induction ps generalizing left with
  | nil => exact Finset.Subset.rfl
  | cons p ps ih =>
    by_cases usable : p.toFinset⊆left
    · exact (by simpa only [scanPaths,ite_eq_left usable] using
        (ih (left\p.toFinset)).trans Finset.sdiff_subset)
    · simpa only [scanPaths,ite_eq_right usable] using ih left

theorem scan_maximal (ps : List (List V)) (left : Finset V) (allowed : ∀ p∈ps,p≠[]) :
    ∀ p∈ps, ¬p.toFinset⊆(scanPaths ps left).2 := by
  induction ps generalizing left with
  | nil => simp
  | cons q ps ih =>
    intro p member full
    by_cases usable : q.toFinset⊆left
    · simp only [scanPaths,ite_eq_left usable] at full
      rcases List.mem_cons.mp member with rfl|later
      · obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil p (allowed p (by simp))
        have h := (scan_subset ps (left\p.toFinset)) (full (List.mem_toFinset.mpr hx))
        exact (Finset.mem_sdiff.mp h).2 (List.mem_toFinset.mpr hx)
      · exact ih (left\q.toFinset) (fun l hl => allowed l (by simp [hl])) p later full
    · simp only [scanPaths,ite_eq_right usable] at full
      rcases List.mem_cons.mp member with rfl|later
      · exact usable (full.trans (scan_subset ps left))
      · exact ih left (fun l hl => allowed l (by simp [hl])) p later full

theorem scan_disjoint (ps : List (List V)) (left : Finset V) :
    (∀ p∈(scanPaths ps left).1, p.toFinset⊆left) ∧
    ((scanPaths ps left).1).Pairwise (fun p q => Disjoint p.toFinset q.toFinset) := by
  induction ps generalizing left with
  | nil => simp [scanPaths]
  | cons p ps ih =>
    by_cases yes : p.toFinset⊆left
    · simp only [scanPaths,ite_eq_left yes]
      obtain ⟨inside,pair⟩ := ih (left\p.toFinset)
      refine ⟨?_,List.pairwise_cons.mpr ⟨?_,pair⟩⟩
      · intro q hq
        rcases List.mem_cons.mp hq with rfl|h
        · exact yes
        · exact (inside q h).trans Finset.sdiff_subset
      · intro q hq
        exact Finset.disjoint_left.mpr fun x hp h => (Finset.mem_sdiff.mp (inside q hq h)).2 hp
    · simpa only [scanPaths,ite_eq_right yes] using ih left

/-- Exact accounting of the purchased H-tile chains and every remaining tile. -/
theorem scan_account (H : ℕ) (ps : List (List V)) (left : Finset V)
    (good : ∀ p ∈ ps, p.length=H ∧ p.Nodup) :
    (scanPaths ps left).1.length*H + (scanPaths ps left).2.card = left.card := by
  induction ps generalizing left with
  | nil => simp [scanPaths]
  | cons p ps ih =>
    have tail := fun l hl => good l (List.mem_cons_of_mem p hl)
    by_cases use : p.toFinset⊆left
    · have rest := ih (left\p.toFinset) tail
      have size := Finset.card_sdiff_add_card_eq_card use
      have current := good p (List.mem_cons_self ..)
      rw [List.toFinset_card_of_nodup current.2,current.1] at size
      simp only [scanPaths,ite_eq_left use,List.length_cons,Nat.succ_mul]
      omega
    · simpa only [scanPaths,ite_eq_right use] using ih left tail

end
end Hierarchy.AdaptiveProbe

end OAI
