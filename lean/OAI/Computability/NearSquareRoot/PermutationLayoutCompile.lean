import OAI.Computability.NearSquareRoot.CRTControlledReserveConjugate

/-! # Extending disjoint position constraints to forward and inverse layout tables -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PermutationLayout
open IntegerMultiplication.Code Reflections
open ReserveProgram (sweep sweep_poly encodedMoves endpointPair sweep_value)

/-- Postcompose the current permutation with the transposition that imposes `z`. -/
def impose {k : ℕ} (p : Equiv.Perm (Fin k)) (z : Fin k × Fin k) : Equiv.Perm (Fin k) :=
  p.trans (Equiv.swap (p z.1) z.2)

theorem impose_symm {k : ℕ} (p : Equiv.Perm (Fin k)) (z : Fin k × Fin k) :
    (impose p z).symm = p.symm.trans (Equiv.swap (p.symm z.2) z.1) := by
  ext x
  by_cases hx : x = z.2
  · subst x
    simp [impose]
  by_cases hy : x = p z.1
  · subst x
    simp [impose]
  have h1 : p.symm x ≠ p.symm z.2 := p.symm.injective.ne hx
  have h2 : p.symm x ≠ z.1 := by intro h; exact hy (p.symm_apply_eq.mp h)
  simp [impose,Equiv.swap_apply_of_ne_of_ne hy hx,Equiv.swap_apply_of_ne_of_ne h1 h2]

private def exchange (v : Pair × Tally) := sweep ([v.1],v.2)

@[fun_prop] private theorem poly_exchange : Poly exchange := by
  unfold exchange
  fun_prop

/-- Swap two unary labels wherever they occur in the array. -/
private def relabel (z : Pair × Table) : Table := polyPush exchange z

@[fun_prop] private theorem poly_relabel : Poly relabel :=
  Poly.push ([],[]) [] poly_exchange

private def adjust (z : (Table × Table) × Pair) : Table × Table :=
  (relabel ((next (z.1.1,z.2.1),z.2.2),z.1.1), relabel ((next (z.1.2,z.2.2),z.2.1),z.1.2))

@[fun_prop] private theorem poly_adjust : Poly adjust := by unfold adjust; fun_prop

def compile (z : Tally × List (Tally × Tally)) : Table × Table :=
  let base := Iter.lineup z.1
  z.2.foldl (fun s p => adjust (s,p)) (base,base)

private def Fits (n : ℕ) (t : Table) : Prop := t.length ≤ n ∧ ∀ a ∈ t, a.length ≤ n

private theorem next_fits (n : ℕ) (t : Table) (h : Fits n t) (a : Tally) :
    (next (t,a)).length ≤ n := by
  change ((t.drop a.length).headD []).length ≤ n
  cases he : t.drop a.length with
  | nil => simp
  | cons v vs =>
    have mem : v ∈ t.drop a.length := he ▸ List.mem_cons_self
    exact h.2 v (List.mem_of_mem_drop mem)

private theorem relabel_fits {n : ℕ} {a b : Tally} (t : Table) (h : Fits n t)
    (ha : a.length ≤ n) (hb : b.length ≤ n) : Fits n (relabel ((a,b),t)) := by
  refine ⟨by simpa [relabel,polyPush] using h.1, ?_⟩
  intro v hv
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hv
  have bound := h.2 u hu
  change (bif decide (u.length = a.length) then b else
    bif decide (u.length = b.length) then a else u).length ≤ n
  cases decide (u.length = a.length) <;> cases decide (u.length = b.length) <;> assumption

private theorem fold_fits {n : ℕ} (l : List Pair) (s : Table × Table)
    (hs : Fits n s.1 ∧ Fits n s.2)
    (hl : ∀ p ∈ l, p.1.length ≤ n ∧ p.2.length ≤ n) :
    let z := l.foldl (fun st p => adjust (st,p)) s
    Fits n z.1 ∧ Fits n z.2 := by
  induction l generalizing s with
  | nil => exact hs
  | cons p rest ih =>
    have hp := hl p List.mem_cons_self
    exact ih (adjust (s,p)) ⟨relabel_fits s.1 hs.1 (next_fits n s.1 hs.1 p.1) hp.2,
      relabel_fits s.2 hs.2 (next_fits n s.2 hs.2 p.2) hp.1⟩ (fun x hx => hl x (List.mem_cons_of_mem _ hx))

private theorem volume {n : ℕ} (t : Table) (h : ∀ a ∈ t, a.length ≤ n) :
    size t ≤ (2*n+2)*t.length+1 := by
  induction t with
  | nil => simp
  | cons v vs ih =>
    have hv := h v List.mem_cons_self
    have ht := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    rw [size_cons,size_tally,List.length_cons,Nat.mul_succ]
    omega

private theorem fits_of_size {n : ℕ} (t : Table) (h : size t ≤ n) : Fits n t :=
  ⟨(duration t).le.trans h, fun a ha => (duration a).le.trans ((size_bel ha).le.trans h)⟩

/-- The partial-table preparation itself is a polynomial-time P192 register program. -/
@[fun_prop] theorem compile_poly : Poly compile := by
  have loop : Poly (fun z : List Pair × (Table × Table) => z.1.foldl (fun s p => adjust (s,p)) z.2) := by
    apply Poly.fold_left poly_adjust 8 2
    intro z l hl
    let n := size z
    have hz₁ : size z.2.1 ≤ n := by simp only [n,size_prod]; omega
    have hz₂ : size z.2.2 ≤ n := by simp only [n,size_prod]; omega
    have hz := fold_fits l z.2 ⟨fits_of_size _ hz₁,fits_of_size _ hz₂⟩ (fun p hp => by
      have h := size_bel (hl.subset hp)
      have hh : size p.1 + size p.2 + 1 < size z.1 := h
      have hn : size z.1 ≤ n := by simp only [n,size_prod]; omega
      exact ⟨(duration p.1).le.trans (by omega),(duration p.2).le.trans (by omega)⟩)
    let v := l.foldl (fun s p => adjust (s,p)) z.2
    change Fits n v.1 ∧ Fits n v.2 at hz
    have h1 := (volume v.1 hz.1.2).trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hz.1.1) 1)
    have h2 := (volume v.2 hz.2.2).trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hz.2.1) 1)
    change size v.1 + size v.2 + 1 ≤ 8*(n+1)^2
    nlinarith
  have line : Poly (fun z : Tally × List Pair => Iter.lineup z.1) := Easy.fst.poly.compose Iter.poly_line
  exact (Easy.snd.poly.pair (line.pair line)).compose loop

private theorem relabel_table {k : ℕ} (p : Equiv.Perm (Fin k)) (u v : Fin k) :
    relabel ((tally u.val,tally v.val),table p) = table (p.trans (Equiv.swap u v)) := by
  unfold relabel polyPush table
  rw [List.map_ofFn]
  congr 1
  funext j
  exact sweep_value [(u,v)] (p j)

private theorem adjust_tables {k : ℕ} (p : Equiv.Perm (Fin k)) (u : Fin k × Fin k) :
    adjust ((table p,table p.symm),endpointPair u) = (table (impose p u),table (impose p u).symm) := by
  simp only [adjust,endpointPair,next_table]
  apply Prod.ext
  · exact relabel_table p (p u.1) u.2
  · rw [impose_symm]; exact relabel_table ..

private theorem fold_tables {k : ℕ} (l : List (Fin k × Fin k)) (p : Equiv.Perm (Fin k)) :
    (l.map endpointPair).foldl (fun s z => adjust (s,z)) (table p,table p.symm) =
      (table (l.foldl impose p),table (l.foldl impose p).symm) := by
  induction l generalizing p with
  | nil => rfl
  | cons a l ih => simpa only [List.map_cons,List.foldl_cons,adjust_tables] using ih (impose p a)

private theorem preserves {k : ℕ} (l : List (Fin k × Fin k)) (p : Equiv.Perm (Fin k)) (x : Fin k)
    (dst : x ∉ l.map Prod.fst) (src : p x ∉ l.map Prod.snd) : l.foldl impose p x = p x := by
  induction l generalizing p with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons,List.mem_cons,not_or] at dst src
    have step : impose p a x = p x := Equiv.swap_apply_of_ne_of_ne (p.injective.ne dst.1) src.1
    rw [List.foldl_cons,ih (impose p a) dst.2 (step ▸ src.2),step]

private theorem hits {k : ℕ} (l : List (Fin k × Fin k)) (p : Equiv.Perm (Fin k))
    (hd : (l.map Prod.fst).Nodup) (hs : (l.map Prod.snd).Nodup) :
    ∀ z ∈ l, l.foldl impose p z.1 = z.2 := by
  induction l generalizing p with
  | nil => simp
  | cons d l ih =>
    simp only [List.map_cons,List.nodup_cons] at hd hs
    intro z hz
    rcases List.mem_cons.mp hz with eq | mem
    · subst z
      have fixed : impose p d d.1 = d.2 := Equiv.swap_apply_left _ _
      exact (preserves l (impose p d) d.1 hd.1 (fixed ▸ hs.1)).trans fixed
    · exact ih (impose p d) hd.2 hs.2 z mem

/-- Every requested destination reads the prescribed source. Both tables are complete
permutations in increasing destination-address order. -/
theorem compile_valid {k : ℕ} (pairs : List (Fin k × Fin k))
    (hd : (pairs.map Prod.fst).Nodup) (hs : (pairs.map Prod.snd).Nodup) :
    ∃ p : Equiv.Perm (Fin k), (∀ z ∈ pairs, p z.1 = z.2) ∧
      compile (tally k,pairs.map (fun z => (tally z.1.val,tally z.2.val))) =
        (table p,table p.symm) := by
  let idp := Equiv.refl (Fin k)
  refine ⟨pairs.foldl impose idp,hits pairs idp hd hs,?_⟩
  have init : Iter.lineup (tally k) = table idp := Iter.lined k
  unfold compile
  rw [init]
  have f : (fun z : Fin k × Fin k => (tally z.1.val,tally z.2.val)) = endpointPair := by
    funext z
    rfl
  rw [f]
  simpa only [idp,Equiv.refl_symm] using fold_tables pairs idp

end Controlled.PermutationLayout

end NearSquareRoot
end Computability
end OAI
