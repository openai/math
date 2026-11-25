import OAI.Computability.BorderVNP.CoverLorentzSubdivisionRecords

/-!
# Per-tile descriptor and expanded bounds for the actual subdivided pack

Grouping old cable ends by source address and move is enough to bound all new
equality boxes and their two ends. The incoming data of any old box, including
previously retained history, remains at its actual site.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover.SiteRoutes

open BorderVNP.Crossing BorderVNP.Shortening Finset
open scoped Classical

variable {D : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} {I : Type*} [Fintype I]
  {d : ℕ} {L h : ℝ} {R : Type*} {p : Pack D P bits R}

/-- Source address of each old cable in the product deck group. -/
def sourceAddress (r : SiteRoutes p I d L) (e : p.layout.Edge) : I → Deck (d+1) :=
  reduceMove d (r.origin (p.layout.src e))

/-- Noncharged wires use the empty code, which produces no intermediate equality site. -/
noncomputable def moveCode (r : SiteRoutes p I d L) (e : p.layout.Edge) : Option (allowedMoves I L) :=
  if he : r.active e then some (r.step e he) else none

/-- Endpoint carry of a catalog hop. A dummy code can be charged at its own source. -/
noncomputable def endCarry (d : ℕ) (t : Option (allowedMoves I L) × Fin (hopCount L h)) : I → Deck (d+1) :=
  t.1.elim 1 (fun s => reduceMove d (hopCarry (s,t.2) 1))

omit [Fintype P] in
/-- Each real equality box and its two ends are charged at a true endpoint of the preceding
hop. The terminal hop in the upper bound may contribute an additional record. -/
private theorem equality_load (r : SiteRoutes p I d L) (expanded : Bool) (b : I → Deck (d+1))
    (e : p.layout.Edge) :
    (∑ j : Fin ((r.routes h).interior e), if productAddress d (r.physical h (.inr ⟨e,j⟩)) = b then
      1+2*recordCost expanded (p.layout.width e) else 0) ≤
    3 * ∑ j : Fin (hopCount L h), if r.sourceAddress e * endCarry d (r.moveCode e,j) = b then
      recordCost expanded (p.layout.width e) else 0 := by
  by_cases he : r.active e
  · let n := (r.routes h).interior e
    have hn : n+1 = hopCount L h := by simp [n,routes,he,hopCount]
    let F (i : Fin (hopCount L h)) :=
      if r.sourceAddress e * endCarry d (r.moveCode e,i) = b then recordCost expanded (p.layout.width e) else 0
    have hf (j : Fin n) : productAddress d (r.physical h (.inr ⟨e,j⟩)) =
        r.sourceAddress e * endCarry d (r.moveCode e,(finCongr hn) j.castSucc) := by
      rw [r.physical_equality he,hopAddress]
      simp [moveCode,he,endCarry,sourceAddress]
      rfl
    calc
      _ ≤ ∑ j : Fin n, 3*F (finCongr hn j.castSucc) := by
        apply sum_le_sum
        intro j _
        rw [hf j]
        dsimp only [F]
        split_ifs
        · unfold recordCost; omega
        · simp
      _ ≤ ∑ i : Fin (n+1), 3*F (finCongr hn i) := by rw [Fin.sum_univ_castSucc]; omega
      _ = ∑ i : Fin (hopCount L h), 3*F i := Equiv.sum_comp (finCongr hn) (fun i => 3*F i)
      _ = _ := (mul_sum _ _ _).symm
  · have : IsEmpty (Fin ((r.routes h).interior e)) := Fin.isEmpty_iff.mpr (by simp [routes,he])
    rw [Finset.sum_of_isEmpty]
    exact Nat.zero_le _

/-- The actual `localRecords` for both modes of §6, retaining all old payloads and
histories, satisfies a bound independent of level and pack size. -/
theorem localRecords_subdivided_le (r : SiteRoutes p I d L) (expanded : Bool)
    (prior payload : p.layout.Site → ℕ) (M : ℕ)
    (old : ∀ a : I → Deck (d+1), localRecords p.layout expanded prior payload
      (fun v => reduceMove d (r.origin v) = a) ≤ M) (b : I → Deck (d+1)) :
    localRecords (p.layout.subdivide (r.routes h)) expanded (Sum.elim prior (fun _ => 0))
      (Sum.elim payload (fun _ => 0)) (fun v => productAddress d (r.physical h v) = b) ≤
      (1+3*Fintype.card (Option (allowedMoves I L) × Fin (hopCount L h)))*M := by
  classical
  let w (e : p.layout.Edge) := recordCost expanded (p.layout.width e)
  let rows := sourceRows r.sourceAddress r.moveCode (fun e => (w e : ℝ))
  have hpos := sourceRows_nonneg r.sourceAddress r.moveCode (fun e => Nat.cast_nonneg (w e))
  have hrow (a : I → Deck (d+1)) : sourceMass rows a ≤ (M:ℝ) := by
    rw [show rows = _ by rfl,sourceMass_rows]
    have he : testedWidth w (fun e => r.sourceAddress e = a) ≤ M := by
      apply le_trans _ (old a)
      unfold localRecords
      change testedWidth w (fun e => r.sourceAddress e = a) ≤
        _ + testedWidth w (fun e => r.sourceAddress e = a) + _ + _
      omega
    unfold testedWidth at he
    have he' : (∑ e, if r.sourceAddress e = a then w e else 0) ≤ M := by
      convert! he using 2 with e
      split_ifs <;> rfl
    exact_mod_cast he'
  have hz := slotMass_le_max rows (endCarry (h := h) d) hpos hrow b
  change slotMass (sourceRows r.sourceAddress r.moveCode (fun e => (w e:ℝ))) _ b ≤ _ at hz
  rw [slotMass_rows] at hz
  have hZ : (∑ e, ∑ j : Fin (hopCount L h), if r.sourceAddress e * endCarry d (r.moveCode e,j) = b then
      w e else 0) ≤ Fintype.card (Option (allowedMoves I L) × Fin (hopCount L h))*M := by
    exact_mod_cast hz
  rw [subdivision_records_eq]
  have horig : (fun v => productAddress d (r.physical h (.inl v)) = b) =
      fun v => reduceMove d (r.origin v) = b := by
    funext v
    change (productAddress d (r.site v) = b) = _
    rw [r.address_site]
  rw [horig]
  have hadd := sum_le_sum (s := (univ : Finset p.layout.Edge)) (fun e _ => r.equality_load (h := h) expanded b e)
  rw [← mul_sum] at hadd
  rw [add_mul,one_mul,mul_assoc]
  have final := Nat.add_le_add (old b) (hadd.trans (Nat.mul_le_mul_left 3 hZ))
  convert! final using 2
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> rfl

end Cover.SiteRoutes

end BorderVNP
end Computability
end OAI
