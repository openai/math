import OAI.Hierarchy.ProbeFinalRoutes

namespace OAI
/-! # Enumerating the physical additions that discharge both terminal stocks -/

namespace Hierarchy.AdaptiveProbe
open scoped BigOperators
noncomputable section

variable {E I C : Type*} [Fintype I] [Fintype C] [DecidableEq E]

/-- Every use of a physical edge has a slot, including repeated uses by the same route. -/
abbrev RouteOccurrence (core : I → List E) (center : C → List E) :=
  (Σ i, Fin (core i).length) ⊕ (Σ c, Fin (center c).length)

def RouteOccurrence.edge {core : I → List E} {center : C → List E} :
    RouteOccurrence core center → E
  | .inl ⟨i,j⟩ => (core i)[j.val]
  | .inr ⟨c,j⟩ => (center c)[j.val]

def RouteOccurrence.weight {core : I → List E} {center : C → List E}
    (stock : I → ℕ) (reserved used : C → ℕ) : RouteOccurrence core center → ℕ
  | .inl ⟨i,_⟩ => stock i
  | .inr ⟨c,_⟩ => reserved c-used c

theorem sum_positions_eq_count (xs : List E) (e : E) (s : ℕ) :
    (∑ j : Fin xs.length, if xs[j.val]=e then s else 0) = xs.count e*s := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    change (∑ j : Fin (xs.length+1), if (x::xs)[j.val]'(by simpa using j.isLt)=e then s else 0) = _
    rw [Fin.sum_univ_succ]
    by_cases hx : x=e
    · simp [hx,ih,Nat.add_mul,Nat.add_comm]
    · simp [hx,ih]

/-- The sum on the left is the actual scatter bank's one contribution per source slot. -/
theorem route_occurrences_sum (core : I → List E) (center : C → List E)
    (stock : I → ℕ) (reserved used : C → ℕ) (e : E) :
    (∑ o : RouteOccurrence core center, if o.edge=e then o.weight stock reserved used else 0) =
      routeLoad core stock e + routeLoad center (fun c => reserved c-used c) e := by
  classical
  rw [Fintype.sum_sum_type,Fintype.sum_sigma,Fintype.sum_sigma]
  simp only [RouteOccurrence.edge,RouteOccurrence.weight,routeLoad]
  exact congrArg₂ (·+·)
    (Finset.sum_congr rfl (fun i _ => sum_positions_eq_count (core i) e (stock i)))
    (Finset.sum_congr rfl (fun c _ => sum_positions_eq_count (center c) e (reserved c-used c)))

omit [DecidableEq E] in
/-- The occurrence tape has exactly the total length of the two sets of walks. -/
theorem route_occurrences_card (core : I → List E) (center : C → List E) :
    Fintype.card (RouteOccurrence core center) =
      (∑ i,(core i).length)+(∑ c,(center c).length) := by
  simp [RouteOccurrence,Fintype.card_sigma]

omit [DecidableEq E] in
theorem route_occurrences_bound (core : I → List E) (center : C → List E) (l r : ℕ)
    (short : ∀ i,(core i).length≤l) (near : ∀ c,(center c).length≤r) :
    Fintype.card (RouteOccurrence core center) ≤ Fintype.card I*l+Fintype.card C*r := by
  rw [route_occurrences_card]
  exact Nat.add_le_add (by simpa using Finset.sum_le_sum (s:=Finset.univ) (fun i _ => short i))
    (by simpa using Finset.sum_le_sum (s:=Finset.univ) (fun c _ => near c))

/-- A single physical edge can carry all arrivals without word overflow even when
several commodities use it repeatedly. The participation bound counts occurrences. -/
theorem routeLoad_le (route : I → List E) (bits : I → ℕ) (e : E) (uses per : ℕ)
    (incidence : (∑ i,(route i).count e)≤uses) (stock : ∀ i,bits i≤per) :
    routeLoad route bits e≤uses*per := by
  calc
    routeLoad route bits e ≤ ∑ i,(route i).count e*per :=
      Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (stock i)
    _ = (∑ i,(route i).count e)*per := (Finset.sum_mul ..).symm
    _ ≤ uses*per := Nat.mul_le_mul_right _ incidence

theorem settled_width_le (core : I → List E) (center : C → List E) (installed : E → ℕ)
    (stock : I → ℕ) (reserved used : C → ℕ) (e : E) (w seed degree coreCap near cap : ℕ)
    (seeded : installed e≤seed*w) (tight : (∑ i,(core i).count e)≤degree)
    (stockCap : ∀ i,stock i≤coreCap*w) (returns : (∑ c,(center c).count e)≤near)
    (reservedCap : ∀ c,reserved c≤cap*w) :
    installed e+(routeLoad core stock e+routeLoad center (fun c => reserved c-used c) e) ≤
      (seed+degree*coreCap+near*cap)*w := by
  have c := routeLoad_le core stock e degree (coreCap*w) tight stockCap
  have z := routeLoad_le center (fun c => reserved c-used c) e near (cap*w) returns
    (fun j => (Nat.sub_le ..).trans (reservedCap j))
  calc
    _ ≤ seed*w+(degree*(coreCap*w)+near*(cap*w)) := Nat.add_le_add seeded (Nat.add_le_add c z)
    _ = _ := by ring

end
end Hierarchy.AdaptiveProbe

end OAI
