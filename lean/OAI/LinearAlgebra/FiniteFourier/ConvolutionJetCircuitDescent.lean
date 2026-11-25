import OAI.LinearAlgebra.FiniteFourier.CircuitComposition

/-! # Restricting a linear circuit to two scalar coordinates

A multiplication by a fixed quadratic scalar uses two binary gates. Thus an
original binary gate uses at most six base-ring gates. A scaled output may
need two more gates even though scaling on an output is free in the original
circuit.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace QuadraticDescent

variable {R S I J O : Type*} [CommRing R] [CommRing S]
variable (φ : R →+* S) (η : S)

/-- Interpret pairs of base coordinates as quadratic scalars. -/
def decode (x : I × Fin 2 → R) (i : I) : S := φ (x (i,0)) + η * φ (x (i,1))

/-- A pair of available base wires which decodes to the specified scalar signal. -/
private def Represented {n : ℕ} (p : Program R J n) (f : (J → R) → S) : Prop :=
  ∃ u v, Available p u ∧ Available p v ∧ ∀ x, φ (u x) + η * φ (v x) = f x

private abbrev Keeps {m n : ℕ} (p : Program R J m) (q : Program R J n) :=
  ∀ u, Available p u → Available q u

private theorem Represented.keep {m n : ℕ} {p : Program R J m} {q : Program R J n}
    {f : (J → R) → S} (h : Represented φ η p f) (hk : Keeps p q) : Represented φ η q f := by
  obtain ⟨u,v,hu,hv,he⟩ := h
  exact ⟨u,v,hk _ hu,hk _ hv,he⟩

private theorem scale {c d : R} (hη : η^2 = φ c + η*φ d)
    (coords : ∀ s, ∃ a b : R, φ a + η*φ b = s) {n : ℕ} (p : Program R J n)
    (s : S) {f : (J → R) → S} (hf : Represented φ η p f) :
    ∃ m ≤ n+2, ∃ q : Program R J m, Keeps p q ∧ Represented φ η q (fun x => s * f x) := by
  obtain ⟨a,b,rfl⟩ := coords s
  obtain ⟨u,v,hu,hv,he⟩ := hf
  obtain ⟨m,hm,q,hk,h₀⟩ := available_combine p a (c*b) hu hv
  obtain ⟨l,hl,r,hk',h₁⟩ := available_combine q b (a+d*b) (hk _ hu) (hk _ hv)
  refine ⟨l, by omega, r, fun _ h => hk' _ (hk _ h), _, _, hk' _ h₀, h₁, fun x => ?_⟩
  dsimp only
  rw [← he x]
  simp only [map_add, map_mul]
  linear_combination -(φ b * φ (v x)) * hη

private theorem add {n : ℕ} (p : Program R J n) {f g : (J → R) → S}
    (hf : Represented φ η p f) (hg : Represented φ η p g) :
    ∃ m ≤ n+2, ∃ q : Program R J m, Keeps p q ∧ Represented φ η q (fun x => f x + g x) := by
  obtain ⟨u,v,hu,hv,he⟩ := hf
  obtain ⟨w,z,hw,hz,he'⟩ := hg
  obtain ⟨m,hm,q,hk,h₀⟩ := available_combine p 1 1 hu hw
  obtain ⟨l,hl,r,hk',h₁⟩ := available_combine q 1 1 (hk _ hv) (hk _ hz)
  refine ⟨l, by omega, r, fun _ h => hk' _ (hk _ h), _, _, hk' _ h₀, h₁, fun x => ?_⟩
  dsimp only
  rw [← he x, ← he' x]
  simp only [one_mul, map_add]
  ring

private theorem simulate {c d : R} (hη : η^2 = φ c + η*φ d)
    (coords : ∀ s, ∃ a b : R, φ a + η*φ b = s) {t : ℕ} (p : Program S I t) :
    ∃ m ≤ 6*t, ∃ q : Program R (I × Fin 2) m, ∀ w : I ⊕ Fin t,
      Represented φ η q (fun x => Sum.elim (decode φ η x) (p.value (decode φ η x)) w) := by
  induction p with
  | nil =>
    refine ⟨0, by simp, .nil, ?_⟩
    rintro (i | j)
    · refine ⟨(fun x => x (i,0)), (fun x => x (i,1)), ?_, ?_, fun x => rfl⟩
      · exact ⟨.scaled 1 (.inl (i,0)), fun x => by simp [Readout.eval]⟩
      · exact ⟨.scaled 1 (.inl (i,1)), fun x => by simp [Readout.eval]⟩
    · exact j.elim0
  | step p g ih =>
    obtain ⟨m,hm,q,hq⟩ := ih
    obtain ⟨l,hl,r,hk,hr⟩ := scale φ η hη coords q g.leftCoeff (hq g.left)
    obtain ⟨s,hs,z,hk',hz⟩ := scale φ η hη coords r g.rightCoeff
      ((hq g.right).keep φ η hk)
    obtain ⟨n,hn,out,hk'',hav⟩ := add φ η z (hr.keep φ η hk') hz
    have keep {f} (H : Represented φ η q f) : Represented φ η out f :=
      H.keep φ η (fun _ hh => hk'' _ (hk' _ (hk _ hh)))
    refine ⟨n, by omega, out, ?_⟩
    rintro (i | j)
    · exact keep (hq (.inl i))
    · exact Fin.cases hav (fun j => keep (hq (.inr j))) j

private theorem simulateOutputs {c d : R} (hη : η^2 = φ c + η*φ d)
    (coords : ∀ s, ∃ a b : R, φ a + η*φ b = s) {m t : ℕ} (p : Circuit S I O t)
    (q : Program R (I × Fin 2) m) (hq : ∀ w : I ⊕ Fin t,
      Represented φ η q (fun x => Sum.elim (decode φ η x) (p.program.value (decode φ η x)) w))
    (rows : Finset O) :
    ∃ n ≤ m + 2*rows.card, ∃ r : Program R (I × Fin 2) n, Keeps q r ∧
      ∀ o ∈ rows, Represented φ η r (fun x => p.eval (decode φ η x) o) := by
  classical
  induction rows using Finset.induction_on with
  | empty => exact ⟨m, by simp, q, fun _ h => h, by simp⟩
  | @insert o rows ho ih =>
    obtain ⟨n,hn,r,hk,hr⟩ := ih
    have step : ∃ s ≤ n+2, ∃ z : Program R (I × Fin 2) s, Keeps r z ∧
        Represented φ η z (fun x => p.eval (decode φ η x) o) := by
      unfold Circuit.eval
      cases H : p.output o with
      | zero =>
        have hz : Available r (fun _ => 0) := ⟨.zero, fun _ => rfl⟩
        exact ⟨n, by omega, r, fun _ h => h, _, _, hz, hz, fun x => by simp [Readout.eval]⟩
      | scaled a w => exact scale φ η hη coords r a ((hq w).keep φ η hk)
    obtain ⟨s,hs,z,hk',hz⟩ := step
    refine ⟨s, ?_, z, fun _ h => hk' _ (hk _ h), fun i hi => ?_⟩
    · rw [Finset.card_insert_of_notMem ho]
      omega
    · rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hz
      · exact (hr i hi).keep φ η hk'

/-- Restriction of scalars for a binary linear circuit over a quadratic algebra.
A spanning pair suffices. Both its input and its output are represented in the
coordinates `1, η`. -/
theorem circuit [Fintype O] {c d : R} (hη : η^2 = φ c + η*φ d)
    (coords : ∀ s, ∃ a b : R, φ a + η*φ b = s) {t : ℕ} (p : Circuit S I O t) :
    ∃ n ≤ 6*t + 2*Fintype.card O, ∃ q : Circuit R (I × Fin 2) (O × Fin 2) n,
      ∀ x o, decode φ η (q.eval x) o = p.eval (decode φ η x) o := by
  obtain ⟨m,hm,r,hr⟩ := simulate φ η hη coords p.program
  obtain ⟨n,hn,q,_,hq⟩ := simulateOutputs φ η hη coords p r hr Finset.univ
  choose u v hu hv he using fun o => hq o (Finset.mem_univ o)
  choose U hU using hu
  choose V hV using hv
  refine ⟨n, by simpa using hn.trans (Nat.add_le_add_right hm _),
    ⟨q, fun o => if o.2 = 0 then U o.1 else V o.1⟩, fun x o => ?_⟩
  simpa [decode, Circuit.eval, hU, hV] using he o x

end QuadraticDescent

end FiniteFourier
end LinearAlgebra
end OAI
