import OAI.LinearAlgebra.SpectralBooks.PortNetwork
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Log

/-! # Local certificates for bounded-radius port views

The four slots at each visit are indexed by departure port number. Each occupied
slot gives the arrival port at the other end of that same wire and the view from
there. Padding unoccupied slots with `none` gives one encoding even for a vertex
of degree zero. The alphabet `A` carries the base fields and the vertex type.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace PortGraph

variable {V E : Type*} (G : PortGraph V E)

/-- Port numbers, with the four possible port positions indexed from zero. -/
abbrev FourPortNumbering := (v : V) → G.Port v ↪ Fin 4

/-- Degree at most four provides the slots needed by the certificate. -/
theorem exists_fourPortNumbering [∀ v, Fintype (G.Port v)]
    (h : ∀ v, Fintype.card (G.Port v) ≤ 4) : Nonempty G.FourPortNumbering := by
  classical
  exact ⟨fun v => (Function.Embedding.nonempty_of_card_le (β := Fin 4) (by simpa using h v)).some⟩

/-- The paired port on the same wire, retaining its new incoming/outgoing side. -/
def pairedPort {v : V} (p : G.Port v) : G.Port (G.vertex p.1.1 (!p.1.2)) :=
  ⟨(p.1.1, !p.1.2), rfl⟩

/-- The neighbor and its arrival port as seen from a numbered departure slot. -/
noncomputable def portStep (num : G.FourPortNumbering) (v : V) (i : Fin 4) : Option (V × Fin 4) := by
  classical
  exact if h : ∃ p : G.Port v, num v p = i then
    let p := h.choose
    some (G.vertex p.1.1 (!p.1.2), num _ (G.pairedPort p)) else none

@[simp] theorem portStep_port (num : G.FourPortNumbering) {v : V} (p : G.Port v) :
    G.portStep num v (num v p) = some (G.vertex p.1.1 (!p.1.2), num _ (G.pairedPort p)) := by
  classical
  have h : ∃ q : G.Port v, num v q = num v p := ⟨p, rfl⟩
  unfold portStep
  rw [dite_eq_left h]
  exact congrArg (fun q : G.Port v => some (G.vertex q.1.1 (!q.1.2), num _ (G.pairedPort q)))
    ((num v).injective h.choose_spec)

@[simp] theorem portStep_missing (num : G.FourPortNumbering) (v : V) (i : Fin 4)
    (h : ¬∃ p : G.Port v, num v p = i) : G.portStep num v i = none := by
  classical
  simp [portStep, h]

universe u

/-- The tree of walks of length at most `r`, including a slot for every possible
one-port continuation, including immediate reversal of the previous step. -/
def PortView (A : Type u) : ℕ → Type u
  | 0 => A
  | r + 1 => A × (Fin 4 → Option (Fin 4 × PortView A r))

namespace PortView

variable {A : Type u}

/-- Remove the final layer of a view, retaining all earlier arrival ports. -/
def truncate : (r : ℕ) → PortView A (r + 1) → PortView A r
  | 0, z => z.1
  | r + 1, z => (z.1, fun i => (z.2 i).map (fun a => (a.1, truncate r a.2)))

variable {G} (num : G.FourPortNumbering) (base : V → A)

/-- The genuine records, obtained by traversing the actual paired ports. -/
noncomputable def actual : (r : ℕ) → V → PortView A r
  | 0, v => base v
  | r + 1, v => (base v, fun i => (G.portStep num v i).map (fun a => (a.2, actual r a.1)))

/-- The vertex checks its own base data and its unused slots. Each departure
port checks the arrival at its partner and compares the suffix to the partner's
record truncated by one level. All comparisons involve just one vertex or wire. -/
def LocalTests : (r : ℕ) → (V → PortView A r) → Prop
  | 0, z => ∀ v, z v = base v
  | r + 1, z => ∀ v, (z v).1 = base v ∧ ∀ i, (z v).2 i =
      (G.portStep num v i).map (fun a => (a.2, truncate r (z a.1)))

/-- The vertex predicate reads just the root entry and slots not occupied by a port. -/
def VertexTest (v : V) : (r : ℕ) → PortView A r → Prop
  | 0, z => z = base v
  | _ + 1, z => z.1 = base v ∧ ∀ i, (¬∃ p : G.Port v, num v p = i) → z.2 i = none

/-- The endpoint predicate reads the two records on one wire, checking arrival
and the suffix in the direction of the chosen departure port. -/
def PortTest {v : V} (p : G.Port v) : (r : ℕ) → PortView A r → PortView A r → Prop
  | 0, _, _ => True
  | r + 1, z, w => z.2 (num v p) = some (num _ (G.pairedPort p), truncate r w)

/-- Both endpoint tests apply to a loop as well as to an ordinary wire. -/
def EdgeTest (e : E) (r : ℕ) (z w : PortView A r) : Prop :=
  PortTest num (v := G.tail e) ⟨(e, false), rfl⟩ r z w ∧
  PortTest num (v := G.head e) ⟨(e, true), rfl⟩ r w z

/-- The view test factors into a predicate at each vertex and a predicate on
pairs of records at the endpoints of each oriented edge. -/
theorem localTests_iff_vertex_edge (r : ℕ) (z : V → PortView A r) :
    LocalTests num base r z ↔ (∀ v, VertexTest num base v r (z v)) ∧
      ∀ e, EdgeTest num e r (z (G.tail e)) (z (G.head e)) := by
  cases r with
  | zero => exact ⟨fun h => ⟨h, fun _ => ⟨trivial, trivial⟩⟩, fun h => h.1⟩
  | succ r =>
    constructor
    · intro h
      have hp {v : V} (p : G.Port v) : PortTest num p (r + 1) (z v) (z (G.vertex p.1.1 (!p.1.2))) := by
        simpa only [PortTest, portStep_port, Option.map_some] using (h v).2 (num v p)
      exact ⟨fun v => ⟨(h v).1, fun i hi => by rw [(h v).2, portStep_missing _ _ _ _ hi]; rfl⟩,
        fun e => ⟨hp (v := G.tail e) ⟨(e, false), rfl⟩, hp (v := G.head e) ⟨(e, true), rfl⟩⟩⟩
    · rintro ⟨hv, he⟩ v
      refine ⟨(hv v).1, fun i => ?_⟩
      by_cases h : ∃ p : G.Port v, num v p = i
      · obtain ⟨⟨⟨e, b⟩, rfl⟩, rfl⟩ := h
        rw [portStep_port, Option.map_some]
        cases b with
        | false => exact (he e).1
        | true => exact (he e).2
      · rw [portStep_missing _ _ _ _ h]
        exact (hv v).2 i h

private theorem truncate_actual (r : ℕ) (v : V) :
    truncate r (actual num base (r + 1) v) = actual num base r v := by
  induction r generalizing v with
  | zero => rfl
  | succ r ih =>
    apply Prod.ext
    · rfl
    · funext i
      change (((G.portStep num v i).map (fun a => (a.2, actual num base (r + 1) a.1))).map _) = _
      cases h : G.portStep num v i with
      | none => change _ = (G.portStep num v i).map _; rw [h]; rfl
      | some a =>
        change some (a.2, truncate r (actual num base (r + 1) a.1)) = (G.portStep num v i).map _
        rw [h, ih]
        rfl

theorem actual_valid (r : ℕ) : LocalTests num base r (actual num base r) := by
  cases r with
  | zero => exact fun _ => rfl
  | succ r =>
    intro v
    refine ⟨rfl, fun i => ?_⟩
    change (G.portStep num v i).map _ = (G.portStep num v i).map _
    simp only [truncate_actual]

private theorem truncate_valid {r : ℕ} {z : V → PortView A (r + 1)}
    (hz : LocalTests num base (r + 1) z) : LocalTests num base r (fun v => truncate r (z v)) := by
  cases r with
  | zero => exact fun v => (hz v).1
  | succ r =>
    intro v
    refine ⟨(hz v).1, fun i => ?_⟩
    change ((z v).2 i).map _ = _
    rw [(hz v).2]
    cases G.portStep num v i <;> rfl

/-- A global family of locally consistent records is precisely the genuine view
at every vertex, including for loops, parallel wires and isolated vertices. -/
theorem localTests_iff {r : ℕ} (z : V → PortView A r) :
    LocalTests num base r z ↔ z = actual num base r := by
  refine ⟨fun hz => ?_, fun he => he ▸ actual_valid num base r⟩
  induction r with
  | zero => exact funext hz
  | succ r ih =>
    have h := ih (fun v => truncate r (z v)) (truncate_valid num base hz)
    funext v
    apply Prod.ext (hz v).1
    funext i
    have hh (w : V) : truncate r (z w) = actual num base r w := congrFun h w
    change (z v).2 i = (G.portStep num v i).map (fun a => (a.2, actual num base r a.1))
    simpa only [hh] using (hz v).2 i

/-- There is exactly one view assignment passing the vertex and edge tests. -/
theorem existsUnique_localTests (r : ℕ) : ∃! z, LocalTests num base r z :=
  ⟨actual num base r, actual_valid num base r, fun z hz => (localTests_iff num base z).mp hz⟩

/-- The view alphabet is finite at every fixed radius. -/
noncomputable instance instFintype [Fintype A] (r : ℕ) : Fintype (PortView A r) := by
  classical
  induction r with
  | zero => exact ‹Fintype A›
  | succ r ih =>
    letI := ih
    exact inferInstanceAs (Fintype (A × (Fin 4 → Option (Fin 4 × PortView A r))))

private theorem card_succ [Fintype A] (r : ℕ) :
    Fintype.card (PortView A (r + 1)) = Fintype.card A * (4 * Fintype.card (PortView A r) + 1) ^ 4 := by
  change Fintype.card (A × (Fin 4 → Option (Fin 4 × PortView A r))) = _
  simp

/-- A polynomial bound on the base alphabet gives a polynomial bound on the
entire bounded-radius view alphabet, uniformly in the graph. -/
theorem card_le_pow [Fintype A] (r : ℕ) {d N : ℕ} (hN : 0 < N)
    (hA : Fintype.card A ≤ (2 * N) ^ d) :
    Fintype.card (PortView A r) ≤ (2 * N) ^ ((d + 12) * 5 ^ r) := by
  have htwo : 2 ≤ 2 * N := by omega
  have hone : 1 ≤ 2 * N := by omega
  induction r with
  | zero =>
    change Fintype.card A ≤ _
    exact hA.trans (pow_le_pow_right' hone (by simp))
  | succ r ih =>
    let m := (d + 12) * 5 ^ r
    have hm : d + 12 ≤ m := by
      exact Nat.le_mul_of_pos_right _ (by positivity)
    have hslot : 4 * Fintype.card (PortView A r) + 1 ≤ (2 * N) ^ (m + 3) := by
      have hpos : 0 < (2 * N) ^ m := pow_pos (by omega) _
      calc
        _ ≤ (2 * N) ^ m * 5 := by change Fintype.card (PortView A r) ≤ (2 * N) ^ m at ih; omega
        _ ≤ (2 * N) ^ m * (2 * N) ^ 3 := by
          apply Nat.mul_le_mul_left
          exact (by decide : 5 ≤ 2 ^ 3).trans (Nat.pow_le_pow_left htwo 3)
        _ = _ := (pow_add ..).symm
    rw [card_succ]
    calc
      _ ≤ (2 * N) ^ d * ((2 * N) ^ (m + 3)) ^ 4 := Nat.mul_le_mul hA (Nat.pow_le_pow_left hslot 4)
      _ = (2 * N) ^ (d + (m + 3) * 4) := by rw [pow_add (2 * N) d _, pow_mul (2 * N) (m + 3) 4]
      _ ≤ _ := by
        apply pow_le_pow_right' hone
        rw [pow_succ, ← Nat.mul_assoc]
        change d + (m + 3) * 4 ≤ m * 5
        omega

/-- Each possible view has a distinct bit encoding of length at most a fixed
multiple of `⌈log₂(2N)⌉`. In the patch certificate the radius is `2K + 2`. -/
theorem exists_bitEncoding [Fintype A] (r : ℕ) {d N : ℕ} (hN : 0 < N)
    (hA : Fintype.card A ≤ (2 * N) ^ d) :
    Nonempty (PortView A r ↪ (Fin (((d + 12) * 5 ^ r) * Nat.clog 2 (2 * N)) → Bool)) := by
  apply Function.Embedding.nonempty_of_card_le
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.mul_comm, pow_mul]
  exact (card_le_pow r hN hA).trans (Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) _) _)

end PortView
end PortGraph

end SpectralBooks
end LinearAlgebra
end OAI
