import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic.DeriveFintype

/-!
# Directed Hamiltonian-cycle graph for exact-one clauses

Each variable has a track with endpoints, one pair of ports per occurrence slot, and a
buffer between successive pairs. At the slot belonging to a literal, the directed
crossing for the literal's true value passes through its clause vertex. The opposite
crossing uses the edge between the ports.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace HCGadget

/-- The Hamiltonian reduction has a track for each variable, ports for literal occurrences,
separators between tracks, and one vertex per clause. -/
inductive Vertex (k h c : ℕ) where
  | sep (i : Fin k)
  | endpoint (i : Fin k) (side : Bool)
  | buffer (i : Fin k) (j : Fin (h + 1))
  | port (i : Fin k) (j : Fin h) (side : Bool)
  | clause (a : Fin c)
  deriving DecidableEq, Fintype

variable {k h c : ℕ}

/-- Left neighbor of a buffer in the linear order on its track. -/
def prevPort (i : Fin k) (j : Fin (h + 1)) : Vertex k h c :=
  Fin.cases (.endpoint i false) (fun s => .port i s true) j

/-- Right neighbor of a buffer in the linear order on its track. -/
def nextPort (i : Fin k) (j : Fin (h + 1)) : Vertex k h c :=
  Fin.lastCases (.endpoint i true) (fun s => .port i s false) j

/-- Each port has exactly one adjacent buffer along its track. -/
def portBuffer (i : Fin k) (j : Fin h) (b : Bool) : Vertex k h c :=
  .buffer i (if b then j.succ else j.castSucc)

@[simp] theorem prevPort_zero (i : Fin k) : prevPort (h := h) (c := c) i 0 = .endpoint i false := rfl

@[simp] theorem prevPort_succ (i : Fin k) (j : Fin h) :
    prevPort (c := c) i j.succ = .port i j true := by simp [prevPort]

@[simp] theorem nextPort_last (i : Fin k) :
    nextPort (c := c) i (Fin.last h) = .endpoint i true := by simp [nextPort]

@[simp] theorem nextPort_castSucc (i : Fin k) (j : Fin h) :
    nextPort (c := c) i j.castSucc = .port i j false := by simp [nextPort]

/-- Allowed directed edges. The occurrence data give the variable, clause and
satisfying variable value of each slot. -/
inductive Allowed (occ : Fin h → Fin k × Fin c × Bool) : Vertex k h c → Vertex k h c → Prop
  | bufferPrev (i : Fin k) (j : Fin (h + 1)) : Allowed occ (.buffer i j) (prevPort i j)
  | prevBuffer (i : Fin k) (j : Fin (h + 1)) : Allowed occ (prevPort i j) (.buffer i j)
  | bufferNext (i : Fin k) (j : Fin (h + 1)) : Allowed occ (.buffer i j) (nextPort i j)
  | nextBuffer (i : Fin k) (j : Fin (h + 1)) : Allowed occ (nextPort i j) (.buffer i j)
  | enterTrack (i : Fin k) (b : Bool) : Allowed occ (.sep i) (.endpoint i b)
  | exitTrack (i : Fin k) (b : Bool) : Allowed occ (.endpoint i b) (.sep (finRotate k i))
  | cross (i : Fin k) (j : Fin h) (b : Bool) (inactive : (occ j).1 ≠ i ∨ (occ j).2.2 = b) :
      Allowed occ (.port i j b) (.port i j (!b))
  | enterClause (j : Fin h) : Allowed occ (.port (occ j).1 j (!(occ j).2.2)) (.clause (occ j).2.1)
  | exitClause (j : Fin h) : Allowed occ (.clause (occ j).2.1) (.port (occ j).1 j (occ j).2.2)

/-- The graph uses polynomially many vertices, including for empty occurrence lists. -/
theorem card_vertex (k h c : ℕ) : Fintype.card (Vertex k h c) = k * (3 * h + 4) + c := by
  rw [← Fintype.card_congr (proxy_equiv% (Vertex k h c))]
  simp
  ring


variable {occ : Fin h → Fin k × Fin c × Bool}
variable {i : Fin k} {j : Fin (h + 1)} {a : Fin c} {v : Vertex k h c}

private def isPortOrEndpoint : Vertex k h c → Bool
  | .port .. | .endpoint .. => true
  | _ => false

private theorem prevPort_kind (i : Fin k) (j : Fin (h + 1)) :
    isPortOrEndpoint (prevPort (c := c) i j) = true := by
  cases j using Fin.cases <;> simp [isPortOrEndpoint]

private theorem nextPort_kind (i : Fin k) (j : Fin (h + 1)) :
    isPortOrEndpoint (nextPort (c := c) i j) = true := by
  cases j using Fin.lastCases <;> simp [isPortOrEndpoint]

private theorem ne_prevPort_of_kind_false (u : Vertex k h c) (i : Fin k)
    (j : Fin (h + 1)) (hu : isPortOrEndpoint u = false) : u ≠ prevPort i j := by
  intro e
  have he := congrArg isPortOrEndpoint e
  simp only [hu, prevPort_kind] at he
  contradiction

private theorem ne_nextPort_of_kind_false (u : Vertex k h c) (i : Fin k)
    (j : Fin (h + 1)) (hu : isPortOrEndpoint u = false) : u ≠ nextPort i j := by
  intro e
  have he := congrArg isPortOrEndpoint e
  simp only [hu, nextPort_kind] at he
  contradiction

theorem allowed_from_buffer_iff :
    Allowed occ (.buffer i j) v ↔ v = prevPort i j ∨ v = nextPort i j := by
  constructor
  · intro e
    generalize hv : Vertex.buffer i j = u at e
    cases e <;> (try simp_all) <;>
      first | exact (ne_prevPort_of_kind_false _ _ _ rfl hv).elim
            | exact (ne_nextPort_of_kind_false _ _ _ rfl hv).elim
  · rintro (rfl | rfl)
    · exact .bufferPrev i j
    · exact .bufferNext i j

theorem allowed_to_buffer_iff :
    Allowed occ v (.buffer i j) ↔ v = prevPort i j ∨ v = nextPort i j := by
  constructor
  · intro e
    generalize hv : Vertex.buffer i j = u at e
    cases e <;> (try simp_all) <;>
      first | exact (ne_prevPort_of_kind_false _ _ _ rfl hv).elim
            | exact (ne_nextPort_of_kind_false _ _ _ rfl hv).elim
  · rintro (rfl | rfl)
    · exact .prevBuffer i j
    · exact .nextBuffer i j

theorem allowed_from_sep_iff :
    Allowed occ (.sep i) v ↔ ∃ b, v = .endpoint i b := by
  constructor
  · intro e
    generalize hv : Vertex.sep i = u at e
    cases e <;> (try simp_all) <;>
      first | exact (ne_prevPort_of_kind_false _ _ _ rfl hv).elim
            | exact (ne_nextPort_of_kind_false _ _ _ rfl hv).elim
  · rintro ⟨b, rfl⟩
    exact .enterTrack i b

theorem allowed_to_sep_iff :
    Allowed occ v (.sep i) ↔ ∃ b, v = .endpoint ((finRotate k).symm i) b := by
  constructor
  · intro e
    generalize hv : Vertex.sep i = u at e
    cases e <;> (try simp_all [-finRotate_apply, -finRotate_symm_apply]) <;>
      first | exact (ne_prevPort_of_kind_false _ _ _ rfl hv).elim
            | exact (ne_nextPort_of_kind_false _ _ _ rfl hv).elim
  · rintro ⟨b, rfl⟩
    simpa only [Equiv.apply_symm_apply] using Allowed.exitTrack (occ := occ) ((finRotate k).symm i) b

theorem allowed_from_clause_iff :
    Allowed occ (.clause a) v ↔ ∃ j, (occ j).2.1 = a ∧ v = .port (occ j).1 j (occ j).2.2 := by
  constructor
  · intro e
    generalize hv : Vertex.clause a = u at e
    cases e <;> (try simp_all) <;>
      first | exact (ne_prevPort_of_kind_false _ _ _ rfl hv).elim
            | exact (ne_nextPort_of_kind_false _ _ _ rfl hv).elim
  · rintro ⟨j, rfl, rfl⟩
    exact .exitClause j

theorem allowed_to_clause_iff :
    Allowed occ v (.clause a) ↔ ∃ j, (occ j).2.1 = a ∧ v = .port (occ j).1 j (!(occ j).2.2) := by
  constructor
  · intro e
    generalize hv : Vertex.clause a = u at e
    cases e <;> (try simp_all) <;>
      first | exact (ne_prevPort_of_kind_false _ _ _ rfl hv).elim
            | exact (ne_nextPort_of_kind_false _ _ _ rfl hv).elim
  · rintro ⟨j, rfl, rfl⟩
    exact .enterClause j

end HCGadget

end VPVNP
end Computability
end OAI
