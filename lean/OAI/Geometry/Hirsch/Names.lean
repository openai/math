import OAI.Geometry.Hirsch.Realization

noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Board

namespace Naming

variable (u : Dials)

def P := 2*u.h
def R := Network.window u + 2 + Network.size u * (u.D u.h).step
def M := 2*Edges.bound (Network.Action u) (R u)
def H := 2*(P u+1)*(M u)^2+1
def N := H u^(P u+1)

theorem Hpos : 0 < H u := Nat.zero_lt_succ _
theorem Npos : 0 < N u := pow_pos (Hpos u) _

abbrev Radii := Fin (N u)
abbrev Label := Bool ⊕ (u.Ticket × Radii u)
abbrev Symbol := Fin (Edges.bound (Label u) (M u+1)+1)
abbrev NodeData := Fin (Network.size u) × Bool × (Fin (M u+1) → Finset (Symbol u))
def NodeName := Σ r : Radii u, Edges.View (Label u) (NodeData u) r.val

instance : Fintype (NodeName u) := inferInstanceAs (Fintype (Σ r : Radii u, Edges.View (Label u) (NodeData u) r.val))

def length (p : ℕ) := H u^(P u-p)
def block (p r : ℕ) := r / length u p

theorem length_pos (p : ℕ) : 0 < length u p := pow_pos (Hpos u) _

theorem ancestor {p q r s : ℕ} (hq : q < p) (hp : p ≤ P u)
    (h : block u p r / H u = block u p s / H u) : block u q r = block u q s := by
  have he : length u q = (length u p * H u)*H u^(p-q-1) := by
    unfold length; rw [← pow_succ,← pow_add]; congr 1; omega
  simp only [block,he,← Nat.div_div_eq_div_mul]
  exact congrArg (· / _) h

end Naming

open Naming

structure Legs (u : Dials) (X : Type) where
  w : Board X (u.a^u.h)
  along : X → Bool → X → Prop
  info : ∀ i d j, along i d j → w.Middle i ∧ w.live i ∧ w.live j ∧
    w.layer j = w.layer i ∧ w.step j d = w.step i d ∧ (j = i ∨ w.rank j < w.rank i)

namespace Legs

variable {u : Dials} {X : Type} (L : Legs u X)

structure Node (i : X) where
  slot : u.Ticket → Radii u → X
  valid : ∀ a r, slot a r = i ∨ L.along i (!(u.side a)) (slot a r)
  symbol : Symbol u

def empty (i : X) : L.Node i := ⟨fun _ _ => i,fun _ _ => .inl rfl,0⟩

abbrev Decoration := ∀ i, L.Node i

namespace Decoration

variable {L} (A : L.Decoration)

def active (r : Radii u) : Network u X where
  w := L.w
  slot a i := (A i).slot a r
  same a i := ((A i).valid a r).elim (congrArg L.w.layer) (fun h => (L.info _ _ _ h).2.2.2.1)
  jump a i hn := by
    have hh := L.info _ _ _ (((A i).valid a r).resolve_left hn)
    exact ⟨hh.2.1,hh.2.2.2.2.2.resolve_left hn⟩

def fan : Edges X (Label u) := fun i a => match a with
  | .inl d => if L.w.live i then L.w.step i d else i
  | .inr (t,r) => (A i).slot t r

theorem fall (i : X) (a : Label u) (hn : A.fan i a ≠ i) : L.w.rank (A.fan i a) < L.w.rank i := by
  rcases a with d | ⟨t,r⟩
  · by_cases hl : L.w.live i
    · simpa [fan,hl] using L.w.decrease i hl d
    · simp [fan,hl] at hn
  · exact ((A.active r).jump t i hn).2

theorem decrease (i : X) (a : Label u) : L.w.rank (A.fan i a) ≤ L.w.rank i := by
  by_cases he : A.fan i a = i
  · rw [he]
  · exact (A.fall i a he).le

def symbol (i : X) := (A i).symbol

def data (i : X) : NodeData u := (⟨L.w.layer i,L.w.bound i⟩,decide (L.w.live i),
  fun k => A.fan.tally A.symbol k i)

def name (r : Radii u) (i : X) : NodeName u := ⟨r,A.fan.view A.data r i⟩

theorem names (r : Radii u) (i j : X) :
    A.name r i = A.name r j ↔ A.fan.view A.data r.val i = A.fan.view A.data r.val j := by simp [name,NodeName]

def Safe := ∀ i j, j ∈ A.fan.ball (M u+1) i → L.w.rank j < L.w.rank i → A.symbol i ≠ A.symbol j

def Fixed := ∀ i a (r s : Radii u), block u (u.phase a) r.val = block u (u.phase a) s.val → (A i).slot a r = (A i).slot a s

def Break (r : ℕ) (i j : X) := A.fan.view A.data r i = A.fan.view A.data r j ∧
  A.fan.view A.data (r+1) i ≠ A.fan.view A.data (r+1) j

theorem unique_break {i j : X} {r s : ℕ} (hr : A.Break r i j) (hs : A.Break s i j) : r = s := by
  rcases lt_trichotomy r s with hh | hh | hh
  · exact (hr.2 (A.fan.trunc A.data hh hs.1)).elim
  · exact hh
  · exact (hs.2 (A.fan.trunc A.data hh hr.1)).elim

theorem model (safe : A.Safe) (r : Radii u) (p : ℕ) (B : Finset X) (hb : B.card ≤ M u)
    (good : ∀ i ∈ B, ∀ j ∈ B, ¬A.Break r i j) (x : X) :
    ∃ Q : Network u (NodeName u), ∀ k i, (A.active r).ball p k i ⊆ B → (A.active r).Agree Q (A.name r) p k i := by
  let _ : DecidableEq (Symbol u) := fun _ _ => propDecidable _
  let S := B.image A.symbol
  have bound : S.card ≤ M u := Finset.card_image_le.trans hb
  have data : ∀ i j, A.name r i = A.name r j → A.data i = A.data j :=
    fun i j h => A.fan.trunc A.data (Nat.zero_le _) ((A.names _ _ _).mp h)
  apply Network.Consistent.realize (rank := A.fan.score A.symbol S (M u)) _ x
  refine ⟨fun i j h => congrArg (fun a : NodeData u => a.1.val) (data i j h),?_,?_,?_,?_⟩
  · intro i j h
    exact decide_eq_decide.mp (congrArg (fun a : NodeData u => a.2.1) (data i j h))
  · intro i j h
    apply Finset.sum_congr rfl
    intro k hk
    have hh := congrArg (fun a : NodeData u => a.2.2 ⟨k,Finset.mem_range.mp hk⟩) (data i j h)
    exact congrArg (fun s => (s ∩ S).card) hh
  · intro i hi j hj h a
    have eq : A.fan.view A.data (r.val+1) i = A.fan.view A.data (r.val+1) j :=
      by_contra fun hn => good i hi j hj ⟨(A.names _ _ _).mp h,hn⟩
    have each : ∀ a, A.name r (A.fan i a) = A.name r (A.fan j a) :=
      fun a => (A.names _ _ _).mpr (A.fan.targets _ eq a)
    rcases a with d | a
    · exact each (.inl d)
    · by_cases ha : u.phase a < p
      · simpa [Network.edges,ha,active,fan] using each (.inr (a,r))
      · simpa [Network.edges,ha] using h
  intro i hi a hn
  have ex : ∃ b, (A.active r).edges p i a = A.fan i b := by
    rcases a with d | a
    · exact ⟨.inl d,rfl⟩
    · by_cases ha : u.phase a < p
      · exact ⟨.inr (a,r),by simp [Network.edges,ha,active,fan]⟩
      · simp [Network.edges,ha] at hn
  obtain ⟨b,he⟩ := ex
  rw [he] at hn ⊢
  apply A.fan.score_falls A.symbol S bound (Finset.mem_image_of_mem _ hi)
  intro hh
  obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hh
  exact safe i j (A.fan.sub _ _ _ hj) ((A.fan.decreasing _ A.decrease _ _ j hj).trans_lt (A.fall _ _ hn)) he.symm

end Decoration
end Legs
end OAI.Geometry.Hirsch.Layer.Board
