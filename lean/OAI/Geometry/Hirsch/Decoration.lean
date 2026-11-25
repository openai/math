import OAI.Geometry.Hirsch.Names

noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Board

theorem choose_by_rank {X : Type} {Y : X → Type} (rank : X → ℕ) (init : ∀ i, Y i)
    (prop : (∀ i, Y i) → X → Prop)
    (step : ∀ i (a : ∀ i, Y i), ∃ y : Y i, ∀ b, (∀ j, rank j < rank i → a j = b j) → b i = y → prop b i) :
    ∃ b, ∀ i, prop b i := by
  choose take ht using step
  let F := fun i (a : ∀ j, rank j < rank i → Y j) => take i (fun j => if h : rank j < rank i then a j h else init j)
  let wf : WellFounded (fun j i => rank j < rank i) := (measure rank).wf
  let b := wf.fix F
  refine ⟨b,fun i => ht i (fun j => if rank j < rank i then b j else init j) b (by intros; simp_all) ?_⟩
  exact wf.fix_eq F i

namespace Legs.Decoration

open Naming

variable {u : Dials} {X : Type} {L : Legs u X} (A : L.Decoration) (v : u.Valid)

def Earn (a : u.Ticket) (bin : ℕ) (g : X) :=
  ∀ s : Radii u, block u (u.phase a) s = bin → ∀ Q : Network u (NodeName u),
    (A.active s).Agree Q (A.name s) (u.phase a) (Network.window u) g → Q.want v a (A.name s g)

def Promised (i : X) := ∀ a (r : Radii u) j, L.along i (!(u.side a)) j →
  A.Earn v a (block u (u.phase a) r) (L.w.step j (u.side a)) →
  L.w.live ((A i).slot a r) ∧ A.Earn v a (block u (u.phase a) r) (L.w.step ((A i).slot a r) (u.side a))

def Below (A B : L.Decoration) (k : ℕ) := ∀ i, L.w.rank i < k → A i = B i

variable {A} {B : L.Decoration} {k : ℕ} {i : X}

theorem ball_eq {P : X → Prop} (hc : ∀ i, P i → ∀ a, P (A.fan i a))
    (he : ∀ i, P i → ∀ a, A.fan i a = B.fan i a) (n : ℕ) (hi : P i) :
    A.fan.ball n i = B.fan.ball n i := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    simp only [Edges.ball]
    congr 2
    funext a; rw [← he _ hi a]; exact ih (hc _ hi _)

theorem fan_eq (h : (A i).slot = (B i).slot) (a : Label u) : A.fan i a = B.fan i a := by
  rcases a with d | ⟨t,r⟩
  · rfl
  · simp only [fan,h]

namespace Below

variable (h : A.Below B k) (hi : L.w.rank i < k)
include h hi

theorem data : A.data i = B.data i := by
  unfold Decoration.data
  congr 2
  funext n
  have eq := ball_eq (P := fun j => L.w.rank j < k) (fun j hj a => (A.decrease j a).trans_lt hj)
    (fun j hj => fan_eq (congrArg Node.slot (h _ hj))) n.val hi
  unfold Edges.tally
  rw [← eq]
  let _ : DecidableEq (Symbol u) := fun _ _ => propDecidable _
  apply Finset.image_congr
  intro j hj
  exact congrArg Node.symbol (h _ ((A.fan.decreasing _ A.decrease _ _ _ hj).trans_lt hi))

theorem view (n : ℕ) : A.fan.view A.data n i = B.fan.view B.data n i := by
  induction n generalizing i with
  | zero => exact h.data hi
  | succ n ih =>
    simp only [Edges.view,ih hi]
    congr 1
    funext a
    rw [← fan_eq (congrArg Node.slot (h _ hi)) a]
    exact ih ((A.decrease _ _).trans_lt hi)

theorem name (r : Radii u) : A.name r i = B.name r i := congrArg (Sigma.mk r) (h.view hi r.val)

theorem agree (r : Radii u) (Q : Network u (NodeName u)) (p n : ℕ) :
    (A.active r).Agree Q (A.name r) p n i ↔ (B.active r).Agree Q (B.name r) p n i := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    have eq := h.name hi r
    have step : ∀ d, L.w.live i → L.w.rank (L.w.step i d) < k := fun d hl => (L.w.decrease i hl d).trans hi
    have slot : ∀ t, L.w.rank ((A i).slot t r) < k := fun t => (A.decrease i (.inr (t,r))).trans_lt hi
    have basic : ∀ d, L.w.live i →
        (A.name r (L.w.step i d) = Q.w.step (A.name r i) d ∧ (A.active r).Agree Q (A.name r) p n (L.w.step i d) ↔
         B.name r (L.w.step i d) = Q.w.step (B.name r i) d ∧ (B.active r).Agree Q (B.name r) p n (L.w.step i d)) :=
      fun d hl => by rw [h.name (step d hl),eq,ih (step d hl)]
    have jump : ∀ t, (A.name r ((A i).slot t r) = Q.slot t (A.name r i) ∧
        (A.active r).Agree Q (A.name r) p n ((A i).slot t r) ↔
        B.name r ((B i).slot t r) = Q.slot t (B.name r i) ∧ (B.active r).Agree Q (B.name r) p n ((B i).slot t r)) :=
      fun t => by rw [← h _ hi,h.name (slot t),eq,ih (slot t)]
    constructor
    · exact fun hh => ⟨eq ▸ hh.1,eq ▸ hh.2.1,fun d hl => (basic d hl).mp (hh.2.2.1 d hl),
        fun t ht => (jump t).mp (hh.2.2.2 t ht)⟩
    · exact fun hh => ⟨eq.symm ▸ hh.1,eq.symm ▸ hh.2.1,fun d hl => (basic d hl).mpr (hh.2.2.1 d hl),
        fun t ht => (jump t).mpr (hh.2.2.2 t ht)⟩

theorem earn (a : u.Ticket) (bin : ℕ) : A.Earn v a bin i ↔ B.Earn v a bin i := by
  simp only [Earn,h.agree hi,h.name hi]

end Below

variable (A)

def candidate (i : X) (a : u.Ticket) (bin : ℕ) (j : X) :=
  L.along i (!(u.side a)) j ∧ A.Earn v a bin (L.w.step j (u.side a))

def pick (i : X) (a : u.Ticket) (bin : ℕ) := if h : ∃ j, A.candidate v i a bin j then h.choose else i

def plan (i : X) (sym : Symbol u) : L.Node i where
  slot a r := A.pick v i a (block u (u.phase a) r)
  valid a r := by
    unfold pick; split
    · rename_i h; exact .inr h.choose_spec.1
    · exact .inl rfl
  symbol := sym

theorem promised (h : A.Below B (L.w.rank i)) (sym : Symbol u) (hi : B i = A.plan v i sym) :
    B.Promised v i := by
  intro a r j hj he
  let bin := block u (u.phase a) r
  have low : ∀ j, L.along i (!(u.side a)) j → L.w.rank (L.w.step j (u.side a)) < L.w.rank i := by
    intro j hj
    obtain ⟨_,_,hl,_,_,he⟩ := L.info _ _ _ hj
    exact (L.w.decrease _ hl _).trans_le (he.elim (fun h => by rw [h]) LT.lt.le)
  have ex : ∃ j, A.candidate v i a bin j := ⟨j,hj,(h.earn v (low _ hj) a bin).mpr he⟩
  have eq : (B i).slot a r = ex.choose := by rw [hi]; exact dite_eq_left ex
  obtain ⟨hj,he⟩ := ex.choose_spec
  rw [eq]
  exact ⟨(L.info _ _ _ hj).2.2.1,(h.earn v (low _ hj) a bin).mp he⟩

theorem exists_decoration (L : Legs u X) (v : u.Valid) :
    ∃ A : L.Decoration, A.Safe ∧ A.Fixed ∧ ∀ i, A.Promised v i := by
  let goal := fun (B : L.Decoration) i =>
    (∀ j ∈ B.fan.ball (M u+1) i, L.w.rank j < L.w.rank i → B.symbol i ≠ B.symbol j) ∧
    (∀ a (r s : Radii u), block u (u.phase a) r = block u (u.phase a) s → (B i).slot a r = (B i).slot a s) ∧
    B.Promised v i
  suffices ∃ B, ∀ i, goal B i by
    obtain ⟨B,hB⟩ := this
    exact ⟨B,fun i => (hB i).1,fun i => (hB i).2.1,fun i => (hB i).2.2⟩
  apply choose_by_rank L.w.rank L.empty
  intro i A
  let trial : L.Decoration := Function.update A i (plan A v i 0)
  let used := (trial.fan.ball (M u+1) i).image trial.symbol
  have size : used.card < Fintype.card (Symbol u) := by
    rw [Fintype.card_fin]
    exact Nat.lt_succ_of_le (Finset.card_image_le.trans (trial.fan.card _ _))
  obtain ⟨sym,hs⟩ : ∃ sym, sym ∉ used := by
    by_contra! hh
    exact size.not_ge (Finset.card_le_card (show Finset.univ ⊆ used from fun x _ => hh x))
  refine ⟨plan A v i sym,fun B h hi => ⟨?_,?_,promised A v h sym hi⟩⟩
  · intro j hj hr he
    have lower : ∀ j, L.w.rank j < L.w.rank i → B j = trial j := by
      intro j hh
      have hn : j ≠ i := fun he => hh.ne (congrArg L.w.rank he)
      simp [trial,hn,h _ hh]
    let near := fun j => j = i ∨ L.w.rank j < L.w.rank i
    have closed : ∀ j, near j → ∀ a, near (fan B j a) := by
      rintro j (rfl | hj) a
      · by_cases he : fan B j a = j
        · exact .inl he
        · exact .inr (fall B _ _ he)
      · exact .inr ((decrease B _ _).trans_lt hj)
    have same : ∀ j, near j → ∀ a, fan B j a = trial.fan j a := by
      intro j hj
      apply fan_eq
      rcases hj with rfl | hj
      · simp [hi,trial,plan]
      · rw [lower _ hj]
    rw [ball_eq closed same _ (.inl rfl)] at hj
    apply hs
    have eq : trial.symbol j = sym := by simpa [symbol,hi,plan,lower _ hr] using he.symm
    exact Finset.mem_image.mpr ⟨j,hj,eq⟩
  · intro a r s he; simp [hi,plan,he]

end Legs.Decoration
end OAI.Geometry.Hirsch.Layer.Board
