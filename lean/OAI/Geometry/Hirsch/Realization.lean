import OAI.Geometry.Hirsch.Neighborhood

noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Board.Network

abbrev Action (u : Dials) := Bool ⊕ u.Ticket

variable {X I : Type} {u : Dials} (Q : Network u X) (p : ℕ)

def edges : Edges X (Action u) := fun i a =>
  match a with
  | .inl d => if Q.w.live i then Q.w.step i d else i
  | .inr a => if u.phase a < p then Q.slot a i else i

def ball := (Q.edges p).ball

variable {Q p} {i : X} {R : ℕ}

theorem basic_sub (hl : Q.w.live i) (d : Bool) : Q.ball p R (Q.w.step i d) ⊆ Q.ball p (R+1) i := by
  simpa [ball,edges,hl] using (Q.edges p).sub R i (.inl d)

theorem slot_sub {a : u.Ticket} (ha : u.phase a < p) : Q.ball p R (Q.slot a i) ⊆ Q.ball p (R+1) i := by
  simpa [ball,edges,ha] using (Q.edges p).sub R i (.inr a)

theorem Agree.compare {Q₁ Q₂ : Network u I} {f g : X → I} {e : Equiv.Perm I}
    (h₁ : Q.Agree Q₁ f p R i) (h₂ : Q.Agree Q₂ g p R i)
    (he : ∀ j ∈ Q.ball p R i, e (f j) = g j) : Q₁.Agree Q₂ e p R (f i) := by
  induction R generalizing i with
  | zero => exact True.intro
  | succ R ih =>
    have eq := he i ((Q.edges p).root _ i)
    simp only [Agree,eq]
    refine ⟨h₁.1.symm.trans h₂.1,h₁.2.1.symm.trans h₂.2.1,?_,?_⟩
    · intro d hl
      have hl' := h₁.2.1.mpr hl
      obtain ⟨e₁,a₁⟩ := h₁.2.2.1 d hl'
      obtain ⟨e₂,a₂⟩ := h₂.2.2.1 d hl'
      rw [← e₁,← e₂]
      have hh := fun j hj => he j (basic_sub hl' d hj)
      exact ⟨hh _ ((Q.edges p).root _ _),ih a₁ a₂ hh⟩
    · intro a ha
      obtain ⟨e₁,a₁⟩ := h₁.2.2.2 a ha
      obtain ⟨e₂,a₂⟩ := h₂.2.2.2 a ha
      rw [← e₁,← e₂]
      have hh := fun j hj => he j (slot_sub ha hj)
      exact ⟨hh _ ((Q.edges p).root _ _),ih a₁ a₂ hh⟩

theorem permute (A : Finset X) (f g : X → I)
    (he : ∀ i ∈ A, ∀ j ∈ A, f i = f j ↔ g i = g j) :
    ∃ e : Equiv.Perm I, ∀ i ∈ A, e (f i) = g i := by
  let S := A.image f
  have ex : ∀ y : ↥S, ∃ i ∈ A, f i = y.val := fun y => Finset.mem_image.mp y.property
  choose rep hr hf using ex
  have inj : Function.Injective (fun y => g (rep y)) := fun x y h =>
    Subtype.ext ((hf x).symm.trans (((he _ (hr x) _ (hr y)).mpr h).trans (hf y)))
  obtain ⟨e,hh⟩ := Equiv.Perm.exists_extending_pair (fun y : ↥S => y.val) _ Subtype.val_injective inj
  refine ⟨e,fun i hi => ?_⟩
  let y : ↥S := ⟨f i,Finset.mem_image_of_mem _ hi⟩
  exact (hh y).trans ((he _ (hr y) _ hi).mp (hf y))

structure Consistent (Q : Network u X) (p : ℕ) (A : Finset X) (f : X → I) (rank : X → ℕ) : Prop where
  layer : ∀ i j, f i = f j → Q.w.layer i = Q.w.layer j
  live : ∀ i j, f i = f j → (Q.w.live i ↔ Q.w.live j)
  height : ∀ i j, f i = f j → rank i = rank j
  next : ∀ i ∈ A, ∀ j ∈ A, f i = f j → ∀ a, f (Q.edges p i a) = f (Q.edges p j a)
  falls : ∀ i ∈ A, ∀ a, Q.edges p i a ≠ i → rank (Q.edges p i a) < rank i

theorem Consistent.realize {A : Finset X} {f : X → I} {rank : X → ℕ} (h : Q.Consistent p A f rank)
    (x : X) : ∃ N : Network u I, ∀ R i, Q.ball p R i ⊆ A → Q.Agree N f p R i := by
  let B := A.image f
  have choose : ∀ b, ∃ i, (b ∈ B → i ∈ A) ∧ (b ∈ Set.range f → f i = b) := by
    intro b
    by_cases hb : b ∈ B
    · obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hb
      exact ⟨i,fun _ => hi,fun _ => he⟩
    by_cases hh : b ∈ Set.range f
    · exact ⟨hh.choose,fun h => (hb h).elim,fun _ => hh.choose_spec⟩
    · exact ⟨x,fun h => (hb h).elim,fun h => (hh h).elim⟩
  choose rep mem eq using choose
  have key : ∀ i, f (rep (f i)) = f i := fun i => eq _ ⟨i,rfl⟩
  have layer := fun i => h.layer _ _ (key i)
  have ht := fun i => h.height _ _ (key i)
  let board : Board I (u.a^u.h) := {
    layer := fun b => Q.w.layer (rep b)
    bound := fun b => Q.w.bound _
    live := fun b => b ∈ B ∧ Q.w.live (rep b)
    step := fun b d => f (Q.w.step (rep b) d)
    west := fun b hb => by rw [layer]; exact Q.w.west _ hb.2
    east := fun b hb => by rw [layer]; exact Q.w.east _ hb.2
    rank := fun b => rank (rep b)
    decrease := by
      intro b hb d; rw [ht]
      have hh := h.falls _ (mem _ hb.1) (.inl d)
      simp only [edges,ite_eq_left hb.2] at hh
      exact hh (fun he => (Q.w.decrease _ hb.2 d).ne (congrArg Q.w.rank he)) }
  let N : Network u I := {
    w := board
    slot := fun a b => if b ∈ B ∧ u.phase a < p then f (Q.slot a (rep b)) else b
    same := fun a b => by split <;> simp [board,layer,Q.same]
    jump := by
      intro a b hn
      split at hn
      · rename_i hh
        have ne : Q.slot a (rep b) ≠ rep b := by
          intro he; apply hn; rw [he,eq b (by obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hh.1; exact ⟨i,hi⟩)]
        have hd := h.falls _ (mem _ hh.1) (.inr a)
        simp only [edges,ite_eq_left hh.2] at hd
        simp only [ite_eq_left hh,board,ht]
        exact ⟨⟨hh.1,(Q.jump _ _ ne).1⟩,hd ne⟩
      · contradiction }
  refine ⟨N,fun R => ?_⟩
  induction R with
  | zero => exact fun _ _ => True.intro
  | succ R ih =>
    intro i hi
    have hm := hi ((Q.edges p).root _ i)
    have hb : f i ∈ B := Finset.mem_image_of_mem _ hm
    have live := h.live _ _ (key i)
    have next := h.next i hm _ (mem _ hb) (key i).symm
    refine ⟨(layer i).symm,by simp [N,board,hb,live],?_,?_⟩
    · intro d hl
      exact ⟨by simpa [N,board,edges,hl,live.mpr hl] using next (.inl d),ih _ ((basic_sub hl d).trans hi)⟩
    · intro a ha
      exact ⟨by simpa [N,edges,hb,ha] using next (.inr a),ih _ ((slot_sub ha).trans hi)⟩

end OAI.Geometry.Hirsch.Layer.Board.Network
