import OAI.Computability.BorderVNP.CubeTeamRowDispatch

/-! # Chronological memory and vertex-directory image of the owned row scan -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.TeamRows

open RoutingISA RoutingISA.Owned VPVNP.BurstRAM

/-- The two mutable outputs threaded through the group roles. -/
structure ViewState (w : ℕ) where
  /-- Word address of the next free vertex triple. -/
  out : ℕ
  /-- The entire physical RAM image, including shared views, private stores and declarations. -/
  mem : Memory w

/-- The public symbols corresponding to a native square-table ordinal. -/
def pairAt (d : ℕ) (q : Fin (d*d)) : Fin d × Fin d := finProdFinEquiv.symm q

/-- The successive physical row images in the exact order used by the native loop. -/
def fold {w : ℕ} (l : TeamRowPrepare.Layout) (owner : Fin l.d → ℕ)
    (step : Fin l.d → Fin l.d → ViewState w → ViewState w) (start : ViewState w) :
    ℕ → ViewState w
  | 0 => start
  | q+1 =>
    let before := fold l owner step start q
    if h : q < l.d*l.d then
      let p := pairAt l.d ⟨q,h⟩
      if owner p.1 = l.teamID then step p.1 p.2 before else before
    else before

/-- One in-range row either updates the two outputs by its actual role or
retains them at the next ordinal. -/
theorem fold_succ {w : ℕ} (l : TeamRowPrepare.Layout) (owner : Fin l.d → ℕ)
    (step : Fin l.d → Fin l.d → ViewState w → ViewState w) (start : ViewState w)
    (q : ℕ) (hq : q < l.d*l.d) :
    fold l owner step start (q+1) =
      let p := pairAt l.d ⟨q,hq⟩
      let prev := fold l owner step start q
      if owner p.1 = l.teamID then step p.1 p.2 prev else prev := by
  simp only [fold,hq,dite_true]

/-- At an owned endpoint the role's exact memory transformer is applied once. -/
theorem fold_role {w : ℕ} (l : TeamRowPrepare.Layout) (owner : Fin l.d → ℕ)
    (step : Fin l.d → Fin l.d → ViewState w → ViewState w) (start : ViewState w)
    (q : ℕ) (hq : q < l.d*l.d) (own : owner (pairAt l.d ⟨q,hq⟩).1 = l.teamID) :
    fold l owner step start (q+1) =
      step (pairAt l.d ⟨q,hq⟩).1 (pairAt l.d ⟨q,hq⟩).2 (fold l owner step start q) := by
  rw [fold_succ _ _ _ _ _ hq, ite_eq_left own]

/-- A row whose first group belongs to another team leaves both outputs in place. -/
theorem fold_skip {w : ℕ} (l : TeamRowPrepare.Layout) (owner : Fin l.d → ℕ)
    (step : Fin l.d → Fin l.d → ViewState w → ViewState w) (start : ViewState w)
    (q : ℕ) (hq : q < l.d*l.d) (own : owner (pairAt l.d ⟨q,hq⟩).1 ≠ l.teamID) :
    fold l owner step start (q+1) = fold l owner step start q := by
  rw [fold_succ _ _ _ _ _ hq, ite_eq_right own]

/-- Numeric array lookup on in-range group indices; the default is never read
by the physical iterator. -/
def wordOwner {d : ℕ} (owner : Fin d → ℕ) (i : ℕ) := if h : i < d then owner ⟨i,h⟩ else 0

/-- Instantiate the native scan with the chronological row transformers. Each
owned row supplies its concrete emitted trace and resulting memory and pointer.
The final native state is the full ordered fold, including its unchanged input
words and all earlier row stores. -/
theorem scan_fold {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (strict diagonal : Code) (l : TeamRowPrepare.Layout) (owner : Fin l.d → ℕ)
    (cost : ℕ → ℕ) (bits : ℕ → List Bool) (step : Fin l.d → Fin l.d → ViewState w → ViewState w)
    (s : Bank w) (m : Memory w) (fit : l.Fits w) (hf : readings pub 0 = l.frame)
    (inventory : ∀ q, let z := fold l owner step ⟨readings s 7,m⟩ q
      l.Fields (readings z.mem) ∧ ∀ g : Fin l.d, readings z.mem (l.ownerBase+g.val) = owner g)
    (role : ∀ q : Fin (l.d*l.d), let p := pairAt l.d q
      let prev := fold l owner step ⟨readings s 7,m⟩ q.val
      let next := step p.1 p.2 prev
      owner p.1 = l.teamID → ∀ u : Bank w, readings u 7 = prev.out →
        TeamRowPrepare.ReadyRow l (readings prev.mem) q.val (.ofWords u prev.mem) →
        TraceRun pub mac (if p.1 = p.2 then diagonal else strict) u prev.mem (bits q.val) (cost q.val)
          (fun t mt => readings t 7 = next.out ∧ mt = next.mem ∧
            readings t 22 = q.val ∧ readings t 23 = l.d*l.d)) :
    let last := fold l owner step ⟨readings s 7,m⟩ (l.d*l.d)
    TraceRun pub mac (scan strict diagonal) s m (choices l (wordOwner owner) bits)
      (ticks l (wordOwner owner) cost) (fun t mt =>
        readings t 7 = last.out ∧ mt = last.mem ∧ readings t 22 = l.d*l.d ∧ readings t 23 = l.d*l.d) := by
  let initial : ViewState w := ⟨readings s 7,m⟩
  let I (q : ℕ) (u : Word w) (mu : Memory w) :=
    u.val = (fold l owner step initial q).out ∧ mu = (fold l owner step initial q).mem
  have pubWords (q : ℕ) (u : Word w) (mu : Memory w) (ih : I q u mu) :
      l.Fields (readings mu) ∧ ∀ g < l.d, readings mu (l.ownerBase+g) = wordOwner owner g := by
    rw [ih.2]
    refine ⟨(inventory q).1,fun g hg => ?_⟩
    simpa only [wordOwner,hg,dite_true] using (inventory q).2 ⟨g,hg⟩
  have ownAt (q : ℕ) (hq : q < l.d*l.d) :
      wordOwner owner (q/l.d) = owner (pairAt l.d ⟨q,hq⟩).1 := by
    have hd : q/l.d < l.d := (pairAt l.d ⟨q,hq⟩).1.isLt
    simp only [wordOwner,hd,dite_true]
    rfl
  have skip (q : ℕ) (hq : q < l.d*l.d) (ho : wordOwner owner (q/l.d) ≠ l.teamID)
      (u : Word w) (mu : Memory w) (ih : I q u mu) : I (q+1) u mu := by
    change _ = (fold l owner step initial (q+1)).out ∧ _ = (fold l owner step initial (q+1)).mem
    rw [fold_skip _ _ _ _ _ hq (ownAt q hq ▸ ho)]
    exact ih
  have visit (q : ℕ) (hq : q < l.d*l.d) (ho : wordOwner owner (q/l.d) = l.teamID)
      (u : Bank w) (mu : Memory w) (ih : I q (u 7) mu)
      (ready : TeamRowPrepare.ReadyRow l (readings mu) q (.ofWords u mu)) :
      TraceRun pub mac (if q/l.d = q%l.d then diagonal else strict) u mu (bits q) (cost q) (Next l I q) := by
    let p := pairAt l.d ⟨q,hq⟩
    have owned : owner p.1 = l.teamID := ownAt q hq ▸ ho
    have eqn : (q/l.d = q%l.d) ↔ p.1 = p.2 := by
      change p.1.val = p.2.val ↔ p.1 = p.2
      exact Fin.val_inj
    have hm := ih.2
    subst mu
    have hcode : (if q/l.d = q%l.d then diagonal else strict) =
        (if p.1 = p.2 then diagonal else strict) := by
      by_cases he : p.1 = p.2
      · simp [he,eqn.mpr he]
      · simp [he,eqn.not.mpr he]
    rw [hcode]
    apply (role ⟨q,hq⟩ owned u ih.1 ready).mono le_rfl
    rintro t mt ⟨ptr,mem,cur,bound⟩
    refine ⟨?_,cur,bound⟩
    change _ = (fold l owner step initial (q+1)).out ∧ _ = (fold l owner step initial (q+1)).mem
    rw [fold_role _ _ _ _ _ hq owned]
    exact ⟨ptr,mem⟩
  have run := scan_run pub mac strict diagonal l (wordOwner owner) cost bits I s m fit hf
    ⟨rfl,rfl⟩ pubWords skip visit
  exact run.mono le_rfl fun _ _ h => ⟨h.1.1,h.1.2,h.2⟩

end Cube.TeamRows

end BorderVNP
end Computability
end OAI
