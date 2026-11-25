import OAI.Computability.IntegerMultiplication.Loom.Priority

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Loom
open Strip Dims Code Adic Net Port
variable {I J L W : Type} [DecidableEq J] [Fintype J] [Fintype W]
variable {p : ℕ} {discount : ℝ}

@[simp] theorem field_length (p j : ℕ) : (field p j).length=j := by induction j <;> simp_all [field]
theorem rack_eq (p n j) :
    Rack (field p j) n = field p (n*j) := by
  have eq (a b : ℕ) : field p a ++ field p b = field p (a+b) := by
    induction a with
    | zero => simp [field]
    | succ a ih => rw [field,List.cons_append,ih,Nat.add_right_comm,field]
  induction n with
  | zero => rw [Nat.zero_mul]; rfl
  | succ n ih => rw [Rack,ih,eq,Nat.add_mul,Nat.one_mul,Nat.add_comm j]

-- undye permits flat keys. Use existence so we don't compute any casts.
noncomputable section
omit [DecidableEq J] in
theorem condensed (p k : ℕ) (f : J≃Fin (dim J)) :
    Nonempty (Adopt (threads (line p (dim J^k)) f)
      (line p (dim J^(k+1)))) := by
  rw [pow_succ']
  unfold line
  rw [← rack_eq]
  exact ⟨undye _ f (Adopt.same _)⟩
def condensate (p k : ℕ) (f : J≃Fin (dim J)) :=
  Classical.choice (condensed p k f)

variable (p k : ℕ) (f : J ≃ Fin (dim J)) (P G B : Tape)
def depthAdopt :
    Adopt (arrays f (line p (dim J^k)) P G B)
      (stock p P G B (dim J^(k+1))) :=
  let v := condensate p k f
  (Adopt.same _).split (v.split ((Adopt.same _).split (v.split (Adopt.same _))))
omit [DecidableEq J] in
theorem preserved (a : Keys P G B J (Block p (dim J^k))) :
    (depthAdopt p k f P G B).cast (swapper _ _ _ a) =
      swapper _ _ _ ((depthAdopt p k f P G B).cast a) := rfl

variable {p k P G B}
private theorem allRack (t : Tape) (m a : ℕ) {p} (d : ∀ a∈t,2≤a ∧ a≤p) (e : a∈Rack t m) :
    2≤a ∧ a≤p := by
  induction m with
  | zero => simp [Rack] at e
  | succ m ih => exact (List.mem_append.mp e).elim (fun v => d _ v) ih
theorem ivory {p j : ℕ} (h : 2≤p) : ∀ a∈field p j,2≤a ∧ a≤p := by
  induction j with
  | zero => intro _ e; simp [field] at e
  | succ j ih => intro a e; exact (List.mem_cons.mp e).elim (fun e => by rw [e]; exact ⟨h,le_rfl⟩) (ih _)
variable {f}
-- only cross s.1=false q.1=true
def infant (v : Stair (dim J) p (k+1)) (hq : 2≤p)
    (f : J ≃ Fin (dim J)) (i j : J) : Stair (dim J) p k where
  supplyLimit := v.supplyLimit
  north := preamble f v.north v.isle (field p (dim J^k)) (false,i)
  south := appendix f v.isle v.south (field p (dim J^k)) (true,j)
  isle := silence f v.isle (field p (dim J^k)) (false,i) (true,j)
  tame := by
    simp only [preamble_false,appendix_true,silence_false_true]
    intro a e
    simp only [List.mem_append] at e
    have A (h : a∈v.north ∨ a∈v.isle ∨ a∈v.south) := v.tame a (by simp; tauto)
    have E : ∀ n, a∈Rack (field p (dim J^k)) n → 2≤a ∧ a≤p := fun n => allRack _ n _ (ivory hq)
    rcases e with ((((e|e))|(e|e|e))|e|e)
    · exact A (.inl e)
    · exact E _ e
    · exact E _ e
    · exact A (.inr (.inl e))
    · exact E _ e
    · exact E _ e
    · exact A (.inr (.inr e))
  lock := by
    have e := length_cross f v.north v.isle v.south (field p (dim J^k)) (false,i) (true,j) (.inl ⟨rfl,rfl⟩)
    rw [field_length] at e
    have h := v.lock
    rw [pow_succ, ← Nat.mul_assoc] at h
    exact e.le.trans h

abbrev nextStop (p k : ℕ) (f : J ≃ Fin (dim J)) (i j : J) {P G B : Tape} :=
  twoStops (p:=p) (j:=dim J^k) (P:=P) (G:=G) (B:=B) f (false,i) (true,j) (.inl ⟨rfl,rfl⟩)
def infancy (v : Stair (dim J) p (k+1)) (hq : 2≤p) (f : J ≃ Fin (dim J)) (i j : J) :
    Adopt (arrays f (line p (dim J^k)) v.north v.isle v.south)
      (stock p (infant v hq f i j).north (infant v hq f i j).isle (infant v hq f i j).south (dim J^k)) :=
  (nextStop p k f i j).view

theorem infancyAlter (v : Stair (dim J) p (k+1)) (hq : 2≤p)
    [NeZero p] (f : J≃Fin (dim J)) (i j : J)
    (t : SpanKey (infant v hq f i j).north (infant v hq f i j).isle (infant v hq f i j).south (Block p (dim J^k))) :
    (infancy v hq f i j).cast.symm (swapper _ _ _ t) =
      (reflect f (Lag.pivot i j) (p:=p) trivial v.north v.isle v.south (dim J^k)).symm
        ((infancy v hq f i j).cast.symm t) := by
  let e := nextStop (P:=v.north) (G:=v.isle) (B:=v.south) p k f i j
  change e.view.cast.symm (swapper _ _ _ t) = (e.tune (Equiv.prodComm _ _)).symm (e.view.cast.symm t)
  apply e.view.cast.injective
  change _ = e.view.cast (e.bridge _ _)
  rw [Axis.changed]
  simp [Axis.pair,swapper,Equiv.prodComm]
  have h := Equiv.apply_symm_apply e.view.cast t
  refine (Equiv.apply_symm_apply e.view.cast _).trans ?_
  exact congrArg (fun a : @SpanKey (infant v hq f i j).north
    (infant v hq f i j).isle (infant v hq f i j).south (Block p (dim J^k)) =>
      (a.1, a.2.2.2.1, a.2.2.1, a.2.1, a.2.2.2.2)) h.symm

end
end Loom

end IntegerMultiplication
end Computability
end OAI
