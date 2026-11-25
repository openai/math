import OAI.Computability.IntegerMultiplication.Loom.Concert

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Loom
open Net Strip Adic Port Strip.Optic Dims Code
variable {I J W L Z : Type} [Fintype J] [DecidableEq J] [Fintype W] {p : ℕ} [NeZero p]
variable {k : I→ℕ} {j : ℕ}
variable {P G B : Tape}
noncomputable section
-- rotation preparatory and finishing
-- D ↤ D-H. finish D ↤ -D+H.
def upper (close : Bool) (i : J) : List (Lag J p) :=
  (bif close then [Lag.width (true,i) Span.one.opposite,Lag.gather (true,i) (false,i) Pinpoint.unit]
   else [Lag.gather (true,i) (false,i) Pinpoint.unit.opposite])
omit [DecidableEq J] in
theorem upper_clean (c : Bool) (i : J) {p} (f : J ≃ Fin (dim J)) :
    ∀ l∈upper (p:=p) c i,l.legal (ranking f) ∧ l.prices=0 := by
  cases c <;> intro l hl <;> simp [upper] at hl
  · subst l; simp [Lag.legal,Lag.early,Lag.prices]
  rcases hl with rfl | rfl <;> simp [Lag.legal,Lag.prices,Lag.early]
abbrev effect (c : Bool) (v : Duplex J (Tower p j)) (i : J) :=
  bif c then v.1 i-v.2 i else v.2 i-v.1 i
omit [Fintype J] [NeZero p] in
theorem upper_ran (c : Bool) (i : J) (v : Duplex J (Tower p j)) :
    (upper c i).foldl (Lag.fire j) v=(v.1,Function.update v.2 i (effect c v i)) := by
  cases c
  · simp [upper,Lag.fire,place,hear,effect,sub_eq_add_neg]
  simp [upper,Lag.fire,hear,place,effect,sub_eq_add_neg,add_comm]

def initial (c : Bool) (u : List J) : List (Lag J p) := u.flatMap (upper c)
omit [DecidableEq J] in
theorem initial_clean (c : Bool) (l : List J) {p} (f : J ≃ Fin (dim J)) :
    ∀ a ∈ initial (p:=p) c l, a.legal (ranking f) ∧ a.prices=0 := by
  intro a b
  obtain ⟨i,_,e⟩ := List.mem_flatMap.mp b
  exact upper_clean c i f _ e
omit [Fintype J] [NeZero p] in
theorem initial_fuel (c) (l : List J) (s : l.Nodup) (v : Duplex J (Tower p j)) :
    (initial c l).foldl (Lag.fire j) v =
      (v.1,fun i => if i ∈ l then effect c v i else v.2 i) := by
  induction l generalizing v with
  | nil => simp [initial]
  | cons i l ih =>
    simp only [List.nodup_cons] at s
    change (upper c i ++ initial c l).foldl _ _ = _
    rw [List.foldl_append,upper_ran,ih s.2]
    congr 1
    ext o
    by_cases e : o=i
    · subst o; simp [s.1]
    simp [List.mem_cons,e,effect]

variable (f : J ≃ Fin (dim J))
def stages (P G B : Tape) (c : Bool) (p j : ℕ) [NeZero p] :
    Equiv.Perm (Keys P G B J (Block p j)) :=
  let l := (Series.arbitrary J).explore
  recreation f _ _ _ _ (initial c l) (fun a h => (initial_clean c l f a h).1)

theorem endOf (c : Bool) (x : Keys P G B J (Block p j)) :
    square (stages f P G B c p j x) = (((chase x).1,effect c (chase x)),watcher x) := by
  rw [stages,fore,initial_fuel c _ (Series.nodup _) (chase x)]
  simp_rw [Series.complete (Series.arbitrary J),ite_true]

private def flip (P G B : Tape) (J A : Type) : Equiv.Perm (SpanKey P G B (J→A)) :=
  ⟨swapper P G B,swapper P G B,by intro; rfl,by intro; rfl⟩
theorem third :
    ((stages f P G B false p j).trans (tide (1:Matrix J J (Tower p j)) P G B)).trans
      (stages f P G B true p j) = flip P G B J (Block p j) := by
  ext x : 1
  apply square.injective
  have q (c) (x : Keys P G B J (Block p j)) : chase (stages f P G B c p j x) = ((chase x).1,effect c (chase x)) ∧
      watcher (stages f P G B c p j x)=watcher x := Prod.ext_iff.mp (endOf f c x)
  have t (x : Keys P G B J (Block p j)) : chase (tide (1:Matrix J J (Tower p j)) _ _ _ x) =
      ((chase x).1+(chase x).2,(chase x).2) ∧ watcher (tide (1:Matrix J J (Tower p j)) P G B x)=watcher x := by
    have h := Prod.ext_iff.mp (forward (1:Matrix J J (Tower p j)) x)
    simpa only [square,Lens,Equiv.coe_fn_mk,Shuttle.Rank.shear,Matrix.one_mulVec] using h
  change (chase _,watcher _)=(( (chase x).2,(chase x).1),watcher x)
  simp only [Equiv.trans_apply,(q ..).1,(q ..).2,(t ..).1,(t ..).2]
  congr 2 <;> ext i <;> simp [effect,sub_eq_add_neg, add_comm]

variable {r : Regime I} (P : (i:I)→Stair (dim J) p (k i+1)) (l : I→ℕ)
variable (hp : 2≤p) (H : r.Small fun i => (P i).ticket)
variable {A : I→Type} (s : (i:I)→Series (A i))
variable (m : ∀ i,(s i).count≤l i) (v : (i:I)→fieldView P i → A i→Bead)
include m hp H
theorem curtain (c : Bool) :
    Drive r (fun i => (ringArea P f i).count) l (cloth (ringArea P f) s v)
      (cloth (ringArea P f) s (fun i => travel
        (stages f (P i).north (P i).isle (P i).south c p (dim J^k i)) (v i))) := by
  suffices hs : ∀ l' : List (Lag J p),
      (h : ∀ i∈l',i.legal (ranking f)) → (g : ∀ i∈l',i.prices=0) →
      Drive r (fun i=>(ringArea P f i).count) l (cloth (ringArea P f) s v)
        (cloth (ringArea P f) s (fun i => travel (recreation f
          (P i).north (P i).isle (P i).south (dim J^k i) l' h) (v i))) by
    exact hs _ _ (fun a h => (initial_clean c _ f a h).2)
  intro e h g
  have u := priority P f hp H
  induction e generalizing v with
  | nil => exact Drive.self u.1 (cloth_size _ _ u v m)
  | cons a e ih =>
    have v0 := freeRide P f hp H a (h _ List.mem_cons_self) (g _ List.mem_cons_self) _ s l m v
    exact Drive.pipe v0 (ih _ (fun i hi => h _ (List.mem_cons_of_mem _ hi))
        (fun i hi => g _ (List.mem_cons_of_mem _ hi)))
omit hp H m in
theorem corner_value {i : I} (u : Keys (P i).north (P i).isle (P i).south J (Block p (dim J^k i))→Z) :
    travel (stages f (P i).north (P i).isle (P i).south true p _)
      (travel (tide (1:Matrix J J (Tower p _)) (P i).north (P i).isle (P i).south)
        (travel (stages f (P i).north (P i).isle (P i).south false p _) u)) =
      u ∘ (swapper _ _ _) := by rw [succession _ _ u,succession,third f]; rfl
end
end Loom

end IntegerMultiplication
end Computability
end OAI
