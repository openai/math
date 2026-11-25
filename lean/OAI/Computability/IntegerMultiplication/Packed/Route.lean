import OAI.Computability.IntegerMultiplication.Packed.Tower

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Packed
open Strip Code Loom Adic Port Dims Strip.Optic
noncomputable section
variable {X : Type} (P G R S : X→Tape) (H L i : X→ℕ) {r : Regime X}
variable (hP : Told r P) (hG : Told r G) (hR : Told r R) (hS : Told r S)
variable (h : r.Has fun x=>signs (H x) (L x) (i x)) (c : r.Has (tally ∘ extent H L i))
variable (guard : ∀ x a,a∈P x++G x++R x++S x→a≤Net.Shuttle.base)
variable {l : X→ℕ}
abbrev Reorder (_E : ∀x:X,Equiv.Perm (Plate (H x) (L x) (i x))) (p) :=
  let _I := Series0 P G R S H L i
  -- remove
  fun x : ℕ => x+p
variable {U : X → Type} (u : (x:X)→Series (U x)) (z : ∀ x,(u x).count≤l x)
abbrev Payload := fun (x:X) => U x → Bead
abbrev Action (E : ∀x:X,Equiv.Perm (Plate (H x) (L x) (i x))) :=
  ∀ (f : (x:X) → Addr P G R S H L i x→U x→Bead),
    Sail (l:=l) P G R S H L i (r:=r) (cloth (Series0 P G R S H L i) u f)
      (cloth (Series0 P G R S H L i) u (fun x=> travel (invoke (E x) ..) (f x)))
include hP hG hR hS c z
private theorem follow (q : Equiv.Perm Pos) :
    Action P G R S H L i (r:=r) (l:=l) u (fun _ => agent q (Equiv.refl _)) := by
  intro v
  let s := port P G R S H L i hP hG hR hS c
  have us := Spindle.belly (extent H L i) Net.Motif.sigma_range.1.le
  simp_rw [agent_id]
  exact Breeze.launch (Drive.self s.1 (cloth_size _ u s v z)) us

private theorem job_pipe {m n} (a : Action P G R S H L i (r:=r) (l:=l) u m)
    (b : Action P G R S H L i (r:=r) (l:=l) u n) :
    Action P G R S H L i (r:=r) (l:=l) u (fun x=> (m x).trans (n x)) :=
  fun f =>
    let s := port P G R S H L i hP hG hR hS c
    have h := a f
    have g := b (fun x=>travel (invoke (m x) ..) (f x))
    Spindle.Breeze.pipe h g (Drive.fetch s.1 (cloth_size _ u s f z))

include h
private theorem second (t : Turn) (ht : t∈order)
    (q : Pos ≃ Pos) (doneR : q (target t)=.moon) :
    Action P G R S H L i (r:=r) (l:=l) u (fun _ => agent q (walk t)) := by
  have tR : t.shift=1 ∨ t.shift=-1 := by
    simp only [order,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with kk|kk|kk|kk|kk|kk|kk|kk <;> subst t <;> decide
  intro v
  have hx := straight P G R S H L i hP hG hR hS c h _ (visible u v z)
    q t tR doneR
  exact Breeze.launch hx (Spindle.belly (extent H L i) Net.Motif.sigma_range.1.le)

include guard
private theorem weather (t : Turn) (ht : t∈order) (q : Pos≃Pos) :
    Action P G R S H L i (r:=r) (l:=l) u (fun _ => agent q (walk t)) := by
  by_cases e : q (target t)=.moon
  · exact second P G R S H L i hP hG hR hS h c u z t ht q e
  let E := Equiv.swap (q (target t)) Pos.moon
  have e0 : (q.trans E) (target t)=.moon := by simp [E]
  have hx := second P G R S H L i hP hG hR hS h c u z t ht (q.trans E) e0
  have w : Action P G R S H L i (r:=r) (l:=l) u (fun x => arrange E) := fun v =>
    exchange P G R S H L i hP hG hR hS guard c u z v (q (target t)) e
  have k := job_pipe P G R S H L i hP hG hR hS c u z (job_pipe P G R S H L i hP hG hR hS c u z w hx) w
  have d (x:X) :
      ((arrange E).trans (agent (q.trans E) (walk (H:=H x) (L:=L x) (i:=i x) t))).trans (arrange E)=agent q (walk t) :=
    conjugate q E _
  simpa only [d] using k

theorem touring (q : Pos≃Pos) :
    Action P G R S H L i (r:=r) (l:=l) u (fun _x=> agent q (cruise order)) := by
  suffices hz : ∀ t : List Turn,(∀ v∈t,v∈order) → Action P G R S H L i (r:=r) (l:=l) u (fun x=> agent q (cruise t)) from hz _ (fun _=>id)
  intro t e
  induction t with
  | nil => exact follow P G R S H L i hP hG hR hS c u z q
  | cons a t ih =>
    have g := job_pipe P G R S H L i hP hG hR hS c u z
      (weather P G R S H L i hP hG hR hS h c guard u z a (e _ List.mem_cons_self) q)
      (ih (fun x m=>e _ (List.mem_cons_of_mem _ m)))
    simpa only [agent_con,cruise] using g
end
end Packed

end IntegerMultiplication
end Computability
end OAI
