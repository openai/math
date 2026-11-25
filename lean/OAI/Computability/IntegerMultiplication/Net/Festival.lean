import OAI.Computability.IntegerMultiplication.Net.Account

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Net.Motif
open Finset Circuit
namespace Carnival
variable {T C : Type} (z : Loom T C) [DecidableEq T]
open Place Beat Parallel
def boundary (n : ℕ) : Bank T C → Place T
| .inl t => xEntry n t
| .inr (.inl t) => .ybox n t
| .inr (.inr (k,_,_)) => if k.val < n then .full else .clear

def stage (j : S) (b : Bool) : Circuit (Bank T C) (Place T) :=
  (plans z j b).weave (parcel j)

theorem enter (j : S) (b : Bool) : (stage z j b).init =
    boundary j.val := by
  funext w
  rcases w with x|y|⟨k,p,a⟩
  · simp [stage, Job.weave, plans, join, st, splitBank, boundary, repr, lx]
  · simp [stage, Job.weave, plans, join, st, splitBank, boundary, repr, ly]
  by_cases e : k=j
  · subst k; cases a with
    | inl uv => cases uv; simp [stage, Job.weave, plans, st, repr, splitBank, boundary, aux]
    | inr r => simp [stage, Job.weave, plans, st, repr, splitBank, boundary, aux]
  simp [stage, Job.weave, plans, splitBank, boundary, e]

theorem leave (j : S) (b : Bool) : (stage z j b).sink =
    boundary (j.val+1) := by
  unfold stage; rw [Job.sink_weave]
  simp_rw [concludes]
  funext w
  rcases w with x|y|⟨k,p,a⟩
  · simp [plans, splitBank, boundary, climax, repr, lx, xEntry]
  · simp [plans, splitBank, boundary, climax, repr, ly]
  by_cases e : k=j
  · subst k; cases a with
    | inl uv => cases uv; simp [plans, splitBank, boundary, climax, repr, aux]
    | inr r => simp [plans, splitBank, boundary, climax, repr, aux]
  have hf : k.val < j.val + 1 ↔ k.val < j.val := by
    have : k.val ≠ j.val := fun x => e (Fin.ext x)
    omega
  simp [plans, splitBank, boundary, e, hf]

theorem stage_ok (j : S) (b : Bool) (sym : ∀ a b, z.near a b = z.near b a) : (stage z j b).ok :=
  (plans z j b).weave_ok _ (plans_ok z j b sym)
theorem stage_smooth (j : S) (b : Bool) :
    (stage z j b).smooth (road (fun x y => z.near x y)) := weave_smooth _ _ _
      (fun p => Beat.simple z j p b) (fun _ => road.still _)

def tribute (h : ℤ) (j : S) : Bank T C → ℤ
| .inl _ => if j.val=0 then 1 else 0
| .inr (.inl _) => 0
| .inr (.inr (_k,_,.inl _)) => 0
| .inr (.inr (k,_,.inr _)) => if k=j then 2*h else 0

theorem stage_cost (j : S) (b : Bool) (h : ℤ) (hh : 2 ≤ h) (w : Bank T C) :
    (stage z j b).cost (fun _ => allowance h) w =
      charge h (boundary (j.val+1) w) - charge h (boundary j.val w) +
        tribute h j w := by
  rw [stage, Job.cost_weave _ _ _ (stay_allowance _)]
  simp_rw [Function.comp_apply]
  rcases w with x|y|⟨k,p,a⟩
  · simp [splitBank, join, Beat.detailed z j _ _ h hh, stageBill, st, climax,
      repr, lx, boundary, tribute, xEntry]
  · simp [splitBank, join, Beat.detailed z j _ _ h hh, stageBill, st, climax,
      repr, ly, boundary, tribute]
  by_cases e : k=j
  · subst k; rcases a with ⟨x,y⟩|_ <;>
      simp [splitBank, join, Beat.detailed z j _ _ h hh, stageBill, st, climax,
        repr, aux, boundary, tribute]
  have hf : k.val < j.val + 1 ↔ k.val < j.val := by
    have : k.val ≠ j.val := fun x => e (Fin.ext x)
    omega
  cases a <;> simp [splitBank, join, boundary, tribute, e, hf]

variable [Fintype T] [Fintype C] {R : Type} [Ring R]

def update (b : Bool) (w : Bank T C → R) : Bank T C → R
| .inl t => if b then w (xW t) - w (yW t) else w (xW t)
| .inr (.inl t) => if b then w (yW t) else w (yW t) + w (xW t)
| .inr (.inr r) => w (.inr (.inr r))

theorem stage_run (j : S) (b : Bool) (h : R) (hz : z.good h) (w : Bank T C → R) :
    (stage z j b).logical h w = update b w := by
  rw [stage, Pad.job_run]
  simp_rw [Beat.stage_moves z _ _ h hz]
  funext a
  rcases a with a|a|⟨k,p,s⟩
  · cases b <;> simp [splitBank, Pad.actSeq, View.load, update, lx, mixBank, View.val, xW, yW]
  · cases b <;> simp [splitBank, Pad.actSeq, View.load, update, mixBank, View.val, ly, xW, yW]
  by_cases e : k=j
  · subst k
    cases b <;> simp [splitBank, Pad.actSeq, View.load, update, mixBank, View.val, aux, qW]
  simp [splitBank, Pad.sleepSeq, e, update, mixBank, qW]

/-- fixed circuit -/
def net : Circuit (Bank T C) (Place T) :=
  ((stage z 0 false).con (stage z 1 true)).con (stage z 2 false)
omit [Fintype T] [Fintype C] in
theorem bridge0 : (stage z 0 false).sink = (stage z 1 true).init :=
  (leave z 0 _).trans (enter z 1 _).symm
omit [Fintype T] [Fintype C] in
theorem bridge1 : ((stage z 0 false).con (stage z 1 true)).sink = (stage z 2 false).init :=
  (con_sink _ _ (bridge0 z)).trans ((leave z 1 _).trans (enter z 2 _).symm)

omit [Fintype T] [Fintype C] in
theorem init_net : (net z).init = boundary 0 := enter z 0 _
omit [Fintype T] [Fintype C] in
theorem sink_net : (net z).sink = boundary 3 :=
  (con_sink _ _ (bridge1 z)).trans (leave z 2 _)
omit [Fintype T] [Fintype C] in
theorem ok_net (sym : ∀ a b, z.near a b = z.near b a) : (net z).ok :=
  con_ok _ _ (con_ok _ _ (stage_ok _ _ _ sym) (stage_ok _ _ _ sym)) (stage_ok _ _ _ sym)
omit [Fintype T] [Fintype C] in
theorem smooth_net :
    (net z).smooth (road (fun a b => z.near a b)) :=
  con_smooth _ _ (bridge1 z) _ (con_smooth _ _ (bridge0 z) _ (stage_smooth z _ _)
    (stage_smooth z _ _)) (stage_smooth z _ _)

def perm : Bank T C → Bank T C
| .inl t => yW t
| .inr (.inl t) => xW t
| .inr (.inr r) => .inr (.inr r)
omit [DecidableEq T] [Fintype T] [Fintype C] in
theorem involutive : Function.Involutive (perm (T:=T) (C:=C)) := by rintro (_|_|_); all_goals rfl
def route := Equiv.mk (perm (T:=T) (C:=C)) perm involutive involutive
def sign : Bank T C → R
| .inr (.inl _) => -1
| _ => 1
theorem run_net (h : R) (hz : z.good h) (w : Bank T C → R) (u : Bank T C) :
    (net z).logical h w (route u) = sign u * w u := by
  change (net z).logical h w (perm u) = sign u * w u
  unfold net
  simp_rw [con_logical, stage_run z _ _ h hz]
  rcases u with x|y|_
  all_goals simp [perm, update, sign, xW, yW]

omit [Fintype T] [Fintype C] in
theorem cost_net (h : ℤ) (hh : 2 ≤ h) (w : Bank T C) :
    (net z).cost (fun _ => allowance h) w =
    charge h ((net z).sink w) - charge h ((net z).init w) +
      (tribute h 0 w + tribute h 1 w + tribute h 2 w) := by
  rw [init_net, sink_net, net, con_cost _ _ _ (bridge1 z), con_cost _ _ _ (bridge0 z),
    stage_cost _ _ _ _ hh, stage_cost _ _ _ _ hh, stage_cost _ _ _ _ hh]
  -- numeric fin
  change (charge h (boundary 1 w) - charge h (boundary 0 w) + _ + (charge h (boundary 2 w) - charge h (boundary 1 w) + _) +
    (charge h (boundary 3 w) - charge h (boundary 2 w) + _)) = _
  abel

end Carnival
end Net.Motif

end IntegerMultiplication
end Computability
end OAI
