import OAI.Computability.IntegerMultiplication.Net.Labels

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Net.Motif
open Touch Loom Place
namespace Beat
variable {C T : Type} (z : Loom T C) (j : S) (p : Sub T)
def st : Local T C → Place T :=
  repr (fun t => xEntry j.val (fill j p t)) (fun t => .ybox j.val (fill j p t))
    (fun _ _ => .clear) (fun _ => .clear)
def r0 : Local T C → Place T :=
  repr (fun t => xEntry j.val (fill j p t)) (fun t => .ybox j.val (fill j p t))
    (fun x y => if z.near x y then .ybox j.val (fill j p y) else .clear) (fun _ => .clear)
def r1 : Local T C → Place T :=
  repr (fun t => xEntry j.val (fill j p t)) (fun _ => .low j p)
    (fun x y => if z.near x y then .ybox j.val (fill j p y) else .clear) (fun _ => .low j p)
def r2 : Local T C → Place T :=
  repr (fun t => .leanOn j p t) (fun _ => .low j p)
    (fun x y => if z.near x y then .leanOn j p x else .clear) (fun _ => .low j p)
def r3 : Local T C → Place T :=
  repr (fun _ => .high j p) (fun _ => .low j p)
    (fun x y => if z.near x y then .leanOn j p x else .clear) (fun _ => .high j p)
def r4 : Local T C → Place T :=
  repr (fun _ => .high j p) (fun _ => .low j p)
    (fun x y => if z.near x y then .leanOn j p x else .clear) (fun _ => .low j p)
def r5 : Local T C → Place T :=
  repr (fun _ => .high j p) (fun t => .ybox (j.val+1) (fill j p t))
    (fun x y => if z.near x y then .ybox (j.val+1) (fill j p y) else .clear) (fun _ => .low j p)
def r6 : Local T C → Place T :=
  repr (fun _ => .high j p) (fun t => .ybox (j.val+1) (fill j p t))
    (fun x y => if z.near x y then .ybox (j.val+1) (fill j p y) else .clear) (fun _ => .high j p)
def r7 : Local T C → Place T :=
  repr (fun _ => .high j p) (fun t => .ybox (j.val+1) (fill j p t))
    (fun x y => if z.near x y then .high j p else .clear) (fun _ => .high j p)
def climax : Local T C → Place T :=
  repr (fun t => .box (j.val+1) (fill j p t)) (fun t => .ybox (j.val+1) (fill j p t))
    (fun _ _ => .full) (fun _ => .full)

def rhythm (z : Loom T C) (j : S) : List (Sub T → Local T C → Place T) :=
  [r0 z j, r1 z j, r2 z j, r3 z j, r4 z j, r5 z j, r6 z j, r7 z j]
@[simp] theorem rhythm_len : (rhythm z j).length = 8 := rfl

variable [DecidableEq T]
def march (z : Loom T C) (b : Bool) : List (Touch T C) :=
  if b then (z.pairs true).back else (z.pairs false).fwd
@[simp] theorem march_len (b : Bool) : (march z b).length = 8 := by cases b <;> rfl

def plans (z : Loom T C) (j : S) (b : Bool) : Parallel.Job
    (Sub T) (Local T C) (Idler T C j) (Place T) where
  start := st j
  prog := List.zipWith (fun r l => Pad.wrap r l 0) (march z b) (rhythm z j) ++ [Pad.nothing (climax j)]
  idle g := if g.1.val.val < j.val then .full else .clear

theorem plans_ok (b : Bool) (sym : ∀ a b, z.near a b = z.near b a) : (plans z j b).ok := by
  intro p e h
  cases b
  · simp [Parallel.Job.child, plans, march, rhythm, Pairing.fwd] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals try apply Touch.ok
    any_goals
      rintro t (⟨u,v⟩|i) n
      -- weights
      all_goals
        simp [pairs, copy, inj] at n
    -- check
    all_goals try rfl -- repr uniform
    any_goals exact fun w v hn => (hn rfl).elim
    all_goals
      rcases n with ⟨ht,hn⟩
      try replace hn := hn.1
      subst t
      first | simp [repr, r0, r7, r5, r2, role, lx, ly, hn]
  · simp [Parallel.Job.child, plans, march, rhythm, Pairing.back] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals try apply Touch.ok
    any_goals
      rintro t (⟨u,v⟩|i) n
      all_goals
        simp [pairs, copy, inj] at n
    all_goals try rfl
    any_goals exact fun w v hn => (hn rfl).elim
    all_goals
      rcases n with ⟨ht,hn⟩
      try replace hn := hn.1
      subst t
      first | simp [repr, r0, r7, r5, r2, role, lx, ly]
      all_goals simp_all only
-- label history without coefficients
theorem flight (b : Bool) :
    (((plans z j b).child p).ops.map Hop.label) =
      (rhythm z j).map (· p) ++ [climax j p] := by
  cases b <;> rfl
theorem concludes (b : Bool) :
    ((plans z j b).child p).sink = climax j p := by
  cases b <;> rfl

variable {R : Type} [Fintype T] [Fintype C] [Ring R]
theorem stage_moves (h : R) (hz : z.good h) (b : Bool) (w : View T C R) :
    ((plans z j b).child p).logical h w.val =
      if b then ({w with x:= w.x - w.y} : View T C R).val
      else ({w with y:= w.y + w.x} : View T C R).val := by
  unfold Circuit.logical
  change (((List.zipWith .. ++ [Pad.nothing _]).map _).foldl (fun t e => _) _) = _
  rw [Pad.ops_eval (march z b) (rhythm z j) (by simp)]
  cases b
  · simpa only [march, Bool.false_eq_true, ite_false] using congrArg View.val ((z.pairs false).fwd_run h (z.pairs_act h false hz) w)
  simpa only [march, Bool.true_eq, ite_true] using congrArg View.val ((z.pairs true).back_run h (z.pairs_act h true hz) w)

end Beat
end Net.Motif

end IntegerMultiplication
end Computability
end OAI
