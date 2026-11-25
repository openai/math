import OAI.Computability.IntegerMultiplication.Strip.Room
import OAI.Computability.IntegerMultiplication.Code.Loop

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Strip
open Code Code.Task
/-- Regime: designated descriptor channel, from which all polynomial work on ghost
information used on tape must be computable. Scale function and k remain arbitrary. -/
structure Regime (X : Type*) where
  scale : X → ℕ
  header : X → Tree
  gauge : Dom scale (fun i => (header i).count)

namespace Regime
variable {X Y Z : Type*} (r : Regime X)

def Small (a : X → Tree) := Code.Task.BT r.scale r.header a
/-- communicate small types from header -/
def Has [Codec Y] (g : X → Y) := r.Small (send ∘ g)

variable {r}
theorem Small.extent {k : X → Tree} (h : r.Small k) : Dom r.scale (fun i => (k i).count) := Task.BT.length h r.gauge

theorem self : r.Small r.header := (⟨_,Dom.base _,Task.self⟩ : Task.BT _ _ _)

theorem Small.chain {k f : X → Tree} (h : r.Small k) (g : Task.BT r.scale k f) : r.Small f :=
  Task.BT.compose h g

theorem Small.pair {k f : X → Tree} (h : r.Small k) (v : r.Small f) :
    r.Small (together k f) := by
  have c : r.Small (together r.header r.header) := ⟨_,r.gauge,Task.copy _⟩
  obtain ⟨b,d,hd⟩ := h
  obtain ⟨a,i,hi⟩ := v
  apply c.chain (Code.Task.BT.compose (s:=together k f) (u:=together k r.header) _ _)
  · exact ⟨_,d, hd.left _⟩
  · exact ⟨_, (Task.BT.length (⟨_,d,hd⟩ : r.Small k) r.gauge).add i, hi.right _⟩

theorem Small.yes {k : X → Tree} (h : r.Small k) [Codec Y] {v : X → Y}
    (g : ∃ f : Tree→Y, Poly f ∧ ∀ x, f (k x)=v x) :
    r.Has v := by
  obtain ⟨f,a,d⟩ := g
  have z := a.on (q:=k) (p:=r.scale) (by simpa [size,show send (X:=Tree)=id from rfl] using h.extent)
  apply h.chain
  simpa only [Function.comp_def,d,show send (X:=Tree)=id from rfl,id_eq] using z

theorem Has.pair [Codec Y] [Codec Z] {g : X → Y} {f : X → Z} (h : r.Has g) (v : r.Has f) :
    r.Has (fun x => (g x,f x)) := Small.pair h v
theorem Has.thenDo [Codec Y] [Codec Z] {g : X → Y} (h : r.Has g) {f : Y → Z} (a : Poly f) :
    r.Has (fun x => f (g x)) :=
  Small.chain h (a.on (Small.extent h))

theorem Has.ez [Codec Y] [Codec Z] {g : X → Y} (h : r.Has g) {f : Y → Z} (a : Easy f) :
    r.Has (fun x => f (g x)) := Has.thenDo h a.poly
theorem fixed [Codec Y] (v : Y) : r.Has (fun _ => v) :=
  self.yes ⟨fun _ => v, IntegerMultiplication.Code.Poly.const v, fun _ => rfl⟩

-- Can run all polynomial allowances under a "wide" regime where arbitrary powers
-- absorbed by the given budget. Often holds asymptotically due suffix. Else use
-- fat allowance
def ripe (w : X→ℝ) :=
  (∀x,1≤w x) ∧ ∀ n : ℕ, ∃ C : ℕ, ∀ i, ((r.scale i+1:ℕ)^n:ℕ) ≤ (C:ℝ)*w i
theorem Small.cooked {w : X→ℝ} (e : ripe (r:=r) w) {a} (h : r.Small a) :
    Carries w r.header a := by
  obtain ⟨b,⟨k,C,u⟩,ht⟩ := h
  obtain ⟨m,N,g⟩ := r.gauge
  obtain ⟨D,d⟩ := e.2 k
  obtain ⟨V,v⟩ := e.2 m
  refine ⟨⟨e.1,b,ht,C*D+1,fun i => ?_⟩, N*V,fun i => ?_⟩
  · calc
     _ ≤ ((C*(r.scale i+1)^k:ℕ):ℝ)+1 := by exact_mod_cast Nat.add_le_add_right (u i) _
     _ ≤ _ := by specialize d i; push_cast at d ⊢; have hh := mul_le_mul_of_nonneg_left d (Nat.cast_nonneg (α:=ℝ) C); linarith [e.1 i]
  calc
   _ ≤ ((N*(r.scale i+1)^m:ℕ):ℝ) := by exact_mod_cast g i
   _ ≤ _ := by specialize v i; push_cast at v ⊢; rw [mul_assoc]; gcongr

end Regime
end Strip

end IntegerMultiplication
end Computability
end OAI
