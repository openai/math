import OAI.Computability.IntegerMultiplication.Strip.Aero

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Strip
open Code
variable {I A : Type}
/-- Main case: number of records budget = count of the layout and each record
Tree length ≤ fixed constant * (length+1). Under sublayout and regrouping may use Drive directly. -/
structure Manifest (s : I→Type) (l : I→ℕ) (v : (i:I)→s i→Tree) : Prop where
  size : ∃ C : ℕ, ∀ i a, (v i a).count ≤ C*(l i+1)

abbrev Fleet (r : Regime I) (l : I→ℕ) {S T : I→Type} (s : (i:I)→Series (S i))
    (t : (i:I)→Series (T i)) (v : (i:I)→S i→Tree) (u : (i:I)→T i→Tree) :=
  Drive r (fun i => (s i).count) l (stackRun s v) (stackRun t u)

namespace Manifest
variable {r : Regime I} {l : I→ℕ} {S G : I→Type} {s : (i:I)→Series (S i)}
variable {v : (i:I)→S i→Tree}
theorem lives (h : Manifest S l v) (hs : Station r s) :
    Alive r (fun i => (s i).count) l (stackRun s v) := by
  obtain ⟨C,e⟩ := h.size
  exact aliveData hs v C e (fun _ => le_rfl)

theorem localize {s : (i:I)→G i→S i→Tree}
    (h : Manifest (fun i => G i × S i) l (fun i z => s i z.1 z.2)) :
    Manifest (fun x : Sigma G => S x.1) (fun x => l x.1) fun x a => s x.1 x.2 a := by
  obtain ⟨C,e⟩ := h.size
  exact ⟨C,fun x a => e _ (x.2,a)⟩
theorem shift {G} (h : Manifest S l v) (e : (x : I) → G x → S x) :
    Manifest G l fun x a => v x (e x a) :=
  let ⟨C,g⟩ := h.size
  ⟨C,fun x _a => g x _⟩ -- let elimination Exists ok Prop

end Manifest
namespace Fleet
variable {S B C : I→Type} {r : Regime I} {l : I→ℕ}
variable {s : (i:I)→Series (S i)} {b : (i:I)→Series (B i)} {c : (i:I)→Series (C i)}
abbrev cartS (s : (i:I)→Series (S i)) (b : (i:I)→Series (B i)) :=
  fun i => (s i).cart (b i)
theorem keep {v} (h : Manifest _ l v) (u : Station r s) :
    Fleet r l s s v v := Drive.self u.1 (h.lives u)
theorem chain {v u w} (h : Fleet r l s b v u)
    (e : Fleet r l b c u w) (q : ∀ i,(b i).count=(s i).count) :
    Fleet r l s c v w :=
  Drive.pipe h (Rip.monoSize e (fun i => (q i).le) (fun _ => le_rfl))

-- lift through any prefix (fewer copies than h*l)
theorem wind (hs : Station r s) (hb : Station r b)
    {v : (i:I)→S i × B i→Tree} {u : (i:I)→S i × C i→Tree}
    (hw : Manifest _ l v)
    (act : Fleet (r.pull (Sigma.fst : Sigma S → I)) (fun x => l x.1) (fun x => b x.1)
        (fun x => c x.1) (fun x a => v x.1 (x.2,a)) (fun x a => u x.1 (x.2,a))) :
    Fleet r l (cartS s b) (cartS s c) v u :=
  Drive.air hs hb (by simp [cartS]) v u (keep hw (hs.product hb)) act

-- lift with per-prefix signal
theorem guide (hs : Station r s) (hb : Station r b)
    {v : (i:I)→S i × B i→Tree} {u : (i:I)→S i × C i→Tree}
    (hw : Manifest _ l v)
    (sig : (i:I)→S i→Tree) (e : Dom (fun x:Sigma S => r.scale x.1) (fun x => (sig x.1 x.2).count))
    (g : Rip r (fun i => (s i).count) l r.header (stackRun s sig))
    (act : Fleet (onboard r sig e) (fun x:Sigma S => l x.1) (fun x => b x.1) (fun x => c x.1)
        (fun x a => v x.1 (x.2,a)) (fun x a => u x.1 (x.2,a))) :
    Fleet r l (cartS s b) (cartS s c) v u := by
  apply Drive.buses hs hb (by simp ) sig e _ v u (keep hw (hs.product hb)) act
  exact g.monoSize (fun i => by exact (Series.count_cart (s i) (b i)) ▸ Nat.le_mul_of_pos_right _ (hb.1 i)) (fun _ => le_rfl)
end Fleet
end Strip

end IntegerMultiplication
end Computability
end OAI
