import OAI.Computability.IntegerMultiplication.Port.Lag

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Port.Lag
open Finset
variable {p : ℕ} {J : Type} [DecidableEq J]
noncomputable section
abbrev H (i:J) : Spot J := (false,i)
abbrev D (i:J) : Spot J := (true,i)
def repeatA (t : J) (c : List J) (b : J → Pinpoint p) : List (Lag J p) :=
  c.map fun k => gather (D t) (D k) (b k)
theorem active (t) (c : List J) (r : t∉c) (b : J→Pinpoint p) (j) (x : Duplex J (Tower p j)) :
    (repeatA t c b).foldl (fire j) x =
      (x.1, Function.update x.2 t (x.2 t + (c.map (fun k => (b k).stamp j*x.2 k)).sum)) := by
  apply hear_all
  intro s
  suffices ∀ a : Spot J, hear ((repeatA t c b).foldl (fire j) x) a =
      if a=D t then x.2 t+(c.map fun k => (b k).stamp j*x.2 k).sum else hear x a by
    rw [this]; rcases s with ⟨_|_,k⟩
    · simp [D,hear]
    by_cases e : k=t <;> simp [D,hear,e]
  clear s
  induction c generalizing x with
  | nil =>
    intro a
    split_ifs with h
    · subst a; simp [repeatA,hear,D]
    rfl
  | cons k c ih =>
    intro a
    simp only [List.mem_cons,not_or] at r
    rw [repeatA,List.map_cons,List.foldl_cons]
    specialize ih r.2 (fire j x (gather (D t) (D k) (b k))) a
    rw [repeatA] at ih
    rw [ih]
    by_cases e : a=D t
    · subst a
      simp only [ite_true,List.map_cons,List.sum_cons,fire,place,hear,D]
      simp only [Function.update_self]
      have g : List.map (fun i => (b i).stamp j*(Function.update x.2 t (x.2 t+(b k).stamp j*x.2 k)) i) c =
          List.map (fun i => (b i).stamp j*x.2 i) c := List.map_inj_left.mpr (fun i hi => by
            simp [Function.update_of_ne (show i ≠ t from fun eq => r.2 (eq ▸ hi))])
      simp [g,add_assoc]
    rw [ite_eq_right e,fire,placed,ite_eq_right e,ite_eq_right e]

def wave (t : J) (c : List J) (b : J → Pinpoint p) : List (Lag J p) :=
  c.map fun k => gather (H k) (H t) (b k)
theorem progress (t : J) (c : List J) (r : t∉c) (n : c.Nodup) (b : J → Pinpoint p)
    (j) (x : Duplex J (Tower p j)) :
    (wave t c b).foldl (fire j) x =
      ((fun k => x.1 k + if k∈c then (b k).stamp j*x.1 t else 0), x.2) := by
  induction c generalizing x with
  | nil =>
    apply Prod.ext
    · ext; simp [wave]
    rfl
  | cons k c ih =>
    simp only [List.nodup_cons] at n
    simp only [List.mem_cons,not_or] at r
    rw [wave,List.map_cons,List.foldl_cons, ← wave, ih r.2 n.2]
    refine Prod.ext ?_ rfl
    funext i
    by_cases e : i=k
    · subst k; simp [fire,place,hear,n.1]
    simp [fire,place,hear,e, r.1]

/-- actual middle shear with one pivot. -/
def peak (h t : J) (a : Span p) : List (Lag J p) :=
  [width (D t) a,
   gather (D t) (H h) Pinpoint.unit,
   pivot h t,
   width (D t) a.reciprocal.opposite,
   gather (D t) (H h) (some a.reciprocal)]
theorem middle (h t) (a : Span p) (j) (x : Duplex J (Tower p j)) :
    (peak h t a).foldl (fire j) x =
      (Function.update x.1 h (x.1 h + a.land j * x.2 t), x.2) := by
  apply Prod.ext
  · funext i
    by_cases hv : i=h
    · rw [hv]
      simp [peak,fire,place,hear,H,D, Pinpoint.unit,Pinpoint.stamp,add_comm]
    simp [peak,fire,place,hear,H,D,hv]
  funext i
  by_cases hv : i=t
  · rw [hv]
    simp [peak,fire,place,hear,H,D,Pinpoint.unit,Pinpoint.stamp]
    have hh := a.land_rec (j:=j)
    linear_combination (x.2 t) * hh
  simp [peak,fire,place,hear,H,D,hv]

omit [DecidableEq J] in
theorem peakLegal (rank : J→ℕ) (i t) (a : Span p) :
    ∀ x∈peak i t a,x.legal rank := by simp [peak,legal,early,D,H]

end
end Port.Lag

end IntegerMultiplication
end Computability
end OAI
