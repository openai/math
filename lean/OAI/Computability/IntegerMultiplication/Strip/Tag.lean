import OAI.Computability.IntegerMultiplication.Strip.Bearing
import OAI.Computability.IntegerMultiplication.Code.Filter

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Strip
open Code Code.Task
variable {I T : Type} {A B : I→Type} {w : I→ℝ} {input : I→Tree}
variable [Codec T] [FiniteState T] [DecidableEq T]
theorem restore {Y : Type} (k : T) (f : I → List (T×Y)) [Codec Y]
    (h : Carries w input (fun i => send (Ribbon.read k (f i))))
    (g : Carries w input (fun i => send ((f i).map Prod.fst))) :
    Carries w input (fun i => send ((f i).map (Ribbon.keep k))) := by
  have l := g.twice h
  simpa [Ribbon.frame] using
    l.chain (Carries.func (y:=fun i => ((f i).map Prod.fst,Ribbon.read k (f i))) g.budget l.out
      (Ribbon.dress k) (Ribbon.easyDress k))

theorem rebuild {Y : Type} (f : I → List (T×Y)) [Codec Y]
    (h : ∀ k, Carries w input (fun i => send (Ribbon.read k (f i))))
    (g : Carries w input (fun i => send ((f i).map Prod.fst))) :
    Carries w input (fun i => send ((f i).map Prod.snd)) := by
  have hh (v : List T) (u : v.Nodup) :
      Carries w input (fun i => send ((f i).map (Ribbon.collect v))) := by
    induction v with
    | nil =>
      have e := g.chain (Carries.func g.budget g.out
        (fun l : List T => l.map fun _ => ([] : List Y))
        (by fun_prop))
      have eq : Ribbon.collect ([]:List T) = fun (_ : T×Y) => [] := by funext; simp [Ribbon.collect]
      simpa [List.map_map,Function.comp_def,eq] using e
    | cons t v ih =>
      rw [List.nodup_cons] at u
      let F i := (f i).map (Ribbon.keep t)
      let Z i := (f i).map (Ribbon.collect v)
      have l := (restore t f (h t) g).twice (ih u.2)
      have e := l.chain (Carries.func (y:=fun i => (F i,Z i))
        g.budget l.out Ribbon.unite (Ribbon.easyUnite easy_id))
      simpa only [F,Z,Ribbon.collecting _ _ _ u.1] using e
  classical
  let : Fintype T := Fintype.ofFinite _
  have hl := hh _ (Finset.nodup_toList (Finset.univ:Finset T))
  have hf := hl.chain (Carries.func g.budget hl.out List.flatten Easy.flatten)
  suffices e : ∀ l : List (T×Y),
      (l.map (Ribbon.collect (Finset.univ:Finset T).toList)).flatten = l.map Prod.snd by
    simpa only [e] using hf
  intro l; induction l <;> simp_all [Ribbon.collect]

variable (s : (i:I)→Series (A i)) (d : (i:I)→Series (B i))
variable (u : (i:I)→A i→Tree) (v : (i:I)→B i→Tree)
variable (key : (i:I)→A i→T) (tag : (i:I)→B i→T)
abbrev blob {P V : Type} (s : Series P) (k : P→T) (v : P→V) :=
  s.tab fun a => (k a,v a)

-- transport by tag match
theorem tagged (h : Carries w input (stackRun s u))
    (i : Carries w input (stackRun s fun x a => send (key x a)))
    (j : Carries w input (stackRun d fun x a => send (tag x a)))
    (agree : ∀ x t,
      Ribbon.read t (blob (s x) (key x) (u x)) = Ribbon.read t (blob (d x) (tag x) (v x))) :
    Carries w input (stackRun d v) := by
  have hs := coalesce s (fun x a => send (key x a)) _ i h
  have lsa (x) : stripe (s x) (together (fun a => send (key x a)) (u x)) =
      send (blob (s x) (key x) (u x)) := stripe_eq' (s x) (fun a => (key x a,u x a))
  have lsb (x) : stripe (d x) (v x) =
      send ((blob (d x) (tag x) (v x)).map Prod.snd) := by
    rw [blob,Series.map_tab,stripe_eq]
    rfl
  unfold stackRun at *
  simp only [lsa] at hs
  simp only [lsb]
  apply rebuild (fun x => blob (d x) (tag x) (v x))
  · intro k; simp_rw [← agree]
    exact hs.chain (Carries.func i.budget hs.out (Ribbon.read k) (Ribbon.easyRead k easy_id))
  simp only [blob,Series.map_tab,Function.comp_def,← stripe_eq']
  exact j
end Strip

end IntegerMultiplication
end Computability
end OAI
