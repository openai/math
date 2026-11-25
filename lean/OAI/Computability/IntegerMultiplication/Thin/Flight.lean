import OAI.Computability.IntegerMultiplication.Thin.Edge
import OAI.Computability.IntegerMultiplication.Strip.Pacing
import OAI.Computability.IntegerMultiplication.Code.Iter

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Thin
open Code Strip Dims Adic Packed Net Net.Walsh Earth Loom
noncomputable section
variable {I : Type} {r : Regime I}
variable (k w n : I→ℕ)
abbrev Sig (k : ℕ) := Fin k×Fin k
abbrev Plane (i:I) := Fin (n i)→Sig (k i)
abbrev Card := Tally × Tally
def screen {i j : ℕ} (p : Fin i→Sig j) : List Card :=
  List.ofFn (fun k=> (tally (p k).1.val,tally (p k).2.val))

variable (p : (i:I)→Plane k n i)
variable (Hp : r.Has fun i=> screen (p i))
variable (Hk : r.Has (tally ∘ k)) (Hn : r.Has (tally ∘ n))
variable (gain : ∀ i x,(p i x).1 < (p i x).2)
-- record budget K bound length cert
variable (K:ℕ)
structure Wrapped (i:I) where
  x : Byte (k i)→ Code.Tree
  ok : ∀ a,(x a).count≤K*(w i+1)
abbrev ship (i:I) (x : Wrapped k w K i) := stripe (line 2 (k i)) x.x
def gangway (i:I) (x:Fin (n i)) (z:Wrapped k w K i) : Wrapped k w K i :=
  ⟨z.x ∘ choke (p i x).1 (p i x).2,fun _j=> z.ok _⟩
abbrev rolls (i:I) := 2^k i*(w i+1)

abbrev Flights := Dial.Hi n (Wrapped k w K)
include p Hp Hn Hk gain

private theorem H1 :
    Dial.HiLib n (fun _=>1) (ship k w K) (gangway k w n p K) Hn (M:=single) (L:=rolls k w) := by
  let Q := Flights k w n K -- maybe order k w K n
  let i0 (i:Q) := i.val.whereNow
  let rr := Dial.stepR (B:=Wrapped k w K) n Hn
  let j (i : Q) := Dial.focus n i
  have small_ {A} [Codec A] (v : I→A) (c : r.Has v) : rr.Has (v ∘ i0) :=
    Task.BT.map (Dial.small n Hn (send ∘ v) c) (fun x:Q=> x.val)
  let o (i:Q) := i.val.tick
  have t : rr.Has (tally ∘ o) := Task.BT.map (Dial.tick_ n Hn) (fun x:Q=>x.val)
  have d : rr.Has (fun i=> tally (j i).val) := by
    have χ := t.ez (show Easy (fun i:Tally=> (cutLists ([()],i)).2) from
      (easy_cut ((Easy.const [()]).pair easy_id)).sndCompose)
    have y (i:Q) : (cutLists ([()],(tally ∘ o) i)).2=tally (j i).val := by simp [cutLists,j,Dial.focus,tally,o]
    simp_rw [← y]; exact χ
  let α i := (p (i0 i) (j i)).1; let β i := (p (i0 i) (j i)).2
  let L i := k (i0 i); let V i := w (i0 i); let N i := rolls k w (i0 i)
  have Y : ∀i,2^L i≤N i := by
    intro i; apply Nat.le_mul_of_pos_right; omega -- N reducible?
  have T := ((small_ _ Hp).pair d).ez (Code.Iter.facile ([],[]))
  have σ : rr.Has fun i=> (tally (α i).val,tally (β i).val) := by
    simpa only [Function.comp_def,screen,Code.Iter.entry] using T
  let A (i:Q) := i.val.value
  let h (i:Q) := (A i).x
  have y : Live rr N (stackRun (fun i=>line 2 (L i)) h) :=
    surveyed (fun i=>line 2 (L i)) h K V
      (fun i=> by rw [Series.total,show Fintype.card _ = _ from Adic.count (p:=2) (l:=L i)])
      (fun i=> (A i).ok)
  have u := motion L α β (fun i=> gain _ _) Y (Drive.fetch (fun _=> Nat.le_refl 1) y)
    (σ.ez Easy.fst) (σ.ez Easy.snd) (small_ _ Hk) h (Drive.self (fun _=> Nat.le_refl 1) y)
  exact Breeze.launch u (fun _=> le_rfl)

theorem rotation :
    let i0 := (fun i:Dial.States (Wrapped k w K)=> i.1)
    Breeze ((fun i:I=> (n i:ℝ)+1) ∘ i0) (r.pull i0) (single ∘ i0) (rolls k w ∘ i0)
      (together (r.header ∘ i0) (fun i=> ship k w K i.1 i.2))
      (fun i=> ship k w K i.1 (Dial.iter n (gangway k w n p K) (Dial.start n i))) := by
  refine (Dial.cyclone n (fun (_:I)=>1) Hn (ship k w K) (gangway k w n p K) (fun (_:I)=>Nat.le_refl 1)
    (fun _=>le_rfl) ?_ (H1 k w n p Hp Hk Hn gain K)).raise (fun i=> ?_)
  · let h (i : Sigma (Wrapped k w K)) := i.2.x
    let L := fun (i:Sigma (Wrapped k w K))=> k i.1
    exact surveyed (fun i=>line 2 (L i)) h K (fun i=>w i.1)
      (fun i=> by rw [Series.total,show Fintype.card _=_ from Adic.count (p:=2) (l:=L i)]; exact le_rfl)
      (fun i=> i.2.ok)
  dsimp only [Function.comp_apply]; rw [one_mul]

-- perm visited = compose all generators in schedule ascending order as action on bits
def low {n L} (p:Fin n→ Sig L) :
    (x:ℕ)→ x≤n → Equiv.Perm (Fin L)
| 0,_=>Equiv.refl _
| s+1,h=>
  let a := p ⟨s,h⟩
  (Equiv.swap a.1 a.2).trans (low p s (by omega))

-- order: image perm after (s+1) schedule: accum where applying bit u swap s then s-1. x composed choke s ∘ choke s-1. vector evaluation precomp swap(s-1) ∘ swap(s) i.e. high applied to indices -> our low=s.trans lower. yes

omit p Hp Hk Hn gain
def lever {k:ℕ} (u:Equiv.Perm (Fin k)) (x:Byte k) : Byte k :=
  (layBit k).symm ((layBit k x) ∘ u)
@[simp] theorem lever_same {k} (x:Byte k) :
    lever (Equiv.refl _) x=x := Equiv.symm_apply_apply (layBit k) x
theorem lever_trans {k} (u v:Equiv.Perm (Fin k)) (x:Byte k) :
    lever u (lever v x)=lever (u.trans v) x := by
  unfold lever
  rw [Equiv.apply_symm_apply]
  rfl
include p
theorem lantern (x : Dial.Scope n (Wrapped k w K)) :
    (Dial.iter n (gangway k w n p K) x).x = x.value.x ∘ lever (low (p x.whereNow) x.tick x.limit) := by
  rw [Dial.iter]
  dsimp only [Dial.advance]
  split_ifs with h
  ·
    let y : Dial.Hi n _ := ⟨x,h⟩
    change (Dial.iter n (gangway k w n p K) (Dial.advance n (gangway k w n p K) y)).x = _
    rw [lantern (Dial.advance n (gangway k w n p K) y)]
    let a := Dial.focus n y
    let i := x.whereNow
    let σ := p i
    let t := x.tick-1
    suffices e : low σ x.tick x.limit =
        (Equiv.swap (σ a).1 (σ a).2).trans (low σ t ((Nat.sub_le ..).trans x.limit)) by
      funext q
      change Byte (k i) at q
      change x.value.x (lever (Equiv.swap (σ a).1 (σ a).2)
        (lever (low σ t ((Nat.sub_le ..).trans x.limit)) q)) = _
      rw [lever_trans,← e]
      rfl
    have z : t+1=x.tick := by unfold t; omega
    cases x with
    | mk i m g x=> cases m with
      | zero=> exact (Nat.lt_irrefl _ h).elim
      | succ m=> rfl
  ·
    have v : x.tick=0 := by omega
    cases x with
    | mk i m g x=> cases m with
      | zero=> simp [low,Function.comp_def]
      | succ m=> contradiction
termination_by x.tick
decreasing_by change x.tick-1<x.tick; omega
end
end Thin

end IntegerMultiplication
end Computability
end OAI
