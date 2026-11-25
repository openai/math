import OAI.Computability.IntegerMultiplication.Haze.Paradigm

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Strip.Dial
open Code
variable {I : Type}
variable {r : Regime I} {L M : I → ℕ} (n : I→ℕ) (f : I→ℝ)
variable (h : r.Has (tally ∘ n))
variable {B : I→Type} (e : (i:I)→B i→Tree)
variable (g : (i:I)→Fin (n i)→B i→B i)
structure Scope (n : I→ℕ) (B : I→Type) where
  whereNow : I
  tick : ℕ
  limit : tick ≤ n whereNow
  value : B whereNow
abbrev where_ : Scope n B→ I := Scope.whereNow
def permit : Scope n B→Tree :=
  fun x=>Tree.fork (r.header x.whereNow) (send (tally x.tick))

include h
def rev (h : r.Has (tally ∘ n)) : Regime (Scope n B) where
  scale := r.scale ∘ where_ n
  header := permit n (r:=r)
  gauge := by
    let W := Scope n B
    let A (i:W) := (send (tally (n i.whereNow))).count
    have z : Dom (r.scale ∘ where_ n) A := (Regime.Small.extent (r:=r) (k:= send ∘ tally ∘ n) h).map (where_ n)
    dsimp only [permit, Tree.count]
    refine (((r.gauge.map (where_ n)).add (z.mono (b:=fun i:W=> (send (tally i.tick)).count) ?_)).add (Dom.const _ 1))
    intro i
    change size (tally _)≤ size (tally _)
    rw [size_tally,size_tally,tally_length,tally_length]; have := i.limit; omega
-- `include h` affects def? def doesn't see proof param => add explicit h to def since uses inside proof
omit h

abbrev Hi (n : I→ℕ) (B : I→Type) := {x : Scope n B // 0<x.tick}
abbrev hot (t : Hi n B) := t.val
abbrev stepR (h : r.Has (tally ∘ n)) :=
  ((rev n (B:=B) h).pull (@Subtype.val _ (fun x : Scope n B=>0<x.tick)))

def focus (t : Hi n B) : Fin (n t.val.whereNow) :=
  ⟨t.val.tick-1,by have := t.val.limit; have := t.property; omega⟩
def advance (t : Hi n B) : Scope n B :=
  ⟨t.val.whereNow, t.val.tick-1,(Nat.sub_le ..).trans t.val.limit,g _ (focus n t) t.val.value⟩
def land : Scope n B → Option (Scope n B) :=
  fun x=> if h : 0<x.tick then some (advance n g ⟨x,h⟩) else Option.none
def iter : (x:Scope n B) → B x.whereNow
| x =>
  if h : 0<x.tick then iter (advance n g ⟨x,h⟩) else x.value
termination_by x=> x.tick
decreasing_by change x.tick-1<x.tick; omega

include h
-- accessors
theorem small (q : I→Tree) (s : r.Small q) :
    (rev n (B:=B) h).Small (q ∘ where_ n) := by
  apply Code.Task.BT.compose _ (Code.Task.BT.map s _)
  let R := rev n (B:=B) h
  refine (show Code.Task.BT R.scale R.header (r.header ∘ where_ n) from
    ⟨fun i=> R.header i |>.count,R.gauge,(Task.dropRight _ _).mono (fun _=> by
      change _≤ _ +_ +_; omega)⟩)

theorem tick_ :
    (rev n (B:=B) h).Has fun i=> tally i.tick := by
  refine ⟨fun i=>(r.header i.whereNow).count,r.gauge.map (where_ n),Task.dropLeft _ _⟩

-- Sweep indexed group over countdown, preserving header for each step
abbrev node := where_ (B:=B) n
abbrev scLeaf := fun x:Scope n B=> e x.whereNow x.value
abbrev HiLib (h : r.Has (tally ∘ n)) :=
  let R := stepR (B:=B) n h
  let K (t : Hi n B) := t.val.whereNow
  Breeze (f ∘ K) R (M ∘ K) (L ∘ K)
    (together R.header (scLeaf n e ∘ hot n))
    (fun i=> scLeaf n e (advance n g i))

variable (a : ∀i,1 ≤ M i) (d : ∀ i,1≤f i)

abbrev States (B:I→Type) := Sigma B
abbrev start (x:States B) : Scope n B := ⟨x.1,n x.1,le_rfl,x.2⟩

variable (z : Alive (r.pull (Sigma.fst (β:=B))) (M ∘ Sigma.fst) (L ∘ Sigma.fst)
      (fun i:States B=> e i.1 i.2))
include a d z
theorem cyclone (c : HiLib n f e g h (M:=M) (L:=L)) :
    let E i := f i*((n i:ℝ)+1)
    Breeze (E ∘ Sigma.fst)
      (r.pull (Sigma.fst (β:=B))) (M ∘ Sigma.fst) (L ∘ Sigma.fst)
      (together (r.header ∘ Sigma.fst) (fun i:States B=> e i.1 i.2))
      (fun i:States B=> e i.1 (iter n g (start n i))) := by
  let D := Scope n B
  let R := rev n (B:=B) h
  let A := scLeaf n e
  let W (x:D) := together R.header A x
  let Z := fun i:D=> e i.whereNow (iter n g i)
  let M₀ := M ∘ where_ (B:=B) n; let L₀ := L ∘ where_ (B:=B) n
  let f₀ := f ∘ where_ (B:=B) n
  let f₁ i := f₀ i*((i.tick:ℝ)+1)
  have v : Alive R M₀ L₀ A := z.pull (fun i:D=> (show States B from ⟨i.whereNow,i.value⟩))
  have nz := fun i:D=> a i.whereNow
  have κ := Drive.started (l:=L₀) (r:=R) nz
  have Y : Alive R M₀ L₀ W := Rip.alivePair κ v
  have ts := tick_ n (B:=B) h
  let bb (x:D) : Bool := !(tally x.tick).isEmpty
  have eB : ∀ x:D, bb x=true ↔ 0<x.tick := by
    intro x; unfold bb tally; cases x.tick <;> simp [List.replicate_succ]
  have p : Rip R M₀ L₀ W (send ∘ bb) :=
    (Rip.split Y).1.chain (Rip.header nz
      (show R.Has bb from ts.ez (show Easy (fun x:Tally=> !x.isEmpty) from ?_)))
  · let Stop := {x : D // bb x=false}
    let step := hot (n:=n) (B:=B)
    let stop := (fun i:Stop=>i.val)
    have goals (x:D) : (bb x=false→∃ y:Stop,x=stop y) ∧ (bb x=true→∃ y:Hi n B,x=step y) :=
      ⟨fun h=>⟨⟨x,h⟩,rfl⟩,fun h=>⟨⟨x,(eB _).mp h⟩,rfl⟩⟩
    have Lo (i:Stop) : ¬ (0 < i.val.tick) := fun u=> (Bool.noConfusion ((i.property.symm.trans ((eB _).mpr u)):false=true))
    have lo : Breeze (f₀ ∘ stop) (R.pull stop) (M₀ ∘ stop) (L₀ ∘ stop) (W ∘ stop)
        (Z ∘ stop) := by
      refine Breeze.launch ?_ ?_; swap; exact fun i=> d (where_ n i.val)
      suffices m : Z ∘ stop=A ∘ stop by rw [m]; exact (Rip.split Y).2.pull stop
      funext i
      change e _ (iter _ _ _)=_
      rw [iter]
      dsimp only [advance]
      rw [dite_eq_right (Lo i)]
      rfl
    have hi : Breeze (f₀ ∘ step) (R.pull step) (M₀ ∘ step) (L₀ ∘ step) (W ∘ step)
        (W ∘ advance n g) := by
      let R₀ := R.pull step
      let M₁ := M₀ ∘ step; let L₁ := L₀ ∘ step
      have q := (Rip.split (Y.pull step)).1
      let H := tally ∘ Scope.tick (n:=n) (B:=B) ∘ step
      let Q (x:Hi n B) := r.header (step x).whereNow
      change Rip R₀ M₁ L₁ (W ∘ step) (together Q (send ∘ H)) at q
      have a := (Rip.split q.idle).2
      have u : Easy (fun i : Tally=> i.tail) :=
        show Easy List.tail from (by
          have r := (easy_cut ((Easy.const [()]).pair (easy_id (X:=Tally)))).sndCompose
          have eq : (fun x:Tally => (cutLists ([()],x)).2)=List.tail := by funext x; cases x <;> rfl
          simpa only [eq] using r)
      have j := q.chain ((Rip.split q.idle).1.twice (Loom.Fatigue.act (x:=H) a _ u))
      have w (x:ℕ) : (tally x).tail=tally (x-1) := by cases x <;> simp [tally,List.replicate_succ]
      unfold H at j
      simp only [Function.comp_def,w] at j
      exact (Breeze.launch j (fun i=>d (step i).whereNow)).pair c
    have q : Breeze f₁ R M₀ L₀ W Z :=
      spin bb p (land n g) stop step goals (fun x=> by unfold land stop; rw [dite_eq_right (Lo x)])
        (advance n g) (fun i=> by unfold land step hot; rw [dite_eq_left i.2]) lo hi
        (fun i x h=> by
          unfold land at h
          split at h
          · rename_i hi; injection h with h; subst x
            unfold Z
            conv_rhs => arg 2; rw [iter]
            dsimp only [advance]
            rw [dite_eq_left hi]
          contradiction)
        (fun i=> by unfold f₁ f₀; dsimp; have := d (where_ n (B:=B) i); positivity)
        (fun i _=> le_mul_of_one_le_right (le_trans (by norm_num) (d _)) (by simp))
        (fun i j he=> by
          unfold land at he; split at he
          next u =>
            injection he with e; subst j
            refine ⟨?_,le_rfl,le_rfl,le_rfl⟩
            change f₀ i*((i.tick:ℝ)+1)≥ f₀ i+ f₀ i*((↑(i.tick-1):ℝ)+1)
            push_cast [Nat.cast_sub u]; ring_nf; exact le_rfl --
          contradiction)
    have a' := q.along_cast (start n)
    let f (i:States B) := f₁ (start n i)
    let K := r.pull (Sigma.fst : States B→I)
    have t : K.Has (fun i=> tally (n i.1)) := Task.BT.map h (Sigma.fst : States B → I)
    let V : Alive K (M ∘ Sigma.fst) (L ∘ Sigma.fst) _ := Drive.started (fun i=> a i.1)
    let n := V.twice (Rip.header (fun i : States B=>a i.1 : ∀ (i:States B),1≤(M ∘ Sigma.fst) i) t)
    exact (Breeze.launch (n.left z) a'.1).next (show Breeze _ K _ _ _ _ from ⟨a'.1,a'.2⟩)
  have v := Easy.listCase (X:=Unit) (f:=fun _=>true) false (Easy.const _)
  have y : (fun l : Tally=> !l.isEmpty) = fun x=> List.casesOn (motive:=fun _=>Bool) x false (fun _ _=>true) := by
    funext l; cases l <;> rfl
  rw [y]; exact v
end Strip.Dial

end IntegerMultiplication
end Computability
end OAI
