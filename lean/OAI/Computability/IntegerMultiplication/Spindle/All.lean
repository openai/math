import OAI.Computability.IntegerMultiplication.Spindle.Cycle

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Spindle
open Strip Dims Adic Code Loom
variable {I J W L : Type} [Fintype J] [DecidableEq J] [Fintype W]
variable {D p : ℕ} [NeZero p] {τ : ℝ}
noncomputable section

def proceed (hp : 2≤p) : Hull D p → Task.Event (Hull D p)
| ⟨[],_⟩ => .done
| ⟨a::l,g⟩ => .jump (Shell.advance (⟨a,l,g⟩:Shell D p) hp)

omit [NeZero p] in
theorem healthy (hp : 2≤p) :
    ∀ x,Task.Event.sound (codeChart D p).issue (codeChart D p).reply x (proceed hp x) := by
  rintro ⟨_|⟨a,l⟩,y⟩
  · trivial
  exact returned hp (⟨_,_,y⟩:Shell D p)

-- base (width zero)
abbrev Blank D p := Craft D p []
abbrev seed (x : Blank D p) : Hull D p := ⟨[],x⟩
omit [NeZero p] in
private theorem leaf {x : Blank D p} (z : x.span.sector) :
    swapper _ _ _ z=z :=
  rfl -- Pin field0 Unit eta
omit [NeZero p] in
private theorem quick (hp : 2≤p) (d : 2≤D) :
    let G := regime (p:=p) d
    let H := seed (D:=D) (p:=p)
    let J0 := codeChart D p
    Rip (G.pull H) (Hull.rate ∘ H) (Hull.width ∘ H)
      (J0.issue ∘ H) (fun i => Task.Event.signal J0.issue J0.reply (H i) (proceed hp (H i))) := by
  let G := regime (p:=p) d
  let H := seed (D:=D) (p:=p)
  let r := G.pull H
  let n := Hull.rate ∘ H
  let l := Hull.width ∘ H
  let u i := (H i).scope
  have s : r.Has (fun i => (u i).mint) := Regime.self
  have ft := Bounds.opened u hp d s (Dom.base _)
  let T := fun i => Series.natural (l i)
  have f (i) : (T i).count ≤ l i := by simp [T]
  have h := Drive.self ft.1 (cloth_size _ _ ft (fun i => (H i).load) f)
  let i0 := (codeChart D p).issue ∘ H
  let j0 := (codeChart D p).reply ∘ H
  change Rip r n l i0 j0 at h -- swapper defeq? yes
  obtain ⟨k,e⟩ := h
  exact ⟨k,(fixture e.small e.budget _).twice e⟩

-- drive => event signal
variable (R : Series W) (d : Design J W L p τ)
include R d
private theorem quickHigh (g : 0<τ) :
    let G := regime (p:=p) d.occupancy
    let H := Shell.clip (D:=dim J) (p:=p)
    let J0 := codeChart (dim J) p
    Breeze (gust peak (dim J) τ ∘ H) (G.pull H) (Hull.rate ∘ H) (Hull.width ∘ H)
      (J0.issue ∘ H) (fun i => Task.Event.signal J0.issue J0.reply (H i) (proceed d.large (H i))) := by
  obtain ⟨x,k,z⟩ := drive d.large R d g.le
  exact ⟨x,k,(fixture z.small z.budget _).twice ((fixture z.small z.budget _).twice z)⟩

private def lamp (x : Hull D p) := !x.1.isEmpty
omit [NeZero p] R d in
private theorem case_lit (x : Hull D p) :
    (lamp x=false → ∃ i : Blank D p,x=seed i) ∧ (lamp x=true → ∃ i:Shell D p,x=i.clip) := by
  rcases x with ⟨_|⟨a,l⟩,v⟩
  · exact ⟨fun _ => ⟨_,rfl⟩,fun h => Bool.noConfusion (show false=true from h)⟩
  exact ⟨fun h => Bool.noConfusion (show true=false from h), fun _ => ⟨⟨_,_,_⟩,rfl⟩⟩

-- Sized.select cost simpler via Task.control and same D.
omit R d in
private theorem timerSplit {I α β : Type} {p q : I→Tree} {w : I→ℝ}
    (tag : I→Bool) (hi : β → I) (low : α→I)
    (covers : (i : I) → (tag i=false → ∃ x,i=low x) ∧ (tag i=true → ∃ y,i=hi y))
    (s : Sized (w ∘ low) (p ∘ low) (q ∘ low))
    (t : Sized (w ∘ hi) (p ∘ hi) (q ∘ hi)) :
    Sized w (together (send ∘ tag) p) q := by
  have z : ∀ i,1≤w i := by
    intro i
    cases d : tag i
    · obtain ⟨v,rfl⟩ := (covers i).1 d; exact s.1 _
    obtain ⟨v,rfl⟩ := (covers i).2 d; exact t.1 _
  let A i := ⌈w i⌉₊
  have j : Task A (together (send ∘ tag) p) q := by
    apply Task.control tag
    · let X := {i // tag i=false}
      choose u h using fun i : X => (covers i.1).1 i.2
      simpa only [Function.comp_def,← h] using Task.on s.release u
    let X := {i // tag i=true}
    choose u h using fun i : X => (covers i.1).2 i.2
    simpa only [Function.comp_def,← h] using Task.on t.release u
  refine ⟨z,A,j,3,fun i => ?_⟩
  specialize z i; simp only [A,Nat.cast_ofNat]
  have t := Nat.ceil_lt_add_one (show 0≤w i by linarith)
  linarith

set_option maxHeartbeats 600000 in
private theorem everywhere (g : 0<τ) :
    let G := regime (p:=p) d.occupancy
    let M := codeChart (dim J) p
    Breeze (gust peak (dim J) τ) G Hull.rate Hull.width
      M.issue (fun i => Task.Event.signal M.issue M.reply i (proceed d.large i)) := by
  let G := regime (p:=p) d.occupancy
  let M := codeChart (dim J) p
  let H := Hull (dim J) p
  have s := Bounds.opened (s:= Hull.scope (D:=dim J)) d.large d.occupancy
    (Regime.self (r:=G) : G.Has fun i => i.scope.mint) (Dom.base _)
  let T i := Series.natural (Hull.width (D:=dim J) (p:=p) i)
  have hv (i) : (T i).count ≤ Hull.width i := by simp [T]
  have v := cloth_size _ T s Hull.load hv
  have e : Alive G Hull.rate Hull.width M.issue :=
    Rip.alivePair (Rip.header s.1 Regime.self) v
  have a : G.Has lamp := by
    have y := (Bounds.kept (fun i:H => i.scope) (Regime.self (r:=G))).1
    show G.Has _; have f := y.ez (Easy.listCase (X:=Tally) (f:=fun _ => true) false (Easy.const _)) -- definitional (!isEmpty)?
    suffices u : (lamp (p:=p) (D:=dim J)) = (fun i => List.casesOn (motive:=fun _=>Bool) i.1 false (fun _ _ => true)) from u ▸ f
    funext i; rcases i with ⟨_|⟨a,l⟩,g⟩ <;> rfl
  have c := ((Rip.split e).1.chain (Rip.header s.1 a)).twice e
  have hi := mild (peak:H→ℕ) (dim J) (by have := d.occupancy; omega) g.le
  obtain ⟨_,u,t⟩ := Breeze.launch c hi
  let Z := runrate (gust (peak:H→ℕ) (dim J) τ) G Hull.rate Hull.width
  obtain ⟨_,b,y⟩ := Breeze.launch (quick d.large d.occupancy)
    (show ∀ x:Blank (dim J) p,1≤(gust peak _ τ ∘ seed) x from fun _ => hi _)
  obtain ⟨_,c,z⟩ := quickHigh R d g
  have wor j : Z j=runrate (gust peak (dim J) τ) G Hull.rate Hull.width j := rfl
  let k := u+b+c
  have tb := t.larger (fun i => rate_higher i (hi i) (by omega : u≤k))
  refine ⟨hi,k,tb.chain ?_⟩
  have td : Sized (Z k) _ _ :=
    timerSplit (w:=Z k) (p:=M.issue) (q:=fun i => Task.Event.signal M.issue M.reply i (proceed d.large i)) lamp Shell.clip seed case_lit (y.runs.mono (d:=Z k ∘ seed)
      (fun i => (rate_higher (r:=G) (n:=Hull.rate) (l:=Hull.width) (seed i) (hi _) (by omega : b≤k)))) (z.runs.mono (d:=Z k ∘ Shell.clip)
      (fun i => (rate_higher (r:=G) (n:=Hull.rate) (l:=Hull.width) (Shell.clip i) (hi _) (by omega : c≤k))))
  exact ⟨td,tb.out⟩

private def agenda (D) (τ : ℝ) (d : 2≤D) (k) :=
  fun x:Hull D p => mass (regime d) Hull.rate Hull.width k x*(acres τ D x.plan+1)
theorem campaign (g : 0<τ) :
    ∃ k, Sized (agenda (dim J) (p:=p) τ d.occupancy k)
      (codeChart (dim J) p).issue (codeChart (dim J) p).reply := by
  obtain ⟨a,k,t⟩ := everywhere R d g
  let F := gust (peak:Hull (dim J) p→ℕ) (dim J) τ
  let G := regime (p:=p) d.occupancy
  let T := runrate F G Hull.rate Hull.width
  refine ⟨k,Sized.suspend (proceed d.large) t.runs (healthy d.large) (fun i => ?_) (fun i => ?_)⟩
  · have s := Bounds.opened (s:= Hull.scope (D:=dim J)) d.large d.occupancy
      (Regime.self (r:=G) : G.Has fun i => i.scope.mint) (Dom.base _)
    have hz : 0 ≤ acres τ (dim J) i.plan := by
      unfold acres; apply List.sum_nonneg
      intro b h
      obtain ⟨w,_,rfl⟩ := List.mem_map.mp h
      unfold dim; positivity
    exact one_le_mul_of_one_le_of_one_le (unit_mass s.1 k i) (by linarith)
  rcases i with ⟨l,v⟩
  cases l with
  | nil => simp [peak,proceed,agenda,runrate,gust,Hull.plan, acres]
  | cons a l =>
    let s : Shell (dim J) p := ⟨a,l,v⟩
    change (mass G Hull.rate Hull.width k s.clip)*((dim J:ℝ)^τ)^a.length + agenda (dim J) τ d.occupancy k (s.advance d.large) ≤
      agenda (dim J) τ d.occupancy k s.clip
    have eq : mass G Hull.rate Hull.width k (s.advance d.large)=mass G Hull.rate Hull.width k s.clip := by
      have ⟨t,z,e⟩ := landing d.large s
      unfold mass G regime
      simp only [t,z,e]
    simp only [agenda] -- eq matches?
    change _* _ + (mass G Hull.rate Hull.width k (s.advance d.large) : ℝ) * (acres τ (dim J) l+1) ≤
      mass G Hull.rate Hull.width k s.clip*(acres τ (dim J) (a::l)+1)
    rw [eq,plus_acres]; linarith
end
end Spindle

end IntegerMultiplication
end Computability
end OAI
