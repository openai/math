import OAI.Computability.IntegerMultiplication.Hook.Pulse

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Hook
open Strip Dims Loom Adic Code Net Net.Walsh Haze Earth Phase Packed Axon Staff Dusk Bits
variable {I J W A X: Type} [Codec X] (d₀:X) [Fintype J] [DecidableEq J] [Fintype W] (dl : Guild J W A Motif.sigma) (R₁ : Series W)
variable (p t : I→Tape) (f g j y w U : I→ℕ) {T:I→Type} (z:(i:I)→Series (T i)) {r:Regime I}
variable (h : ArrayCards r p t w)
variable (F: Realizes r f) (G:Realizes r g) (J₁:Realizes r j) (Y:Realizes r y)
variable (u:∀ i,((z i).count+1)*(w i+1)≤U i)
variable (s:∀ i,Phase.safe (f i) (j i)) (q:∀ i,Phase.safe (f i) (y i)) (m:∀ i,f i≤w i+1)
variable (hn:∀ i,1≤f i)
variable (o : (i:I)→Fin (f i)→Word) (O:r.Has (fun i=>List.ofFn (o i)))
variable (g₁ : I→ℝ) (X₀ : I→ Ask.Tab (X:=X)) (A₀:I→Dusk.Pair× X→Dusk.Pair) (Y₀ : I→ℕ→X) (L:(i:I)→ Grain (w i) × X→ Grain (w i))
variable (lv : ∀ i,1≤g₁ i)
variable (d : Register g j y w U X₀ A₀ Y₀ L g₁)

noncomputable section
abbrev Datum (i:I) := residue p t f g j y i → T i → Grain (w i)
def present (i:I) (x : Datum p t f g j y w (T:=T) i) :=
  Tree.fork (send (X₀ i))
    (stripe (zone p t f g j y i)
      (fun a=> strip (z i) fun b=> Dusk.mark (x (browser a) b)))
abbrev altitude (i:I) := Ht (g i) (j i) (y i)
def drift (i:I) (k:Fin (altitude g j y i)) (x : Datum p t f g j y w i (T:=T)) : Datum p t f g j y w i (T:=T) :=
    runOn (fun (x:residue p t f g j y i→ Grain (w i)) a=> L i (Hook.logic (b:=k) Walsh.F x a,Y₀ i (θ k (Bits.value ∘ (o i)) a.2 % 2^(altitude g j y i)))) x -- define by direct
def gesture (i:I) (x : Datum p t f g j y w i (T:=T)) :=
  (layers (altitude g j y i)).foldl (fun a k=> drift p t f g j y w o Y₀ L i k a) x

-- pull Register along
theorem table_alive (s : ∃ a:ℕ,∀ i,size (X₀ i)≤ a*(U i+1))
    (N : I→ℕ) (q :∀ i,1≤N i) : Alive r N U (fun i=> send (X₀ i)) := by
  obtain ⟨B,b⟩:=s
  refine ⟨0,Carries.idles (unit_mass q 0) ⟨B, fun i=>?_⟩⟩
  simp only [mass,pow_zero]
  change ((size (X₀ i)):ℝ) ≤ _
  have H : (size (X₀ i):ℝ)≤ (B:ℝ)*((U i:ℝ)+1) := by exact_mod_cast b i
  refine H.trans ?_
  gcongr; exact le_mul_of_one_le_left (by positivity) (by exact_mod_cast q i)
include d h F G J₁ Y u
theorem Kit :
    Alive (r.pull (Sigma.fst (β:=Datum p t f g j y w (T:=T)))) (listB p t f g j y ∘ Sigma.fst) (U ∘ Sigma.fst)
      (fun i=> present p t f g j y w z X₀ i.1 i.2) := by
  obtain ⟨B,b⟩ := d.volume
  let H := T
  let Z := Dial.States (Datum p t f g j y w (T:=H))
  let atZ := Sigma.fst (β:=Datum p t f g j y w (T:=H))
  let u0 := listB p t f g j y
  have q : ∀ i,1 ≤ u0 i := (placeR p t f g j y w h F G J₁ Y).1
  have s : Station (r.pull atZ) (fun i=>zone p t f g j y i.1) := by
    obtain ⟨k,u'⟩ := placeR p t f g j y w h F G J₁ Y
    exact ⟨fun i=> k i.1,u'.pull atZ⟩
  let k₁ (i:Z) := (send (X₀ i.1))
  have o₁ : Alive (r.pull atZ) (u0 ∘ atZ) (U ∘ atZ) k₁ :=
    (table_alive U X₀ (r:=r) ⟨B,b⟩ u0 q).pull atZ
  exact Rip.alivePair o₁ (shelter (fun i=>zone p t f g j y i.1) (fun i:Z=> z i.1) _ (fun i=> i.2 ∘ browser) s (fun i=> le_trans (Nat.mul_le_mul_right _ (Nat.le_succ _)) (u i.1))) -- n mul

include d₀ dl R₁ O lv s q m hn
omit [Codec X] d₀ [Fintype J] [DecidableEq J] [Fintype W] dl R₁ h F u s q m hn O lv d in
private theorem ascent : Realizes r (altitude g j y) := (G.times J₁).plus Y
-- reverse schedule parameter
private def down' (i:I) (k : Fin (altitude g j y i)) := drift p t f g j y w o Y₀ L (T:=T) i (Fin.rev k)
private theorem exit_r (h₀ : Realizes r (altitude g j y)) :
    Dial.HiLib (M:=listB p t f g j y) (L:=U)
      (altitude g j y) (forecast f j y g₁) (present p t f g j y w z X₀)
      (down' p t f g j y w o Y₀ L) h₀ := by
  let D := Datum p t f g j y w (T:=T)
  let n := altitude g j y
  let Q := Dial.Hi n D
  let i_ (i:Q) := i.val.whereNow
  let R := Dial.stepR (B:=D) n h₀
  have sm {A} [Codec A] (x:I→A) (v : r.Has x) : R.Has (x ∘ i_) :=
    Code.Task.BT.map (Dial.small n h₀ (send ∘ x) v) (fun x:Q=>x.val)
  have ex (x) (v:Realizes r x) : Realizes R (x ∘ i_) := sm _ v
  let N := listB p t f g j y ∘ i_
  let a (i:Q) : Fin (altitude (g ∘ i_) (j ∘ i_) (y ∘ i_) i) :=
    Fin.rev (Dial.focus n i)
  let tick (i:Q) := i.val.tick
  have b0 : Realizes R tick := Code.Task.BT.map (Dial.tick_ n h₀) (fun x:Q=> x.val)
  have b : Realizes R (fun i:Q=> (a i).val) := by
    have e (i) : (a i).val = (n ∘ i_) i - tick i := by
      unfold a Dial.focus Fin.rev
      change n (i_ i)-(tick i-1+1)=_
      have t : 0 < tick i := i.property
      dsimp only [Function.comp_apply,tick] at * -- dsimp at * massive?
      omega
    simp_rw [e]; exact (ex _ h₀).minused b0
  have dl' : Register (g ∘ i_) (j ∘ i_) (y ∘ i_) (w ∘ i_) (U ∘ i_) (X₀ ∘ i_) (A₀ ∘ i_) (Y₀ ∘ i_) (fun i=> L (i_ i)) (g₁ ∘ i_) :=
    {correct i:=d.correct _
     full i:=d.full _
     volume:= by obtain ⟨v,t⟩ := d.volume; exact ⟨v,fun _=>t _⟩
     fare := by obtain ⟨v,t⟩ := d.fare; exact ⟨v,fun _=> t _⟩
     width := by obtain ⟨v,t⟩ := d.width; exact ⟨v,fun i=> t _⟩
     released i:= d.released _
     consumes:= d.consumes.slide (fun i : Sigma (fun i=>Grain ((w ∘ i_) i) × ℕ)=>⟨i_ i.1,i.2⟩)}
  let x (i:Q) := i.val.value
  let A (i:Q) := present p t f g j y w z X₀ (i_ i) (x i)
  have sp := placeR p t f g j y w h F G J₁ Y
  have Ok := (Kit p t f g j y w U z h F G J₁ Y u g₁ X₀ A₀ Y₀ L d).pull (fun i:Q=> (show Sigma D from ⟨i_ i,x i⟩))
  have h1 := Rip.split (Drive.self (n:=N) (l:=U ∘ i_) (r:=R) (fun i=> sp.1 _) (show Alive R N (U ∘ i_) A from Ok))
  have hp : ArrayCards R (p ∘ i_) (t ∘ i_) (w ∘ i_) :=
    ⟨⟨fun i=>h.prefix_.solid _,sm _ h.prefix_.shape⟩,⟨fun i=> h.trail.solid _,sm _ h.trail.shape⟩,
      fun i=> h.below _, ex _ h.digits⟩
  have o2 := process d₀ dl R₁ _ _ _ _ _ _ _ (U ∘ i_) (fun i:Q=>z (i_ i)) hp (ex _ F) (ex _ G) (ex _ J₁) (ex _ Y)
    (fun i=> u (i_ i)) (fun i=> s (i_ i)) (fun i=> q (i_ i)) (fun i=> m (i_ i)) (fun i=>hn (i_ i))
    x a b (fun i=> o (i_ i)) (sm _ O) (g₁ ∘ i_) (X₀ ∘ i_) (A₀ ∘ i_) (Y₀ ∘ i_) (fun i=> L (i_ i))
    (fun i=>lv (i_ i)) dl' A h1.1 h1.2
  exact (Breeze.launch h1.1 o2.1).pair o2

-- List correspondence
omit s q m d h O d₀ F G J₁ Y dl R₁ hn u lv
omit [Codec X] in
private theorem spent_ (i:I) {h:ℕ} (z : h ≤ altitude g j y i)
    (x:Datum p t f g j y w (T:=T) i) :
    Dial.iter (B:=Datum p t f g j y w (T:=T)) _ (down' p t f g j y w o Y₀ L)
       ⟨i,h,z,x⟩ =
      (List.ofFn (fun j:Fin h=> Fin.rev (Fin.castLE z (Fin.rev j)))).foldl
        (fun x k=> drift p t f g j y w o Y₀ L i k x) x := by
  induction h generalizing x with
  | zero =>
    rw [Dial.iter]
    dsimp only [Dial.advance]
    rw [dite_eq_right (Nat.lt_irrefl 0)]
    rfl
  | succ h ih =>
    conv_lhs => rw [Dial.iter]
    dsimp only [Dial.advance]
    rw [dite_eq_left (Nat.succ_pos h)]
    rw [List.ofFn_succ,List.foldl_cons]
    -- identify
    let h' : h ≤ altitude g j y i:= Nat.le_of_succ_le z
    let u := Fin.rev (Fin.castLE z (Fin.rev (0:Fin (h+1))))
    change Dial.iter _ _ ⟨i,h,h',drift _ _ _ _ _ _ _ _ _ _ i _ x⟩=_
    have e : Dial.focus (altitude g j y) (B:=Datum p t f g j y w (T:=T)) (show Dial.Hi (altitude g j y) (Datum p t f g j y w (T:=T)) from ⟨⟨i,h+1,z,x⟩,Nat.succ_pos _⟩)=Fin.castLE z (Fin.rev 0) := by ext; simp [Dial.focus]
    -- simpler simp for iterate parameter?
    rw [ih h']
    have hlist : (List.ofFn (fun t : Fin h => (Fin.castLE h' t.rev).rev)) =
        List.ofFn (fun t : Fin h => (Fin.castLE z t.succ.rev).rev) := by
      apply congrArg List.ofFn
      funext t
      apply Fin.ext
      simp [Fin.rev]
    rw [e, hlist]

include d h O d₀ F G J₁ Y dl R₁ hn u lv s q m
theorem epilog (x:(i:I)→ Datum p t f g j y w i (T:=T)) :
    let fee i := forecast f j y g₁ i*((altitude g j y i:ℝ)+1)
    let N := listB p t f g j y
    let A (v:(i:I)→Datum p t f g j y w i (T:=T)) := fun i=> present p t f g j y w z X₀ i (v i)
    Breeze fee r N U (together r.header (A x)) (A fun i=> gesture p t f g j y w o Y₀ L i (x i)) := by
  let n := altitude g j y
  have ω : Realizes r n := (G.times J₁).plus Y
  have sp := placeR p t f g j y w h F G J₁ Y
  let K := forecast f j y g₁
  have y0 i : 1≤K i := by
    unfold K forecast stairs expense
    have d : (0:ℝ)≤(((j i+y i:ℕ):ℝ)+1)*((f i+1:ℕ):ℝ)^Net.Motif.sigma := by positivity
    linarith [lv i]
  have T0 := Dial.cyclone n K ω (present p t f g j y w z X₀) (down' p t f g j y w o Y₀ L (T:=T)) sp.1 y0 (z:=
    Kit p t f g j y w U z h F G J₁ Y u g₁ X₀ A₀ Y₀ L d)
    (exit_r d₀ dl R₁ p t f g j y w U z h F G J₁ Y u s q m hn o O g₁ X₀ A₀ Y₀ L lv d ω)
  have motionx := T0.along_cast (fun i:I=> (show Sigma _ from ⟨i,x i⟩))
  have e (i:I) :
      gesture p t f g j y w o Y₀ L i (x i) = Dial.iter n (down' p t f g j y w o Y₀ L) (Dial.start n (show Sigma _ from ⟨i,x i⟩)) := by
    unfold gesture Dial.start
    rw [spent_]
    suffices q : (List.ofFn (fun j:Fin (n i)=>Fin.rev (Fin.castLE (show n i≤n i by rfl) (Fin.rev j)))) = layers (n i) by rw [q]
    simp [layers]; rfl
  simp_rw [e]
  exact ⟨fun i=> (motionx.1 i),motionx.2⟩
end
end Hook

end IntegerMultiplication
end Computability
end OAI
