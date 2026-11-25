import OAI.Computability.IntegerMultiplication.Morse.Club

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Morse
open Net Net.Walsh Strip Loom Adic Dusk Grid Axon Finset Code Bits
variable {k w t:ℕ}
abbrev Dot := Dusk.Pair×Dusk.Pair
abbrev Mat := Seat × Seat
-- mixture source. c=0 chooses sum; c=1 diff.
def blend (c:B)(x:Dot) :=
  Dusk.gather (x.1,if c=1 then Dusk.lower x.2 else x.2)
@[fun_prop] theorem blend_cost (v:B):Easy (blend v) := by
  unfold blend; split
  · have h := Dusk.lower_easy; have k:=Dusk.gather_easy; fun_prop
  exact Dusk.gather_easy -- pair eta
@[simp] theorem blend_l (c:B)(u v:Grain w):blend c (Dusk.mark u,Dusk.mark v)=
    Dusk.mark (u+Net.Walsh.F c 1*v):=by
  rcases bit_value c with h|h <;> subst c <;> simp [blend,Walsh.F]
-- packet for one. force output Delta
def brisk (c:B)(x:Dot×card₀) : Dusk.Pair×Orb :=
  (blend c x.1,if c=0 then x.2.1 else x.2.2)
@[fun_prop] theorem brisk_easy (c:B): Easy (brisk c) := by
  unfold brisk; split <;> fun_prop

theorem bracked (p:ℕ)(v:B) (a:cls (k+1) w)(z:Face k)(q:Word)(b:ℕ→Grain w):
    Grid.adjust (brisk v ((Dusk.mark (a (pre 0 z)),Dusk.mark (a (pre 1 z))),shop p q b z))=
      Dusk.mark (blink p q b a v z) := by
  rcases bit_value v with rfl|rfl <;> simp [brisk,blink,Grid.inject,wage,shop,item]
-- point
structure Hooked where
  n:ℕ -- residual length
  w:ℕ
  p:ℕ
  v:p≤w+1
  q:Word
  b:ℕ→Grain w
  a: cls (n+1) w
  z: Face n
open Hooked
def rawD(i:Hooked):Dot:= (Dusk.mark (i.a (pre 0 i.z)),Dusk.mark (i.a (pre 1 i.z)))
abbrev rawC(i:Hooked) := shop i.p i.q i.b i.z
abbrev brightD(i:Hooked):Dot×card₀:=(rawD i,rawC i)
noncomputable section
theorem parcel (i:Hooked):size (brightD i) ≤ 64*(i.w+1) := by
  have e a:= tea i.p i.q i.b i.v i.z a
  unfold brightD rawD rawC shop
  rw [size_prod,size_prod]; dsimp only; rw [Dusk.volume,Dusk.volume,size_prod]; dsimp only
  linarith [e 0,e 1]
theorem markWay (c:B):
    Carries (Grid.cost (fun i:Hooked=>i.w)) (send ∘ brightD) (fun i=> send (Dusk.mark (blink i.p i.q i.b i.a c i.z))) := by
  let f:Dusk.Pair×Dusk.Pair×card₀→Dusk.Pair:=fun x=>Grid.adjust (brisk c ((x.1,x.2.1),x.2.2))
  let g:Dot×card₀→Dusk.Pair:= fun x=> Grid.adjust (brisk c x)
  have E:Charming g:= (smooth (brisk_easy c)).leads adjust_p
  have e := (E.slide _ 64 parcel).bill
  simpa only [Function.comp_def,bracked,g,rawD,rawC,brightD] using e

-- generic per-row transfer at this Hook.z for all stations in suffix.
structure Panel where
  k:ℕ
  t:ℕ
  w:ℕ
  p:ℕ
  q:Word
  b:ℕ→Grain w
  a: Deck (k+1) t w
  z: Face k
  ok:p≤w+1
abbrev individual (r:Panel)(i:Fin r.t) : Hooked:=
  ⟨r.k,r.w,r.p,r.ok,r.q,r.b,(fun v=>r.a v i),r.z⟩
abbrev boost (r:Panel) : card₀:=shop r.p r.q r.b r.z
abbrev hint (r:Panel): Mat:=
  (slump (r.a (pre 0 r.z)),slump (r.a (pre 1 r.z)))
abbrev article (r:Panel): Mat×card₀:=
  (hint r,boost r)
abbrev ground (r:Panel)(c:B)(i:Fin r.t) : Grain r.w :=
  blink r.p r.q r.b (fun v=>r.a v i) c r.z
abbrev lab (r:Panel):ℝ:= ((r.t:ℝ)+1)*Grid.cost (fun r:Panel=>r.w) r
abbrev duoR (r:Panel): Seat×Seat := (slump (ground r 0),slump (ground r 1))

theorem walk0 (r:Panel):1≤lab r:=
  one_le_mul_of_one_le_of_one_le (by simp) (cost_pos ..)
theorem packD (r:Panel):
    size (boost r) ≤ 25*(r.w+1) := by
  rw [boost,shop,size_prod]; dsimp only
  have e a:= tea r.p r.q r.b r.ok r.z a
  linarith [e 0,e 1]
theorem big_ (r:Panel):
    (size (article r):ℝ) ≤ 60*lab r := by
  have p: size (article r) ≤60*((r.t+1)*(r.w+1)) := by
    unfold article hint
    rw [size_prod,size_prod]; dsimp only
    have e:=packD r
    have h:=szSlump (r.a (pre 0 r.z))
    have i:=szSlump (r.a (pre 1 r.z))
    nlinarith
  unfold lab Grid.cost
  have t0 : (1:ℝ) ≤ Grid.tax (r.w) := by exact_mod_cast tax_pos ..
  calc
    (size (article r):ℝ) ≤ ((60*((r.t+1)*(r.w+1)):ℕ):ℝ) := by exact_mod_cast p
    _ ≤ _ := by push_cast; have z : (0:ℝ)≤(r.t+1:ℝ)*(r.w+1) := by positivity
                change 60*_≤ 60*((r.t+1:ℝ)*((r.w+1)* tax r.w))
                nlinarith [mul_le_mul_of_nonneg_left t0 z]

private theorem visit {α}(n:ℕ)(f:Fin n→α): Series.tab (Series.natural n) f=List.ofFn f := by
  change List.map f (List.finRange _)=_
  simp [List.finRange,Function.comp_def]
-- stage
theorem cross1 (c:B): Carries lab (send ∘ article) (fun r=> send (slump (ground r c))) := by
  -- root projections from article
  let p(i:Panel):=send (article i)
  have s:=Carries.idles walk0 (p:=p) (show Volume lab p from ⟨60,fun i=>by change (size (article i):ℝ)≤_; rw [Nat.cast_ofNat]; exact big_ i⟩)
  have headX := s.chain (Carries.func walk0 s.out Prod.fst Easy.fst)
  have headB := s.chain (Carries.func walk0 s.out Prod.snd Easy.snd)
  -- align pair of rows to individual dots
  let d:Dusk.Pair := ([],[])
  have both:= headX.chain (Carries.func walk0 headX.out (lock id d d) (easy_lock _ Easy.identity d d))
  let X (r:Panel) (i:Fin r.t):=brightD (individual r i)
  have j r: lock id d d (hint r)=List.ofFn (fun i:Fin r.t=>(X r i).1) := by
    unfold hint slump
    rw [← visit, ← visit, ← visit,paired]; rfl
  have B1 : Carries lab p (fun i=>send (List.ofFn (fun k=>(X i k).1))) := by
    simp_rw [← j]; exact both
  have t := B1.chain (Carries.func walk0 B1.out ruler (Easy.ruler Easy.identity))
  let N (r:Panel):=Series.natural r.t
  have z: Carries lab p (fun i=>Tree.fork (send (tally (N i).count)) (send (boost i))) := by
    have q0 := t.twice headB
    simpa only [N,Series.count_natural,ruler,tally,List.map_const',List.length_ofFn] using q0
  have V : ∃ K:ℕ,∀ i:Panel, ((N i).count+1:ℝ)*(send (boost i)).count≤K*lab i := by
    refine ⟨25,fun r=>?_⟩
    rw [show (N r).count=r.t from Series.count_natural _]; unfold lab cost
    change _ * (size (boost r):ℝ) ≤ _ * _
    have z : (1:ℝ)≤ Grid.tax r.w := by exact_mod_cast tax_pos ..
    have w : (size (boost r):ℝ)≤25*((r.w:ℝ)+1):=by exact_mod_cast packD r
    push_cast
    have s : (0:ℝ)≤ r.w:=Nat.cast_nonneg _
    have j : (0:ℝ)≤ r.t:=Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left z (show (0:ℝ)≤(r.t+1:ℝ)*(r.w+1) by positivity)]
  have S := Strip.spread N _ z V
  have B2 : Carries lab p (stackRun N fun i (k:Fin i.t)=> send (X i k).1) := by
    unfold stackRun; simp_rw [stripe_eq',N,visit]; exact B1
  have U0: Carries lab p (stackRun N fun i k=> send (X i k)) :=
    Strip.coalesce _ _ _ B2 S
  let A : (Σ i:Panel,Fin i.t)→Hooked := fun x=>individual x.1 x.2
  let y(r:Panel) (v:Fin r.t):=send (Dusk.mark (ground r c v))
  have s1 : ∀ i:Panel,1≤(↑i.w+1:ℝ)* Grid.tax i.w:=cost_pos _
  have T := Strip.liftoff N (fun i k=> send (X i k)) y (fun i=>(↑i.w+1:ℝ)*Grid.tax i.w) ((markWay c).slide A)
  have M:= U0.chain (T.larger (d:=lab) (by intro i; rw [show (N i).count=i.t from Series.count_natural _]; unfold lab Grid.cost; linarith [s1 i]))
  unfold stackRun at M
  change Carries lab p (fun i=>stripe (N i) (fun k=> send (Dusk.mark (ground i c k)))) at M
  simp_rw [stripe_eq',N,visit] at M
  exact M

theorem cross : Carries lab (send ∘ article) (send ∘ duoR) :=
  (cross1 0).twice (cross1 1)
end
end Morse

end IntegerMultiplication
end Computability
end OAI
