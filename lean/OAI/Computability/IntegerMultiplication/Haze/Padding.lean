import OAI.Computability.IntegerMultiplication.Haze.Column

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Haze
open Net Net.Shuttle Net.Tensor Net.Walsh Strip Strip.Dims Strip.Optic Code Packed Loom Dusk IntegerMultiplication.Phase
open Finset Spindle

variable {J I W U : Type} [Fintype J] [DecidableEq J] [Fintype W]
local notation "θ" => Net.Motif.sigma
variable (d : Guild J W U θ) (R : Series W) {r : Regime I}
variable (k : I→ℕ) (e : (i:I)→Estate (dim J) (dim J ^ k i))
variable (a : r.Small fun i=> (e i).cert (k i))
variable (u : Dom r.scale fun i=> (e i).metres)
variable (v : r.Has (tally ∘ k)) (q : r.Has fun i=>tally (e i).shade)

-- mask
noncomputable section
private def blackout (k : Tally) : Dusk.Pair :=
  let g : List Bool := fill false (()::k)
  (g,g)
private theorem solid0 : Easy blackout := by unfold blackout; fun_prop
private theorem noData (k : ℕ) :
    blackout (tally k)=Dusk.mark (0:Grain k) := by
  suffices e : fill false (()::tally k) = trip (0:day k) by
    exact Prod.ext e e
  apply Bits.word_inject <;> simp [fill_eq]
def heat (x : Tally × Tally) :=
  ((x.2.map fun _ => blackout x.1),x.2.tail)
theorem air0 : Poly heat := by
  have u : Easy (fun x:Tally×Tally=> (x.2,blackout x.1)) :=
    Easy.snd.pair (Easy.fst.compose solid0)
  let y := u.poly.compose Packed.chamber
  apply Poly.pair y
  refine (Easy.snd.compose ?_).poly
  have h := (Code.easy_cut ((Easy.const [()]).pair (easy_id (X:=Tally)))).sndCompose
  suffices w : (fun i:Tally => i.tail) = fun i=> (Code.cutLists ([()],i)).2 from by simpa only [← w] using h
  funext v; cases v <;> rfl
def feeder (x : (List Dusk.Pair × Tally) × List Dusk.Pair) :=
  x.2 ++ (Code.cutLists (dial (ruler x.2,x.1.2),x.1.1)).1
theorem fastForward : Easy feeder := by
  let j := ((Easy.ruler (Easy.snd (X:=List Dusk.Pair×Tally) (Y:=List Dusk.Pair))).pair
      (Easy.fst.compose Easy.snd)).compose easy_dial
  exact (Easy.snd.pair
    ((Code.easy_cut (j.pair (Easy.fst.compose Easy.fst))).fstCompose)).compose Easy.append
private def cutback (x : List Dusk.Pair × List Dusk.Pair) :=
  (cutLists (ruler x.2,x.1)).1
private theorem easy_back : Easy cutback :=
  (easy_cut ((Easy.ruler Easy.snd).pair Easy.fst)).fstCompose

theorem fed {j n : ℕ} (s : List (Grain j)) (q : 1≤n) :
    feeder (heat (tally j,tally n), s.map Dusk.mark) =
      (s++List.replicate (excess n s.length) 0).map Dusk.mark := by
  have h := (envelope n s.length q).2.le
  simp [feeder,heat,cutLists,dial,tally,ruler,List.map_replicate,List.take_replicate] -- tally unfolding objection
  have z : List.map ((fun _ : Dusk.Pair => ()) ∘ Dusk.mark) s = tally s.length := by simp [tally,Function.comp_def]
  rw [z]; erw [Nat.min_eq_left h]
  exact ⟨rfl,Or.inr (noData j)⟩
  -- inspect

variable {T : I→Type} (s : (i:I)→Series (T i))
private def dwells {S} (a : Series S) (i:S) := (a.index i).val
private theorem helpCut {A F : Type} (s : Series A) (a : Series F) (z v : A → Dusk.Pair) (x : F→Dusk.Pair)
    (l : s.count ≤ a.count)
    (h : ∀ i,x (a.index.symm ⟨(s.index i).val,((s.index i).isLt.trans_le l)⟩)=z i) :
    cutback (a.tab x,s.tab v)=s.tab z := by
  unfold cutback cutLists
  simp only [ruler_length,Series.card]
  apply List.ext_getElem (by simp only [Series.card,List.length_take]; simp only [Nat.min_eq_left l])
  intro i r u
  rw [List.getElem_take]
  have t : i<s.count := by simpa only [Series.card] using u
  let y : A := s.index.symm ⟨i,t⟩
  rw [a.get _ ⟨i,t.trans_le l⟩,s.get _ ⟨i,t⟩]
  simpa only [y,Equiv.apply_symm_apply] using h y
include d R a u v q
abbrev color (x : (i:I)→pkey k e i→T i→ o k e i) :=
  orchid (condition k e) s (fun i=> (e i).shade) x
theorem blizzard
    (x : (i:I)→pkey k e i→T i→ o k e i)
    {L : I→ℕ}
    (h : ∀ i,(s i).count*((e i).shade+1)≤L i) :
    yoke k e (r:=r) (L:=L)
      (together r.header (color k e s x))
      (color k e s (fun i=>runOn (pointed false) (x i))) := by
  let sk i := dim W ^ k i
  have w0 i : 1 ≤ sk i := one_le_pow₀ d.rank
  let N := condition k e
  let M := rate k e
  let t i := (s i).count
  let δ i := excess (sk i) (t i)
  let b i := Spindle.layers (sk i) (t i)
  have gr (i) : (group R k b i).count = t i+δ i := by
    rw [group,strands]
    exact (envelope _ _ (w0 i)).1
  have hd (i) : δ i < sk i := (envelope _ _ (w0 i)).2
  let extend i l := (s i).tab (x i l) ++ List.replicate (δ i) (0:Grain _)
  let V i a := (group R k b i).untab (extend i a)
    (show (extend i a).length=_ from by rw [gr]; simp [extend,t])
  have η i z : strip (group R k b i) (Dusk.mark ∘ V i z) =
      send ((extend i z).map Dusk.mark) := by unfold strip; rw [stripe_eq', ← Series.map_tab,Series.recover]
  let γ (i:I) : QuestP (dim J) (W:=W) := ⟨k i,e i,b i,V i⟩
  have n0 : Station r N := climate (J:=J) γ a (d.large.trans' (by decide))
  let E := color k e s x
  have σ : Alive r M L E := shelter N s (fun i=>(e i).shade) x n0 h
  let MID := steam R k e b V
  have B := Spindle.growth (dim W) _ k _ (cw0 k e u) (by have := d.large; omega)
  have ζ : r.Has (tally ∘ sk) := by
    by_cases w : 2 ≤ dim W
    · exact (juge _ r k w v B).1
    rw [show sk=(fun _=>1) by funext i; simp [sk, show dim W=1 by have := d.rank; omega]]
    exact Regime.fixed _
  let ctrl i := send (heat (tally (e i).shade, tally (sk i)))
  have δ₁ := (q.pair ζ).thenDo air0
  let Q := together r.header E
  have ξ := Drive.fetch n0.1 σ
  have σx := Drive.self n0.1 σ
  have z : Rip r M L Q (stackRun N (fun i _ => ctrl i)) :=
    ξ.chain (clones n0 (fun _=> le_rfl) ctrl δ₁)
  have e0 := Rip.coalesce (s:=N) (fun i _=> ctrl i) (fun i a=> strip (s i) (Dusk.mark ∘ x i a)) z σx
  let pp i := heat (tally (e i).shade,tally (sk i))
  have prep : Rip r M L Q MID := by
    let X i := (N i).tab fun a=> (pp i,(s i).tab (Dusk.mark ∘ x i a))
    have ne : Rip r M L Q (send ∘ X) := by
      unfold stackRun at e0
      simp only [strip,stripe_eq'] at e0
      change Rip r M L Q (fun i=> stripe (N i) (fun a=> send (pp i,(s i).tab (Dusk.mark ∘ x i a)))) at e0
      simp_rw [stripe_eq'] at e0; exact e0 -- using e0
    have f := Fatigue.act (x:=X) ne _ fastForward.mapping
    unfold X at f
    unfold MID steam orchid cloth stackRun
    simp_rw [show ∀ i a,stripe (group R k b i) (fun l=> send ((Dusk.mark ∘ V i a) l))=_ from η]
    have ht (i:I) (a:pkey k e i) :
        feeder (pp i,(s i).tab (fun j=> Dusk.mark (x i a j)))=(extend i a).map Dusk.mark := by
      have e := fed ((s i).tab (x i a)) (w0 i)
      simpa only [pp,extend,t,δ,Series.card,Series.map_tab,Function.comp_def] using e
    simpa only [N,stripe_eq',Series.map_tab,Function.comp_def,ht] using f
  have pass := astern d R k e a u b V
    (p:=Q) (L:=L) (fun i=> by
      rw [gr,Nat.add_mul]; exact Nat.add_le_add (h i) (Nat.mul_le_mul_right _ (hd _).le))
    ((ξ.chain (Rip.header n0.1 a)).twice prep)

  -- transform known head part
  let V' i := runOn (pointed false) (V i)
  let x' i := runOn (pointed false) (x i)
  have eqLen (i) : t i ≤ (group R k b i).count := gr i ▸ Nat.le_add_right ..
  let idx i (a : T i) := (group R k b i).follow
    ⟨dwells (s i) a,(lt_of_lt_of_le ((s i).index a).isLt (eqLen i))⟩
  have hi i z (u:T i) : V i z (idx i u)=x i z u := by
    unfold V Series.untab idx
    simp only [Series.index_follow,extend,dwells]
    have hs : ((s i).index u).val<((s i).tab (x i z)).length := by
      rw [Series.card]; exact ((s i).index u).isLt
    simp only [List.getElem_append_left hs]
    rw [Series.get (f:=x i z) (i:=(s i).index u),Equiv.symm_apply_apply]
  have hi' i z (u:T i) : V' i z (idx i u)=x' i z u := by
    change pointed _ _ _ = pointed _ _ _
    congr 1
    exact funext fun z=> hi i z u
  let W0 := fir R k e b V
  let B0 := together W0 E
  have pe := pass.prepend E σ
  obtain ⟨ν,k0,ω⟩ := pe
  have Po := hue0 d k e
  have cut : Breeze (hue k e) r M L (together Q E) (color k e s x') := by
    let fields i a := (group R k b i).tab (Dusk.mark ∘ V' i a)
    let tmpl i a := (s i).tab (Dusk.mark ∘ x i a)
    have hv : together W0 E =
        send ∘ (fun i=> ((N i).tab (fields i),(N i).tab (tmpl i))) := by
      funext i
      simp only [W0,E,fir,steam,color,orchid,cloth,stackRun,together, Function.comp_def]
      simp_rw [stripe_eq']; rfl
    change Carries _ (together Q E) (together W0 E) at ω
    rw [hv] at ω
    have zip := ω.chain (Carries.func ω.budget ω.out (lock cutback [] []) (easy_lock _ easy_back [] []))
    have ht (i:I) (a:pkey k e i) :
        cutback (fields i a,tmpl i a)=(s i).tab (Dusk.mark ∘ x' i a) :=
      helpCut _ (group R k b i) (Dusk.mark ∘ x' i a) (Dusk.mark ∘ x i a) _ (eqLen i)
        (fun u => congrArg Dusk.mark (hi' i a u))
    refine ⟨ν,k0,?_⟩
    simp only [paired] at zip
    simp_rw [ht] at zip
    unfold color orchid cloth stackRun
    simpa only [N,stripe_eq',Function.comp_def] using zip
  exact (Breeze.launch ((Rip.alivePair (Drive.started n0.1) σ).twice σx) Po).next cut
end
end Haze

end IntegerMultiplication
end Computability
end OAI
