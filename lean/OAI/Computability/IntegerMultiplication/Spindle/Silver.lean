import OAI.Computability.IntegerMultiplication.Spindle.Power

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Spindle
open Code Strip Adic Dims Loom
variable {I J W L : Type} [Fintype J] [DecidableEq J] [Fintype W] {p : ℕ} [NeZero p]
variable {τ : ℝ} {r : Regime I} (k : I→ℕ) (s : (i:I)→Stair (dim J) p (k i))
variable (R : Series W) (d : Design J W L p τ) {A : I→Type} (t : (i:I)→Series (A i))
variable {l : I→ℕ}
variable (v : (i:I)→Key k s i→A i→Bead)

noncomputable section
def excess (n L : ℕ) := alignment (n-1) (tally L)
def layers (n L : ℕ) := (L+excess n L)/n
theorem envelope (n L : ℕ) (h : 1≤n) :
    layers n L*n = L+excess n L ∧ excess n L<n := by
  have e := aligned (n-1) (tally L)
  rw [Nat.sub_add_cancel h,tally_length] at e
  exact ⟨Nat.div_mul_cancel e.2, lt_of_le_of_lt e.1 (by omega)⟩
def cover (v : Tally × List Bead) :=
  v.2 ++ fill (0:Bead)
    (dial (ruler v.2,v.1.tail))
theorem easy_cover : Easy cover := by
  have z : Easy (fun y:Tally×List Bead => dial (ruler y.2,(cutLists (tally 1,y.1)).2)) :=
    (Easy.pair (Easy.ruler Easy.snd)
      (easy_cut ((Easy.const _).pair Easy.fst)).sndCompose).compose easy_dial
  have e : (fun x:Tally => (cutLists (tally 1,x)).2) = (fun x => x.tail) := by
    ext x : 1
    cases x <;> rfl
  have j : Easy (fun y:Tally×List Bead => dial (ruler y.2,y.1.tail)) := by
    -- cases eq
    simpa only [show ∀ x:Tally,(cutLists (tally 1,x)).2=x.tail from congrFun e] using z
  exact (Easy.pair Easy.snd (easy_fill _ j)).compose Easy.append

theorem cover_eq (n : ℕ) (_e : 1≤n) (l : List Bead) :
    cover (tally n,l) = l ++ List.replicate (excess n l.length) 0 := by
  rw [cover,fill_eq]
  have hx : ruler l=tally l.length := by simp [ruler,tally]
  rw [dial]
  dsimp only
  rw [hx,tally_length]
  simp [excess]

variable (e : r.Small fun i => (s i).ticket)
-- this is POWER width algorithm, assumes ticket available. Controller W^k generated additionally.
abbrev copies (v : (i:I)→Key k s i→A i→Bead) := cloth (src k s) t v
include d e R
theorem silver (u : 0≤τ) (g : r.Has (tally ∘ k))
    (hw : Dom r.scale (fun i => (s i).supplyLimit))
    (h : ∀ i,(t i).count ≤ l i) :
    Breeze (gust k (dim J) τ) r (headcount k s) l
      (together r.header (copies k s t v)) (copies k s t (fun i => v i ∘ swapper _ _ _)) := by
  have hd : Dom r.scale (fun i => dim J^k i) :=
    hw.mono (fun i => by have := (s i).lock; omega)
  let w i := dim W ^ k i
  have h0 i : 1 ≤ w i := one_le_pow₀ d.roles
  have t0 := growth (dim W) r.scale k (dim J) hd d.occupancy
  have ht : r.Has (tally ∘ w) := by
    by_cases z : 2≤dim W
    · exact (juge _ r _ z g t0).1
    have m : w=fun _ => 1 := by
      have := d.roles
      ext i; simp [w, show dim W=1 by omega]
    rw [m]; exact Regime.fixed _
  let L i := (t i).count
  let c i := layers (w i) (L i)
  have len (i) : (skein W R (c i) (k i)).count=L i+excess (w i) (L i) := by
    rw [strands]; exact (envelope (w i) _ (h0 i)).1 -- invalid syntax
  have hc i (a : Key k s i) :
      (cover (tally (w i),(t i).tab (v i a))).length = (skein W R (c i) (k i)).count := by
    simp only [cover_eq _ (h0 _),List.length_append,List.length_replicate,Series.card,len,L]
  let V i (a : Key k s i) := (skein W R (c i) (k i)).untab (cover
    (tally (w i),(t i).tab (v i a))) (hc i a)
  have de i a : strip (skein W R (c i) (k i)) (V i a) = send (cover
    (tally (w i),(t i).tab (v i a))) := by unfold strip; rw [stripe_eq',Series.recover]
  let x i : Where (dim J) p W := ⟨k i,s i,c i,V i⟩
  have ft := Where.station_t x d.large e
  change Station r (src k s) at ft
  let A := src k s
  let N := headcount k s
  let X := copies k s t v
  have ve : Alive r N l X := cloth_size _ _ ft v h
  let Q := together r.header X
  have iq : Drive r N l X X := Drive.self ft.1 ve
  have ih := Drive.fetch ft.1 ve
  have pe : Rip r N l Q (stackRun A (fun i _ => send (tally (w i)))) := ih.chain (clones ft (fun _ => le_rfl) _ ht)
  have z := Rip.coalesce (s:=A) _ _ pe iq
  have input : Rip r N l Q (packed k s R c V) := by
    change Rip r N l Q (stackRun A (fun i x => strip _ (V i x)))
    have zz : Rip r N l Q (send ∘ fun i => (A i).tab (fun a => (tally (w i), (t i).tab (v i a)))) := by
      change Rip r N l Q (stackRun A fun i => together _ (fun x => strip (t i) (v i x))) at z
      unfold stackRun at z
      simp only [strip,stripe_eq'] at z
      change Rip r N l Q (fun i => stripe (A i) (fun x => send (tally (w i),(t i).tab (v i x)))) at z
      simpa only [stripe_eq',Function.comp_def] using z
    have := Loom.Fatigue.act zz (List.map cover) easy_cover.mapping
    unfold stackRun
    simp_rw [de]
    simpa only [stripe_eq',Series.map_tab,Function.comp_def] using this
  have swell := Loft k s R d c V (l:=l)
    (fun i => by
      change c i*w i ≤ _
      have y := (envelope (w i) (L i) (h0 i))
      exact y.1.le.trans (Nat.add_le_add (h i) y.2.le))
    e t0 hw u ((ih.chain (Rip.header ft.1 e)).twice input)
  -- preserve original, trim post by matching currents lengths
  let Y i x := v i (swapper _ _ _ x)
  let H := packed k s R c (fun i => V i ∘ swapper _ _ _)
  have ht0 := swell.prepend X ve -- Q and X both available
  let X0 i x := (t i).tab (v i x)
  let H0 i x := cover (tally (w i),(t i).tab (Y i x))
  have pH : H = stackRun A fun i x => send (H0 i x) := by
    funext i; apply congrArg (stripe (A i)); funext a
    exact de _ _
  have pX : X = stackRun A fun i x => send (X0 i x) := by
    funext i; apply congrArg (stripe (A i)); funext a
    exact stripe_eq' ..
  obtain ⟨k0,m,z⟩ := ht0
  have expand := z.chain (zipper A _ _ (Carries.idles z.budget z.out) :
    Carries _ (together H X) (stackRun A fun i x =>
      together (fun x => strip (skein W R (c i) (k i)) (V i (swapper _ _ _ x))) (fun x => strip (t i) (v i x)) x))
  let Y0 i x := (t i).tab (Y i x)
  let strips (i:List Bead × List Bead) := (cutLists (ruler i.2,i.1)).1
  have es : Easy strips := (easy_cut ((Easy.ruler Easy.snd).pair Easy.fst)).fstCompose
  have hu : ∀ i a,strips (H0 i a,X0 i a) = Y0 i a := by
    intro i a; simp [strips,cutLists,H0,X0,Y0,cover_eq _ (h0 _)]
    -- List.take left, Y length
  let y (i:I) := (A i).tab (fun x => (H0 i x,X0 i x))
  have er : Carries (runrate (gust k (dim J) τ) r N l m) (together Q X) (send ∘ y) := by
    unfold stackRun at expand
    simp_rw [de] at expand -- no match under lambda?
    simp only [strip,stripe_eq'] at expand
    change Carries _ _ (fun i => stripe (A i) (fun x => send (H0 i x,X0 i x))) at expand
    simpa only [y,stripe_eq',Function.comp_def] using expand
  have massy := er.chain (Carries.func er.budget (h:=er.out) (List.map strips) es.mapping)
  have hx : Breeze _ r N l (together Q X) (copies k s t Y) :=
    ⟨k0,m,by
      unfold y at massy
      unfold copies cloth stackRun
      -- map
      simpa only [stripe_eq',Series.map_tab,Function.comp_def,hu,Y0] using massy⟩
  have feed := (Rip.alivePair (Drive.started (l:=l) (r:=r) ft.1) ve).twice iq
  exact (Breeze.launch feed (mild k (dim J) (by have := d.occupancy; omega) u)).next hx
end
end Spindle

end IntegerMultiplication
end Computability
end OAI
