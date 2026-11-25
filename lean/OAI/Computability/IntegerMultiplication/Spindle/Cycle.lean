import OAI.Computability.IntegerMultiplication.Spindle.Parcel

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Spindle
open Strip Dims Code Loom Adic
variable {I J W L : Type} [DecidableEq J] [Fintype J] [Fintype W] {p D : ℕ} [NeZero p] {τ : ℝ}
noncomputable section

variable (D p) -- introduced implicit?
-- worklists. avoid Type-param payload in speculation, choose payload List Bead uniform width via Fin length.
structure Craft (D p : ℕ) (l : List Tally) where
  span : Bounds D p l
  count : ℕ
  port : span.sector→Fin count→Bead
variable {D p}
abbrev Hull (D p : ℕ) := Sigma (Craft D p)
abbrev Hull.plan (x : Hull D p) := x.1
abbrev Hull.scope (x : Hull D p) := x.2.span
abbrev Hull.width (x : Hull D p) := x.2.count
abbrev Hull.load (x : Hull D p) := x.2.port
abbrev Hull.head (x : Hull D p) := send x.scope.mint
abbrev Hull.rate (x : Hull D p) := (x.scope.sectorS).count
def regime (d : 2≤D) : Regime (Hull D p) :=
  ⟨fun i => i.scope.scale,Hull.head,⟨1,4*p+13,fun i => by rw [pow_one]; exact i.scope.sized d⟩⟩
def codeChart (D p) : Job (Hull D p) where
  issue i := .fork i.head (stripe i.scope.sectorS fun a => strip (Series.natural i.width) (i.load a))
  reply i := stripe i.scope.sectorS (fun a => strip (Series.natural i.width)
    (i.load (swapper _ _ _ a)))

variable (hp : 2≤p)
-- dependent geometry notation
abbrev Shell (D p) := Σ a : Tally, Σ l : List Tally, Craft D p (a::l)
abbrev Shell.clip (s : Shell D p) : Hull D p := ⟨s.1::s.2.1,s.2.2⟩
abbrev Shell.g (s : Shell D p) := s.clip.scope
abbrev Shell.l (s : Shell D p) := s.2.1
abbrev Shell.h (s : Shell D p) := s.1.length
abbrev Shell.chunk (s : Shell D p) := D^s.h
abbrev Shell.rest (s : Shell D p) := volume D s.l
abbrev Shell.closed_ (s : Shell D p) :=
  closed p s.chunk s.rest s.g.P s.g.G s.g.B
abbrev Shell.outer (s : Shell D p) :=
  outside p s.chunk s.rest s.g.P s.g.G s.g.B
abbrev Shell.inner (s : Shell D p) :=
  inside p s.chunk s.rest s.g.P s.g.G s.g.B
abbrev Shell.first (s : Shell D p) :=
  opA p s.chunk s.rest s.g.P s.g.G s.g.B
abbrev Shell.last (s : Shell D p) :=
  opB p s.chunk s.rest s.g.P s.g.G s.g.B

def Shell.advance (s : Shell D p) (hp : 2≤p) : Hull D p :=
  ⟨s.l,s.g.retreat hp,s.clip.width,
    s.clip.load ∘ s.closed_.cast ∘ s.first ∘ s.inner.cast.symm⟩
include hp
omit [NeZero p] in
theorem returned (s : Shell D p) :
    (codeChart D p).reply (s.advance hp) = (codeChart D p).reply s.clip := by
  -- Adopt packet cyclic rotation
  change stripe (stock p _ _ _ _) (fun a => strip _ (_) ) = stripe (stock p _ _ _ _) _
  erw [s.inner.packet,s.closed_.packet]
  apply congrArg (stripe _)
  funext v
  change strip _ (s.clip.load (s.closed_.cast (s.first (s.inner.cast.symm (swapper _ _ _ (s.inner.cast v)))))) =
    strip _ (s.clip.load (swapper _ _ _ (s.closed_.cast v)))
  erw [← closed_keep,← in_keep,Equiv.symm_apply_apply]
  rfl
omit [NeZero p] in
theorem landing (s : Shell D p) :
    (s.advance hp).rate=s.clip.rate ∧ (s.advance hp).width=s.clip.width ∧
    (s.advance hp).scope.scale=s.clip.scope.scale :=
  ⟨s.inner.cost.symm.trans s.closed_.cost, rfl,rfl⟩

variable (R : Series W) (d : Design J W L p τ)

abbrev peak (s : Hull D p) : ℕ :=
  (s.plan.headD []).length
include R
theorem drive (t : 0≤τ) :
    let F := gust (peak (D:=dim J) (p:=p)) (dim J) τ
    let J0 := codeChart (dim J) p
    let G := regime (p:=p) d.occupancy
    let k := Shell.clip (D:=dim J) (p:=p)
    Breeze (F ∘ k) (G.pull k) (Hull.rate ∘ k) (Hull.width ∘ k)
      (J0.issue ∘ k) (J0.issue ∘ fun x => x.advance hp) := by
  let X := Shell (dim J) p
  let r := (regime (p:=p) d.occupancy).pull (Shell.clip:X→_)
  let sr := Shell.g (D:=dim J) (p:=p)
  let P := fun i:X => (sr i).narrow hp
  let a := Sigma.fst (α:=Tally) (β:=fun a => Σ l:List Tally, Craft (dim J) p (a::l))
  let l := fun i:X => i.clip.width
  let J0 := codeChart (dim J) p
  have m : r.Has fun i:X => (sr i).mint := Regime.self
  have e : Dom r.scale fun i:X => (sr i).scale := Dom.base _
  obtain ⟨y,g,b⟩ := Bounds.inside_s hp d.occupancy sr m e
  have fL : r.Has (tally ∘ (Shell.h:X→ℕ)) := by simpa only [Function.comp_def,recover_tally] using y
  let v := fun i:X => i.clip.load ∘ i.closed_.cast ∘ i.outer.cast.symm
  let T := fun i:X => Series.natural (l i)
  have pass := silver (R:=R) (d:=d) (Shell.h:X→ℕ) P T (l:=l) v g t fL e (by simp [T])
  let Z := fun i:X => src (Shell.h:X→ℕ) P i
  have u : (∀ i:X,i.clip.rate = (Z i).count) := fun i =>
    i.closed_.cost.symm.trans i.outer.cost
  have right : copies Shell.h P T (fun i:X => v i ∘ swapper _ _ _) = fun i:X =>
      stripe (i.advance hp).scope.sectorS fun w => strip (T i) ((i.advance hp).load w) := by
    funext i
    change stripe (stock p _ _ _ _) _ = stripe (stock p _ _ _ _) _
    erw [i.outer.packet, i.inner.packet]
    apply congrArg (stripe _)
    funext j
    change strip (T i) (i.clip.load (i.closed_.cast (i.outer.cast.symm (swapper _ _ _ (i.outer.cast j))))) =
      strip (T i) (i.clip.load (i.closed_.cast (i.first (i.inner.cast.symm (i.inner.cast j)))))
    rw [← out_keep,Equiv.symm_apply_apply,Equiv.symm_apply_apply]
  have left : together r.header (copies Shell.h P T v) = J0.issue ∘ Shell.clip := by
    funext i
    apply congrArg (Tree.fork i.clip.head)
    change stripe (stock p _ _ _ _) _ = stripe (stock p _ _ _ _) _
    erw [i.outer.packet, i.closed_.packet]
    apply congrArg (stripe _)
    funext j
    change strip (T i) (i.clip.load (i.closed_.cast (i.outer.cast.symm (i.outer.cast j)))) =
      strip _ (i.clip.load (i.closed_.cast j))
    rw [Equiv.symm_apply_apply]
  erw [right,left] at pass
  have ft := Bounds.opened sr hp d.occupancy m e -- order?
  let N := Hull.rate ∘ (Shell.clip : X → _)
  have hv := cloth_size (l:=l) (fun i:X => i.clip.scope.sectorS) T ft (fun i => i.clip.load) (by simp [T])
  have e1 := Rip.header (r:=r) (l:=l) (n:=N) ft.1 Regime.self
  let h := Rip.split (Rip.alivePair e1 hv) |>.1
  rw [show N=(fun i => (Z i).count) from funext u] at h -- hb n uses
  change Breeze (gust (Shell.h:X→_) (dim J) τ) r N l _ _
  rw [show N=(fun i => (Z i).count) from funext u]
  exact (Breeze.launch (h.chain (Rip.header (fun i => u i ▸ ft.1 i) b)) pass.1).pair pass
end
end Spindle

end IntegerMultiplication
end Computability
end OAI
