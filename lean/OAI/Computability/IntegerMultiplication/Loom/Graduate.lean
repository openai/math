import OAI.Computability.IntegerMultiplication.Loom.Rotor

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Loom
open Strip Code Dims Net Adic Port Strip.Optic
variable {I J W : Type} [DecidableEq J] [Fintype J] [Fintype W] {p : ℕ}
variable {k : I→ℕ} {r : Regime I} (P : (i:I)→Stair (dim J) p (k i+1))
variable (f : J≃Fin (dim J)) (R : Series W)
noncomputable section
abbrev ringArea (i:I) :=
  arrays f (line p (dim J^k i)) (P i).north (P i).isle (P i).south
abbrev fieldView (i:I) :=
  Keys (P i).north (P i).isle (P i).south J (Block p (dim J^k i))
-- spect consecutive chunk. basic setup
omit [DecidableEq J] in
theorem priority [NeZero p] (hp : 2 ≤ p) (h : r.Small (fun i => (P i).ticket)) :
    Station r (ringArea P f) := by
  let w (i:I) : Where (dim J) p Unit := ⟨k i+1, P i,0,fun _ _ => 0⟩
  have c := Where.station_t w hp h
  let e i := depthAdopt p (k i) f (P i).north (P i).isle (P i).south
  have d (i:I) : (ringArea P f i).count=(w i).plates.count := (e i).cost
  unfold Station
  simp_rw [d]
  exact c
include P in
omit [DecidableEq J] in
theorem levels (h : r.Small fun i => (P i).ticket) :
    r.Small (beacon (dim J) ∘ k) ∧ r.Has (fun i => tally (dim J^k i)) :=
  let hs := (Where.signals (fun i => k i+1) P h).2.2
  ⟨hs,Where.descendants k hs⟩
variable (hc : I → ℕ)
abbrev shaped (i:I) := skein W R (hc i) (k i)
-- allowance for local cargo width (choose arbitrary upper)
variable (l : I→ℕ) (m : ∀ i,(shaped (k:=k) R hc i).count≤l i)

def familyZone (P : (i:I) → Stair (dim J) p (k i+1)) (f : J ≃ Fin (dim J))
    (hc : I→ℕ) (i : I) (x : Where (dim J) p W) :=
  x.1=k i ∧ x.site.supplyLimit=(P i).supplyLimit ∧ x.2.cargo=hc i ∧
    x.plates.count=(ringArea P f i).count
abbrev report (P : (i:I) → Stair (dim J) p (k i+1)) (f : J ≃ Fin (dim J))
    (R : Series W) (r : Regime I) (hc : I→ℕ) (l : I→ℕ) (g : ℤ) :=
  Hopto (Where.current R) r (fun i => (ringArea P f i).count) l (familyZone P f hc) g

abbrev fuel (i : I) := Frame W (hc i) (k i)
abbrev liveData (v : (i:I)→fieldView P i→fuel (W:=W) (k:=k) hc i→Bead) :=
  cloth (ringArea P f) (shaped R hc) v
variable [NeZero p]
def drive (q : Lag J p) (h : q.legal (ranking f)) (i:I) :=
  reflect f q h (P i).north (P i).isle (P i).south (dim J^k i)
theorem freeRide (hp : 2≤p) (H : r.Small fun i => (P i).ticket)
    (q : Lag J p) (z : q.legal (ranking f)) (d : q.prices=0)
    (T : (i:I)→Type) (t : (i:I)→Series (T i)) (l : I→ℕ) (m : ∀ i,(t i).count≤l i)
    (v : (i:I)→fieldView P i→T i→Bead) :
    Drive r (fun i=>(ringArea P f i).count) l (cloth (ringArea P f) t v)
      (cloth (ringArea P f) t (fun i => travel (drive P f q z i) (v i))) := by
  let D := fun i => dim J^k i
  let O := fun i => field p (D i)
  obtain ⟨_,u⟩ := levels P H
  have hn := Told.carrier hp D u
  obtain ⟨a,b,c⟩ := Where.ticket_told (fun i => k i+1) P H
  have h := visible t v m
  cases q with
  | width x alpha =>
    exact sizeUp hp D (fun i => oneStop f x (P:=(P i).north) (G:=(P i).isle) (B:=(P i).south)) alpha u
      (hn.stair f a b x) (hn.lounge f b c x) _ h
  | gather x y alpha =>
    exact shiftUp hp D (fun i => twoStops f y x z (P:=(P i).north) (G:=(P i).isle) (B:=(P i).south)) alpha u
      (hn.stair f a b y) (hn.corridor f b y x) (hn.lounge f b c x) _ h
  | pivot _ _ => contradiction

-- one child call
variable (v : (i:I) → fieldView P i → Frame W (hc i) (k i) → Bead)
include m
omit [Fintype W] in
theorem single (hp : 2≤p) (H : r.Small fun i => (P i).ticket)
    (a b : J) :
    report P f R r hc l 1
      (together r.header (liveData P f R hc v))
      (liveData P f R hc (fun i => travel (drive P f (.pivot a b) trivial i) (v i))) := by
  let q i := infant (P i) hp f a b
  let h i := infancy (P i) hp f a b
  let C (i:I) : Where (dim J) p W :=
    ⟨k i,q i,hc i,v i ∘ (h i).cast.symm⟩
  let N i := (ringArea P f i).count
  refine {
    safe := ⟨fun i => [C i],by
      intro i x e
      rcases List.mem_singleton.mp e with rfl
      exact ⟨rfl,rfl,rfl,(h i).cost.symm⟩,
      by simp,?_⟩ }
  have s := priority P f hp H
  have hx := cloth_size _ _ s v m
  -- synthesize q.ticket
  obtain ⟨Y,y⟩ := levels P H
  let O i := field p (dim J ^ k i)
  have g := Told.carrier hp _ y
  obtain ⟨u,t,z⟩ := Where.ticket_told (fun i => k i+1) P H
  have small : r.Small (fun i => (q i).ticket) :=
    Y.pair (Regime.Has.pair ((g.stair f u t (false,a)).shape)
      (Regime.Has.pair ((g.corridor f t (false,a) (true,b)).shape) ((g.lounge f t z (true,b)).shape)))
  have produce : Rip r N l (together r.header (liveData P f R hc v)) (together (fun i => (q i).ticket)
      (liveData P f R hc v)) := (Rip.header s.1 small).left hx
  have before : together (fun i => (q i).ticket) (liveData P f R hc v) =
      (Where.current R).issue ∘ C := by
    funext i
    apply congrArg (Tree.fork (q i).ticket)
    change stripe (ringArea P f i) _ = stripe _ (fun y => strip _ (v i ((h i).cast.symm y)))
    rw [(h i).packet]
    simp [Function.comp_def]
    rfl
  have after0 : liveData P f R hc (fun i => travel (drive P f (.pivot a b) trivial i) (v i)) =
      (Where.current R).reply ∘ C := by
    funext i
    change stripe (ringArea P f i) (fun x => strip _ (v i ((drive P f (.pivot a b) trivial i).symm x))) =
      stripe _ (fun y => strip _ (v i ((h i).cast.symm (swapper _ _ _ y))))
    rw [(h i).packet]
    apply congrArg (stripe _)
    ext x
    dsimp only [Function.comp_def]
    rw [infancyAlter,Equiv.symm_apply_apply]
    rfl
  rw [before] at produce
  rw [after0]
  exact (Quest.board C s.1).hand produce

omit [Fintype W] in
theorem crossingDo (hp : 2≤p) (H : r.Small fun i => (P i).ticket)
    (q : Lag J p) (z : q.legal (ranking f)) :
    report P f R r hc l q.prices
      (together r.header (liveData P f R hc v))
      (liveData P f R hc (fun i => travel (drive P f q z i) (v i))) := by
  cases q with
  | pivot a b => exact single P f R hc l m v hp H a b
  | width a c => exact Hopto.tarry (freeRide P f hp H (.width a c) z rfl _ (shaped R hc) l m v)
  | gather a b c => exact Hopto.tarry (freeRide P f hp H (.gather a b c) z rfl _ (shaped R hc) l m v)
end
end Loom

end IntegerMultiplication
end Computability
end OAI
