import OAI.Computability.IntegerMultiplication.Packed.Column

/-! # Charged guarded XOR with an arbitrary interchange exponent

The P192 eight-turn algorithm uses a constant number of whole-chunk interchanges.
This refinement passes the interchange procedure as a parameter. The translations,
the table-driven boundary repair with radix sorting, and the final single-bit update
are the existing P192 finite stack programs. The record bounds retain the chosen
exponent on the actual width of the interchanged fields.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled

open IntegerMultiplication IntegerMultiplication.Strip IntegerMultiplication.Strip.Dims
open IntegerMultiplication.Packed IntegerMultiplication.Loom IntegerMultiplication.Adic
open IntegerMultiplication.Code IntegerMultiplication.Port IntegerMultiplication.Strip.Optic
open IntegerMultiplication.Packed.Pos

noncomputable section

/-- Physical rectangular interchange, with coincident extents and arbitrary finite spectators. -/
def RectInterchange {X : Type} (r : Regime X) (n : X → ℕ) (ρ : ℝ) : Prop :=
  ∀ (P G B : X → Tape), r.Has (tally ∘ n) → Told r P → Told r G → Told r B →
    (∀ i j, j ∈ P i ++ G i ++ B i → j ≤ Net.Shuttle.base) →
    ∀ (L : X → ℕ) {T : X → Type} (u : (i : X) → Series (T i)), (∀ i, (u i).count ≤ L i) →
    ∀ v : (i : X) → SpanKey (P i) (G i) (B i) (Block 2 (n i)) → T i → Bead,
      let s i := stock 2 (P i) (G i) (B i) (n i)
      Breeze (Spindle.modes n (τ := ρ)) r (fun i => (s i).count) L
        (together r.header (cloth s u v))
        (cloth s u fun i x => v i (swapper _ _ _ x))

theorem p192_rectInterchange {X : Type} (r : Regime X) (n : X → ℕ) :
    RectInterchange r n Net.Motif.sigma :=
  fun P G B h hp hg hb bound L _ u z v =>
    Spindle.rectBead P G B n h hp hg hb bound L u z v

variable {X : Type} (P G R S : X → Tape) (H L i : X → ℕ) {r : Regime X}
variable (ρ : ℝ) (hρ : 0 ≤ ρ)
variable (sw : RectInterchange r (extent H L i) ρ)
variable (hP : Told r P) (hG : Told r G) (hR : Told r R) (hS : Told r S)
variable (h : r.Has fun x => signs (H x) (L x) (i x)) (c : r.Has (tally ∘ extent H L i))
variable (guard : ∀ x a, a ∈ P x ++ G x ++ R x ++ S x → a ≤ Net.Shuttle.base)
variable {l : X → ℕ} {U : X → Type} (u : (x : X) → Series (U x)) (z : ∀ x, (u x).count ≤ l x)

abbrev Stage (e : ∀ x, Equiv.Perm (Plate (H x) (L x) (i x))) :=
  ∀ f : (x : X) → Addr P G R S H L i x → U x → Bead,
    Breeze (Spindle.modes (extent H L i) (τ := ρ)) r (rate P G R S H L i) l
      (together r.header (cloth (Series0 P G R S H L i) u f))
      (cloth (Series0 P G R S H L i) u fun x => travel (invoke (e x) ..) (f x))

include hP hG hR hS c z guard sw

private theorem exchange (s : Pos) (t : s ≠ moon) :
    Stage P G R S H L i ρ (r := r) (l := l) u
      (fun _ => arrange (Equiv.swap s moon)) := by
  intro f
  let a := Series0 P G R S H L i
  let N (x:X) := cap (i x) (H x) (L x)
  let P' := fun x=> broad (P x) (G x) (H x) (L x) (i x) s
  let G' := fun x=> cross (G x) (R x) (H x) (L x) (i x) s
  let B' x := ([]:Tape) ++ S x
  let v (x:X) := (barrier (P x) (G x) (R x) (S x) (H x) (L x) (i x) s t)
  have hv := Told.carrier (q:=2) (by decide) N c
  have w := sw P' G' B'
    c (show Told r P' from ?_) (show Told r G' from ?_) ((Told.nil).append hS) (fun x n e => ?_) l u z (fun (x:X) b => f x ((v x).view.cast.symm b))
  · have eq (x) : rate P G R S H L i x =
        (stock 2 (P' x) (G' x) (B' x) (N x)).count := (v x).view.cost
    rw [funext eq]
    have p : cloth (fun x => stock 2 (P' x) (G' x) (B' x) (N x)) u
        (fun x b => f x ((v x).view.cast.symm b)) = cloth a u f := by
      unfold cloth stackRun; funext x
      erw [(v x).view.packet]
      apply congrArg (stripe (a x)); funext b
      change strip (u x) (f x ((v x).view.cast.symm ((v x).view.cast b)))=_
      rw [Equiv.symm_apply_apply]
    dsimp only at w
    rw [p] at w
    unfold cloth stackRun at *
    have q : (fun x => stripe (stock 2 (P' x) (G' x) (B' x) (N x))
        fun b => strip (u x) (f x ((v x).view.cast.symm (swapper _ _ _ b))))
        =
        (fun x => stripe (a x) (fun b =>
          strip (u x) (travel (invoke (arrange (Equiv.swap s moon)) _ _ _ _) (f x) b))) := by
      funext x
      erw [(v x).view.packet]
      apply congrArg (stripe _); funext b
      change strip (u x) (f x _) = strip (u x) (f x _)
      rw [gone,arrange_symm,show ((Equiv.swap s moon).symm) = Equiv.swap s moon from rfl]
      rw [← barrier_main (P x) (G x) (R x) (S x) b s t]
      rfl
    exact (q ▸ (show Breeze _ _ _ _ (fun x => _) (fun x => stripe (stock 2 (P' x) (G' x) (B' x) (N x))
        fun b => strip (u x) (f x ((v x).view.cast.symm (swapper _ _ _ b)))) from w))
  · cases s with
    | sun => exact hP.append Told.nil
    | _ => exact hP.append (hv.append (hG.append Told.nil))
  · cases s with
    | noon => exact (Told.nil).append (hR.append Told.nil)
    | _ => exact (Told.nil).append (hG.append (hv.append (hR.append Told.nil)))
  have ve := ivory (p:=2) (by decide) (j:=N x)
  by_contra g
  have hl (d : n∈P x ∨ n∈G x ∨ n∈R x ∨ n∈S x) := g (guard x n (by simp; tauto))
  have hd (q : n∈field 2 (N x)) := (g ((ve n q).2.trans Net.Shuttle.base_large.le))
  cases s <;> simp [P',G',B',broad,cross] at e
  all_goals tauto

omit sw guard in
include hρ in
private theorem follow (q : Equiv.Perm Pos) :
    Stage P G R S H L i ρ (r:=r) (l:=l) u (fun _ => agent q (Equiv.refl _)) := by
  intro v
  let s := port P G R S H L i hP hG hR hS c
  have us := Spindle.belly (extent H L i) hρ
  simp_rw [agent_id]
  exact Breeze.launch (Drive.self s.1 (cloth_size _ u s v z)) us

omit sw guard in
private theorem job_pipe {m n} (a : Stage P G R S H L i ρ (r:=r) (l:=l) u m)
    (b : Stage P G R S H L i ρ (r:=r) (l:=l) u n) :
    Stage P G R S H L i ρ (r:=r) (l:=l) u (fun x=> (m x).trans (n x)) :=
  fun f =>
    let s := port P G R S H L i hP hG hR hS c
    have h := a f
    have g := b (fun x=>travel (invoke (m x) ..) (f x))
    Spindle.Breeze.pipe h g (Drive.fetch s.1 (cloth_size _ u s f z))

include h
omit sw guard in
include hρ in
private theorem second (t : Turn) (ht : t∈Packed.order)
    (q : Pos ≃ Pos) (doneR : q (target t)=.moon) :
    Stage P G R S H L i ρ (r:=r) (l:=l) u (fun _ => agent q (walk t)) := by
  have tR : t.shift=1 ∨ t.shift=-1 := by
    simp only [Packed.order,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with kk|kk|kk|kk|kk|kk|kk|kk <;> subst t <;> decide
  intro v
  have hx := straight P G R S H L i hP hG hR hS c h _ (visible u v z)
    q t tR doneR
  exact Breeze.launch hx (Spindle.belly (extent H L i) hρ)

include hρ
private theorem weather (t : Turn) (ht : t∈Packed.order) (q : Pos≃Pos) :
    Stage P G R S H L i ρ (r:=r) (l:=l) u (fun _ => agent q (walk t)) := by
  by_cases e : q (target t)=.moon
  · exact second P G R S H L i ρ hρ hP hG hR hS h c u z t ht q e
  let E := Equiv.swap (q (target t)) Pos.moon
  have e0 : (q.trans E) (target t)=.moon := by simp [E]
  have hx := second P G R S H L i ρ hρ hP hG hR hS h c u z t ht (q.trans E) e0
  have w : Stage P G R S H L i ρ (r:=r) (l:=l) u (fun x => arrange E) := fun v =>
    exchange P G R S H L i ρ sw hP hG hR hS c guard u z (q (target t)) e v
  have k := job_pipe P G R S H L i ρ hP hG hR hS c u z (job_pipe P G R S H L i ρ hP hG hR hS c u z w hx) w
  have d (x:X) :
      ((arrange E).trans (agent (q.trans E) (walk (H:=H x) (L:=L x) (i:=i x) t))).trans (arrange E)=agent q (walk t) :=
    conjugate q E _
  simpa only [d] using k

theorem touring (q : Pos≃Pos) :
    Stage P G R S H L i ρ (r:=r) (l:=l) u (fun _x=> agent q (cruise Packed.order)) := by
  suffices hz : ∀ t : List Turn,(∀ v∈t,v∈Packed.order) → Stage P G R S H L i ρ (r:=r) (l:=l) u (fun x=> agent q (cruise t)) from hz _ (fun _=>id)
  intro t e
  induction t with
  | nil => exact follow P G R S H L i ρ hρ hP hG hR hS c u z q
  | cons a t ih =>
    have g := job_pipe P G R S H L i ρ hP hG hR hS c u z
      (weather P G R S H L i ρ hρ sw hP hG hR hS h c guard u z a (e _ List.mem_cons_self) q)
      (ih (fun x m=>e _ (List.mem_cons_of_mem _ m)))
    simpa only [agent_con,cruise] using g

omit sw guard hρ in
include h hρ in
/-- The local bit update is independent of the command used for whole-chunk interchange. -/
theorem plateEndBit (p : Equiv.Perm Pos) :
    Stage P G R S H L i ρ (r:=r) (l:=l) u (fun _x=> agent p streak) := by
  intro f
  let q (x:X) := fileAcross (P x) (G x) (R x) (S x) (H x) (L x) (i x)
  have b :=
    letI : (x:X) → DecidableEq (Addr P G R S H L i x) := fun _=>Classical.decEq _
    letI : (x:X) → Fintype (Addr P G R S H L i x) := fun _=>inferInstance
    letI : (x:X) → Fintype (kept (P x) (G x) (R x) (S x) (H x) (L x) (i x)) := fun _=>inferInstance
    localAction q (agent p xor) _ (visible u f z) (supervisor P G R S H L i hP hG hR hS h c)
  have hx := Breeze.launch b (Spindle.belly _ hρ :
    ∀ x, 1≤ Spindle.modes (extent H L i) (τ := ρ) x)
  unfold  stackRun at hx -- then rewrite Optic
  unfold Strip.Optic.travel at *
  have e :
      (fun (a:X) (x:Addr P G R S H L i a)=> strip (u a)
        (f a ((Strip.Optic.field (q a).focus (agent p xor)).symm x))) =
        fun a x=> strip (u a) (f a ((invoke (agent p streak) ..).symm x)) := by
    funext a x
    apply congrArg _
    apply congrArg _
    exact fed _ _
  change Breeze _ _ _ _ _ (fun a=> stripe _ (fun x => strip _ (f a ((Strip.Optic.field (q a).focus (agent p xor)).symm x)))) at hx
  simp_rw [congrFun (congrFun e _) _] at hx -- need correct simp
  exact hx

variable (spar : ∀ x, (3*extent H L i x+1)*(32*i x) ≤ 2^width (H x) (L x))

include hP hG hR hS h c z guard spar
attribute [local irreducible] Packed.order
set_option maxRecDepth 2000 in
private theorem sealed (p : Equiv.Perm Pos) :
    Stage P G R S H L i ρ (r:=r) (l:=l) u (fun _x=> agent p move) := by
  have U :
      Stage P G R S H L i ρ (r:=r) (l:=l) u (fun x=> agent p repair) :=
    fun v => Breeze.launch (shower P G R S H L i hP hG hR hS h c spar u z v p)
      (Spindle.belly (extent H L i) hρ)
  have cp (m n : (x:X) → Equiv.Perm (Plate (H x) (L x) (i x))) (M : Stage P G R S H L i ρ (r:=r) (l:=l) u (fun x=>agent p (m x)))
      (N : Stage P G R S H L i ρ (r:=r) (l:=l) u (fun x=>agent p (n x))) :
      Stage P G R S H L i ρ (r:=r) (l:=l) u (fun x=>agent p ((m x).trans (n x))) := by
    have h0 := port P G R S H L i hP hG hR hS c
    intro f
    let v x := travel (invoke (agent p (m x)) (P x) (G x) (R x) (S x)) (f x)
    have e := Spindle.Breeze.pipe (M f) (N v) (Drive.fetch h0.1 (cloth_size _ _ h0 f z))
    let T x := (agent p (m x)).trans (agent p (n x))
    suffices eq : (fun x => agent p ((m x).trans (n x)))=T by rw [eq]; exact e
    funext x
    exact (agent_con ..).symm
  have eq (H L i : ℕ) : (cruise Packed.order).trans (repair (H:=H) (L:=L) (i:=i))=ideal := by
    ext x : 1; simp only [repair,Equiv.trans_apply,Equiv.symm_apply_apply]
  let f (x:X) := cruise (H:=H x) (L:=L x) (i:=i x) Packed.order
  let g (x:X) := repair (H:=H x) (L:=L x) (i:=i x)
  let m (x:X) := ideal (H:=H x) (L:=L x) (i:=i x)
  have V : Stage P G R S H L i ρ (r:=r) (l:=l) u (fun x => agent p (m x)) := by
    have e : m=(fun x=> (f x).trans (g x)) := funext (fun _=> (eq ..).symm)
    rw [e]
    exact cp f g (touring P G R S H L i ρ hρ sw hP hG hR hS h c guard u z p) U
  exact cp m _ V (plateEndBit P G R S H L i ρ hρ hP hG hR hS h c u z p)


include hP hG hR hS h c z guard spar
theorem guardedXor (q : Equiv.Perm Pos)
    (f : (x:X)→Dome (P x) (G x) (R x) (S x) (slot (H x) (L x) (i x))→U x→Bead) :
    let s := enable P G R S H L i
    Breeze (Spindle.modes (extent H L i) (τ := ρ)) r (fun i=>(s i).count) l (together r.header (cloth s u f))
      (cloth s u fun x=> Strip.Optic.travel (invoke (agent q plusRow) ..) (f x)) := by
  let b x := build0 (P x) (G x) (R x) (S x) (H x) (L x) (i x)
  let v (x:X) := f x ∘ (b x).cast.symm
  have g := sealed P G R S H L i ρ hρ sw hP hG hR hS h c guard u z spar q v
  have e (x:X) : rate P G R S H L i x = (enable P G R S H L i x).count := (b x).cost.symm
  dsimp only
  simp_rw [← e]
  suffices a : cloth (Series0 P G R S H L i) u v=cloth (enable P G R S H L i) u f ∧
      cloth (Series0 P G R S H L i) u (fun x=> travel (invoke (agent q move) ..) (v x))
      = cloth (enable P G R S H L i) u (fun x=> travel (invoke (agent q plusRow) ..) (f x)) by
    change Breeze _ _ _ _ _ (cloth _ u (fun x => travel (invoke (agent q move) ..) (v x))) at g
    rw [a.1] at g
    erw [a.2] at g
    exact g
  constructor <;> funext x <;>
    change stripe _ _=stripe (enable P G R S H L i x) _ <;>
    erw [(b x).packet] <;>
    apply congrArg (stripe _) <;> funext a
  · change strip (u x) (f x ((b x).cast.symm ((b x).cast a)))=_
    rw [Equiv.symm_apply_apply]
  change strip (u x) (f x ((b x).cast.symm ((invoke (agent q move) ..).symm ((b x).cast a))))=_
  erw [appear a q]
  rfl
end
end Controlled

end NearSquareRoot
end Computability
end OAI
