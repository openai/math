import OAI.Computability.IntegerMultiplication.Phase.Coast

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Phase
open Net Net.Walsh Net.Tensor Strip Strip.Optic Strip.Dims Code Packed Loom Dusk
open Matrix Finset
variable {p v : Tape} {h g w : ℕ} {A : Type}
-- two element base case math
noncomputable section
def pls : Equiv.Perm (Addr (Fin 1)) where
  toFun x i := x i+1
  invFun x i := x i+1
  left_inv x := by ext i; exact (show ∀ a: Walsh.B,a+1+1=a by decide) (x i)
  right_inv x := by ext i; exact (show ∀ a: Walsh.B,a+1+1=a by decide) (x i)

theorem heard_r {R : Type} [CommRing R] (c : Quarter R) :
    allC (J:=Fin 1) c (fun _=>false) = kernel c false (fun _=>1) := by
  ext x y
  simp only [kernel,allC,Walsh.A,Walsh.shade,of_apply,Matrix.add_apply,Matrix.smul_apply,Matrix.one_apply,
    Tensor.app, smul_eq_mul]
  rw [Fintype.prod_unique]
  have n x y : (x:Addr (Fin 1)) = y ↔ x 0=y 0 :=
    ⟨fun e => congrFun e 0,fun e=>funext fun i=>by rwa [Subsingleton.elim i (0:Fin 1)]⟩
  -- default i =0
  simp only [n]
  change (if x 0=y 0 then _ else _) =
    _* (if x 0=y 0 then 1 else 0)+_*(if y 0=x 0+1 then 1 else 0)
  by_cases e : x 0=y 0 <;> simp [e,show ∀ a b:B,b=a+1 ↔ a≠b by decide]
def xchg := Strip.Optic.field (target p v h g (Fin 1)) pls

theorem bud (x : Base p v (Screen h g (Fin 1)) → A → Grain w) (i) (a) :
    runOn (pointed false) x i a =
      (gaunt w).glaze false*x i a + (gaunt w).streak false*travel xchg x i a := by
  unfold runOn pointed operate everywhere beamAll Optic.attach
  rw [heard_r]; dsimp only; rw [kernel_at]
  unfold travel xchg Strip.Optic.field fiber
  simp only [Function.comp_apply,Equiv.symm_trans_apply,Equiv.symm_symm,
    Prod.mk.eta, Equiv.symm_apply_apply]
  rfl

-- Rig File normalized
abbrev Lot p v h g := Base p v (Chunk h g)
abbrev pack_lot p v h g := order p v (chunks h g)
private def normT (P V : Tape) (H G : ℕ) : Adopt (plain P V H G 1) (pack_lot P V H G) :=
  let X := chunks H G
  let Z : Adopt (Track X 1) X :=
    ((Loom.step X 0).thenDo ((Adopt.same X).split (sealZero X))).thenDo (Adopt.skip X)
  (Adopt.same _).split (Z.split (Adopt.same _))
abbrev locH h g :=
  ((layout (Adic.field 2 h)).cart Series.one).cart (layout (Adic.field 2 g))
def pinC (H G : ℕ) := ((File.shade (Adic.line 2 H)).unite
  (File.look (Series.natural 2))).unite (File.shade (Adic.line 2 G))
def pic (p v : Tape) h g :=
  (File.shade (layout p)).unite ((pinC h g).unite (File.shade (layout v)))
abbrev Tiny := Unit × ((Unit × Fin 2) × Unit) × Unit
abbrev lamp (x : Chunk h g) : Tiny := ((),(((),x.1.2),()),())
def switch_ : Equiv.Perm Tiny where
  toFun x := ((),(((),x.2.1.1.2+1),()),())
  invFun x := ((),(((),x.2.1.1.2+1),()),())
  left_inv := by decide
  right_inv := by decide
def sce := Strip.Optic.field (pic p v h g).focus switch_

theorem dwarf (x : Base p v (Screen h g (Fin 1))) :
    (normT p v h g).cast (xchg.symm x) = (sce (p:=p) (v:=v) (h:=h) (g:=g)).symm ((normT p v h g).cast x) := rfl

variable {I : Type} {r : Regime I} (H G : I→ℕ) (p v : I→Tape)
private theorem initF (u : r.Has (tally ∘ H)) (e : r.Has (tally ∘ G))
    (f : Told r p) (w : Told r v) :
    Strip.Trace r (fun i=>pack_lot (p i) (v i) (H i) (G i))
      (fun _ x=> send (lamp x.2.1)) := by
  have c : Station r (fun i=>Adic.line 2 (H i)) := Adic.terminal (by decide) _ u
  have d : Station r (fun i=>Adic.line 2 (G i)) := Adic.terminal (by decide) _ e
  let S := Series.natural 2
  have hS : 1≤S.count := by simp [S]
  let k : Strip.Trace r (fun _ : I=>S) (fun _ a=> send a) := ⟨Station.fixed _ hS,
    ?_, Rip.header (fun _ => hS) (Regime.fixed (Y:=Tree) (stripe S send))⟩
  · exact (Trace.always f.station (send ())).product
      ((( (Trace.always c (send ())).product k |>.product (Trace.always d (send ()))).product (Trace.always w.station (send ()))))
  obtain ⟨C,h⟩ : ∃ K : ℕ,∀ i:Fin 2,(send i).count≤ K :=
    ⟨∑ i:Fin 2,(send i).count,fun i=>Finset.single_le_sum (f:=fun i:Fin 2=>(send i).count) (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)⟩
  exact (Dom.const _ C).mono (fun i=> h _)

variable {L w : I→ℕ}
variable {T:I→ Type} (s : (i:I)→Series (T i))
theorem mirror (u : r.Has (tally ∘ H)) (e : r.Has (tally ∘ G))
    (f : Told r p) (B : Told r v) (a : ∀i,(s i).count*(w i+1)≤L i)
    (z : (i:I)→Base (p i) (v i) (Screen (H i) (G i) (Fin 1))→ T i→Grain (w i)) :
    let N := fun i=> plain (p i) (v i) (H i) (G i) 1
    Drive r (fun i=>(N i).count) L (orchid N s w z) (orchid N s w
      (fun _=> travel xchg (z _))) := by
  let N i := plain (p i) (v i) (H i) (G i) 1
  let n i := pack_lot (p i) (v i) (H i) (G i)
  let α i := normT (p i) (v i) (H i) (G i)
  let Z := fun i => z i ∘ (α i).cast.symm
  have Me := initF H G p v u e f B
  have t :=
    letI : (i:I)→ Fintype (Lot (p i) (v i) (H i) (G i)) := fun i=> by unfold Lot Base; infer_instance
    localAction (s:=n)
      (fun i=> pic (p i) (v i) (H i) (G i)) switch_
      (fun i a=> strip (s i) (Dusk.mark ∘ Z i a)) (Dusk.structure_ _ w Z a) Me
  have ee := Fleet.align (r:=r) (l:=L) (fun i a=> strip (s i) (Dusk.mark ∘ z i a))
    (fun i a=> strip (s i) (Dusk.mark ∘ travel xchg (z i) a)) (s:=N) (d:=N) (t:=n) (u:=n) α α
  apply ee
  have q : (fun i k=> strip (s i) (Dusk.mark ∘ (z i (xchg.symm ((α i).cast.symm k))))) =
      (fun i k=> strip (s i) (Dusk.mark ∘ (z i ((α i).cast.symm (sce.symm k))))) := by
    funext i k
    have e :=
      dwarf (p:=p i) (v:=v i) (h:=H i) (g:=G i) ((α i).cast.symm k)
    change (α i).cast (xchg.symm _) = sce.symm ((α i).cast ((α i).cast.symm k)) at e
    rw [Equiv.apply_symm_apply] at e
    rw [show xchg.symm ((α i).cast.symm k)=(α i).cast.symm (sce.symm k) from ((α i).cast.eq_symm_apply).2 e]
  change Fleet r L n n _ (fun i k=> strip (s i) (Dusk.mark ∘ (z i (xchg.symm ((α i).cast.symm k)))))
  rw [q]
  exact t
variable {D : ℕ} {J W : Type} [Fintype J] [Fintype W] (R : Series W)
variable (X : I → Prairie (dim J) W 0)
theorem dawn (h : r.Small fun i => (X i).plot.cert 0) (eH : r.header = fun i => (X i).plot.cert 0) (m : 1≤dim J) :
    let p (i:I) : QuestP (W:=W) (dim J) := ⟨0,X i⟩
    Rip r (fun i=>(X i).plot.terrain.count) (timeMark ∘ p)
      ((oracle (dim J) R).issue ∘ p) ((oracle (dim J) R).reply ∘ p) := by
  dsimp only
  let x (i:I) := Sigma.mk 0 (X i)
  change r.Small (roof x) at h
  have N := climate (J:=J) x h m
  let A (i:I) := (X i).plot.terrain
  let B i := cargo (dim J) R (x i)
  let W0 i := (X i).plot.shade
  let v i := (X i).silo
  let F := timeMark ∘ x
  have s0 i : (B i).count*(W0 i+1)≤F i := by
    rw [show (B i).count=_ from strands ..]
    unfold F timeMark users x
    change _ ≤ _ * _^0 * _
    rw [← dim,pow_zero]
    simp
    nlinarith [(X i).plot.radix] --?
  obtain ⟨p,b,a,d⟩ := profiles x h
  have hdr : Alive r (fun i=>(A i).count) F (roof x) :=
    (Rip.header N.1 h).idle
  let Y := orchid A B W0 v
  have q : Alive r (fun i=> (A i).count) F Y := shelter A B W0 v N s0
  have j := Drive.self N.1 q
  have u : r.Has (tally ∘ (fun i=>(X i).plot.tops)) := a
  have w : r.Has (tally ∘ (fun i=>(X i).plot.foot)) := d
  have e := mirror _ _ _ _ B u w p b s0 v
  let op (x : Dusk.Pair × Dusk.Pair) := gather (join_ false x.1,join_ true x.2)
  have ez : Easy op := (((Easy.fst.compose (join_easy false)).pair
    (Easy.snd.compose (join_easy true))).compose gather_easy)
  have res := duo_open A B (fun i a b=> Dusk.mark (v i a b)) (fun i a b=> Dusk.mark (travel xchg (v i) a b)) op j e ez ([],[]) ([],[])
  -- currently input header = r.header, problem issue = child cert, require r.header equal h (use end). Add equality.
  have z {k} (x y : Grain k) : op (Dusk.mark x,Dusk.mark y)=Dusk.mark ((gaunt k).glaze false*x+(gaunt k).streak false*y) := by
    change gather _=_
    rw [joined,← show (!false)=true from rfl, shone,meet]
  simp only [z] at res
  have hb (i : I) (a : (X i).plot.keys) (b : Frame W (X i).radio 0) :
      (gaunt (X i).plot.shade).glaze false * v i a b +
        (gaunt (X i).plot.shade).streak false * travel xchg (v i) a b =
          runOn (pointed false) (v i) a b := (bud (v i) a b).symm
  simp_rw [hb] at res
  rw [eH] at res -- rewriting header inside Drive? unfold
  change Rip r (fun i => (X i).plot.terrain.count) F
    ((oracle (dim J) R).issue ∘ x) ((oracle (dim J) R).reply ∘ x) at res
  exact res
end
end Phase

end IntegerMultiplication
end Computability
end OAI
