import OAI.Computability.IntegerMultiplication.Phase.Stamp

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Phase
open Net Net.Walsh Net.Tensor Strip Strip.Dims Strip.Optic Packed Loom
open Finset Matrix
variable (J W U : Type) [Fintype J] [DecidableEq J] [Fintype W]
/-- directional instructions interpreted polymorphically in gaussian dyadics -/
structure menu (a b : Addr J→Clock) (n : ℤ) where
  roster : List (Stamp J)
  norm j : j∈roster → j.v ⬝ᵥ j.v=1
  entries : (roster.map bill).sum=b-a
  many : (roster.length:ℤ)≤n
structure Guild (g : ℝ) where
  large : 3 ≤ dim J
  order : J≃Fin (dim J)
  rank : 1≤dim W
  engine : Circuit W U
  civil : engine.ok
  band : U→Addr J→Clock
  edge : U→U→Prop
  ticket : U→U→ℤ
  direction : engine.smooth edge
  pay a b : edge a b → Nonempty (menu J (band a) (band b) (ticket a b))
  witness : W→Addr J
  scar : W→Bool
  due : W≃W
  answer {R : Type} [CommRing R] (c : Quarter R) (x : W→R) w :
    engine.logical c.half x (due w) = c.ph (if scar w then 2 else 0)*x w
  result w : band (engine.sink (due w))-band (engine.init w)=tint (witness w)
  less : ((∑ w:W, engine.cost (fun _ => ticket) w : ℤ) : ℝ)/dim W < (dim J:ℝ)^g

noncomputable section
open Net.Shuttle Net.Motif Net.Motif.Carnival
def order_ : Guild Point FPclock Mark Motif.sigma := by
  classical
  letI := Shuttle.pieces
  refine {
    large := by rw [dim, Shuttle.volume]; norm_num [Motif.radix]
    order := Fintype.equivFin Point
    rank := ?_
    engine := Shuttle.cycle
    civil := Shuttle.trust
    band := addressPhase
    edge := Place.road adapt
    ticket := allow
    direction := Shuttle.quiet
    pay := fun a b e=>?_
    witness := Shuttle.witness
    scar := fun
    | .inr (.inl _) => true
    | _ => false
    due := route
    answer := ?_
    result := Shuttle.profile
    less := price }
  · let a : Motif.Piece := Classical.arbitrary _
    exact Fintype.card_pos_iff.mpr (Nonempty.intro (Sum.inl fun _ => a))
  · obtain ⟨l,c,d,e⟩ := howMany a b e
    exact ⟨⟨l,d,c,e⟩⟩
  intros R I c x w
  cases w with
  | inl a => simpa [sign,c.null] using signed c x (.inl a)
  | inr v =>
    cases v with
    | inl a => simpa [sign,c.moon] using signed c x (.inr (.inl a))
    | inr a => simpa [sign,c.null] using signed c x (.inr (.inr a))

variable {J W U} {b : ℝ} (d : Guild J W U b)
def agenda {a b : U} (e : d.edge a b) := Classical.choice (d.pay a b e)
variable {N O P : Type} [Fintype N] [DecidableEq N] (l : Layout O N J P)
variable {R : Type} [CommRing R] (c : Quarter R)
abbrev assignment (x : W→O→R) :=
  d.engine.physical (codec l d.band c) c.half x
def active (v : Addr J) (i : J) := decide (v i≠0)
def tint_ (v : Addr J) : Walsh.Field J R := Matrix.diagonal (swapSignVec (active v))

private theorem far (x : W→O→R) (w : W) :
    assignment d l c x (d.due w)=
    c.ph (if d.scar w then 2 else 0) • pipe l (allC c (active (d.witness w))) (x w) := by
  unfold assignment
  rw [Circuit.endpoint d.engine d.civil _ _ _ _ (d.answer c) _ w]
  simp_rw [Optic.advance, d.result]
  simp only [Walsh.extract]
  rfl
theorem central (x : W→O→R) (w : W) :
    let inv := d.witness
    c.ph (if d.scar w then 2 else 0) • pipe l ((pack c (active (inv w))) • tint_ (inv w))
      (assignment d l c (fun u=>pipe l (tint_ (inv u)) (x u)) (d.due w)) =
      pipe l (allC c (fun _=>false)) (x w) := by
  have t (v : Bool) : c.ph (if v then 2 else 0)*c.ph (if v then 2 else 0)=1 := by
    cases v <;> simp [c.moon,c.null]
  dsimp only
  rw [far,input_scale, smul_smul,t,one_smul,pipe_mul,pipe_mul,Matrix.smul_mul,Matrix.smul_mul]
  exact congrArg (fun m: Walsh.Field J R=>pipe l m (x w)) (wrap c _)

-- math clock masks
def rising (v : J→Bool) (x : Batch N J) : Clock :=
  ∑ j:J, if v j then 2*weight (fun i:N=>x i j) else 0
def offset (v : J→Bool) : Clock :=
  ∑ j, if v j then 1 else 0
def ebb (v : J→Bool) (x : Batch N J) : Clock :=
  rising v x+(dim N:Clock)*offset v

private theorem step_t (x : B) :
    c.ph (2*readX x) = (Quarter.raySign x:R) := c.shift _
theorem emitted (q : Addr J) (z : O) (x : O→R) :
    pipe l (tint_ q) x z = c.ph (rising (active q) (l z).1)*x z := by
  unfold pipe Optic.broadcast tint_
  rw [Tensor.diag, Strip.Optic.diag]
  unfold Tensor.vec swapSignVec rising
  rw [Finset.prod_comm]
  congr 1
  rw [c.of_sum]
  refine Finset.prod_congr rfl ?_
  intro j _
  split
  next e =>
    simp only [Walsh.weight, Finset.mul_sum,c.of_sum]
    congr 1
    ext i : 1
    exact (step_t c _).symm
  next _ => simp [c.null]

omit [DecidableEq J] in
theorem pack_s (v : J→Bool) : pack c v = c.ph (offset v) := by
  unfold offset pack
  rw [c.of_sum]
  apply Finset.prod_congr rfl; intro _ _
  split <;> simp_all [c.bright]
theorem ph_pow (k : ℕ) (v : Clock) :
    (c.ph v)^k = c.ph ((k:Clock)*v) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ,ih,Nat.cast_add,Nat.cast_one,add_mul,one_mul,c.of_add]
theorem removal (q : Addr J) (z : O) (x : O→R) :
    pipe l ((pack c (active q)) • tint_ q) x z = c.ph (ebb (active q) (l z).1)*x z := by
  unfold pipe Optic.broadcast
  rw [combine_scale]
  simp only [Finset.prod_const,Finset.card_univ,Strip.Optic.scale, Pi.smul_apply,smul_eq_mul]
  rw [pack_s c (active q), ph_pow]
  change c.ph (_*_) * pipe l (tint_ q) x z=_
  rw [emitted _ c,ebb,c.of_add]
  dsimp only [dim]
  ring
theorem solved (x : W→O→R) (w : W) (z : O) :
    let hit := fun w=> active (d.witness w)
    c.ph ((if d.scar w then 2 else 0) + ebb (hit w) ((l z).1))*
      assignment d l c (fun w i=> c.ph (rising (hit w) (l i).1)*x w i) (d.due w) z =
    pipe l (allC c (fun _=>false)) (x w) z := by
  dsimp only
  rw [← central d l c x w]
  simp only [Pi.smul_apply,smul_eq_mul,c.of_add,mul_assoc,
    show ∀ w:W,pipe l (tint_ (d.witness w)) (x w) =
      (fun i=> c.ph (rising (active (d.witness w)) (l i).1)*x w i) from
      fun w=>funext fun i=>emitted ..,removal _ c]

end
end Phase

end IntegerMultiplication
end Computability
end OAI
