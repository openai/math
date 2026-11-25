import OAI.Computability.NearSquareRoot.CRTControlledRowPackets
import OAI.Computability.NearSquareRoot.CRTControlledSizes

/-! # Space and payload reserves for a binary XOR window

High spectators index rows, and low spectators are packed into each cell of
the row program. The raw record width can be any positive natural. Both row
headers and dimension rulers are charged to the original bit volume.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.XorReserve

open IntegerMultiplication IntegerMultiplication.Adic IntegerMultiplication.Code
open IntegerMultiplication.Packed IntegerMultiplication.Strip NearSquareRoot.Controlled
open NearSquareRoot.Space Filter

def pack (B m : ℕ) := 2^B*m
def rowWidth (N B m : ℕ) := 2^N*pack B m
def volume (R N B m : ℕ) := 2^(R+N+B)*m

theorem rows_volume (R N B m : ℕ) : 2^R*rowWidth N B m = volume R N B m := by
  simp only [volume,rowWidth,pack,pow_add,mul_assoc]

private theorem pack_pos {B m : ℕ} (hm : 0 < m) : 0 < pack B m := Nat.mul_pos (Nat.two_pow_pos _) hm

private theorem width_pos {N B m : ℕ} (hm : 0 < m) : 0 < rowWidth N B m :=
  Nat.mul_pos (Nat.two_pow_pos _) (pack_pos hm)

theorem payload_le {degree Q B m : ℕ} (low : payloadBits degree Q ≤ B) :
    2^(payloadBits degree Q)*m ≤ pack B m :=
  Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) low)

theorem polynomial_le_pack {degree scale Q B m : ℕ} (hs : scale ≤ Q) (hm : 0 < m)
    (low : payloadBits degree Q ≤ B) : (scale+1)^degree ≤ pack B m :=
  (Nat.pow_le_pow_left (Nat.succ_le_succ hs) degree).trans
    ((payload_capacity _ _ _ hm).trans (payload_le low))

theorem metadata_le_volume {scale Q e R N B m : ℕ} (hs : scale ≤ Q) (hm : 0 < m)
    (low : payloadBits e Q ≤ B) : max (2^R) (2^N)*(scale+1)^e ≤ volume R N B m := by
  have groups : max (2^R) (2^N) ≤ 2^R*2^N := max_le
    (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)) (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _))
  rw [←rows_volume, rowWidth, ←Nat.mul_assoc]
  exact Nat.mul_le_mul groups (polynomial_le_pack hs hm low)

/-- The numerical obligations passed to the row command. The constant H
bounds the repeated header and its unary high-prefix length per row. -/
structure PacketBounds (degree e scale Q header H R N B m : ℕ) : Prop where
  payload : 2^(payloadBits degree Q)*m ≤ pack B m
  metadata : max (2^R) (2^N)*(scale+1)^e ≤ (H+10)*volume R N B m
  headerArea : 2^R*(header+2*R+2^N*(2*pack B m+2)+5)+1 ≤ (H+10)*volume R N B m
  rowArea : 2^R*rowWidth N B m ≤ (H+10)*volume R N B m

/-- A separate setup bound suffices even if the low reserve is tuned only to
the payload degree. -/
theorem packetBounds {degree e scale Q header H R N B m : ℕ} (hm : 0 < m)
    (low : payloadBits degree Q ≤ B)
    (headerFits : header+2*R ≤ H*rowWidth N B m)
    (setup : max (2^R) (2^N)*(scale+1)^e ≤ volume R N B m) :
    PacketBounds degree e scale Q header H R N B m := by
  have p := pack_pos (B:=B) hm
  have r := width_pos (N:=N) (B:=B) hm
  have cell : 2^N*(2*pack B m+2) ≤ 4*rowWidth N B m := by
    calc
      _ ≤ 2^N*(4*pack B m) := Nat.mul_le_mul_left _ (by omega)
      _ = _ := by unfold rowWidth; ring
  have each : header+2*R+2^N*(2*pack B m+2)+5 ≤ (H+9)*rowWidth N B m := by
    rw [Nat.add_mul]; omega
  have total : 0 < volume R N B m := by rw [←rows_volume]; exact Nat.mul_pos (Nat.two_pow_pos _) r
  have padded : volume R N B m ≤ (H+10)*volume R N B m := Nat.le_mul_of_pos_left _ (by omega)
  refine ⟨payload_le low,setup.trans padded,?_,(rows_volume ..).le.trans padded⟩
  have all := Nat.mul_le_mul_left (2^R) each
  rw [Nat.mul_left_comm (2^R) (H+9),rows_volume] at all
  rw [show H+10 = (H+9)+1 by omega,Nat.succ_mul (H+9) (volume R N B m)]
  omega

/-- A polynomial bound on the row scan factor determines a logarithmic
number of protected high-prefix bits. -/
theorem high_reserve {Q J f R factor : ℕ} (rate : factor ≤ J*(Q+1)^f)
    (high : Nat.clog 2 J + payloadBits f Q ≤ R) : factor ≤ 2^R := by
  have poly := payload_capacity f Q 1 (by decide)
  simp only [Nat.mul_one] at poly
  calc
    _ ≤ J*(Q+1)^f := rate
    _ ≤ 2^(Nat.clog 2 J)*2^(payloadBits f Q) := Nat.mul_le_mul (Nat.le_pow_clog (by decide) _) poly
    _ = _ := (pow_add ..).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) high

/-- For every positive controller scale, these actual high and low cuts both
fit fixed multiples of its ceiling binary logarithm. -/
theorem cuts {Q J f D R B factor : ℕ} (hQ : 0 < Q) (rate : factor ≤ J*(Q+1)^f)
    (high : (Nat.clog 2 J+f)*Nat.clog 2 (Q+1) ≤ R) (low : D*Nat.clog 2 (Q+1) ≤ B) :
    ∃ r b : ℕ, r ≤ R ∧ b ≤ B ∧ factor ≤ 2^r ∧ payloadBits D Q ≤ b ∧
      r+b ≤ (Nat.clog 2 J+f+D)*Nat.clog 2 (Q+1) := by
  have pos : 0 < Nat.clog 2 (Q+1) := by
    by_contra! h
    have cap := Nat.le_pow_clog (by decide : 1 < 2) (Q+1)
    rw [show Nat.clog 2 (Q+1) = 0 by omega,pow_zero] at cap
    omega
  have fit : Nat.clog 2 J + payloadBits f Q ≤ (Nat.clog 2 J+f)*Nat.clog 2 (Q+1) := by
    rw [Nat.add_mul,payloadBits]
    exact Nat.add_le_add_right (Nat.le_mul_of_pos_right _ pos) _
  exact ⟨_,_,fit.trans high,low,high_reserve rate le_rfl,le_rfl,by rw [Nat.add_mul]; exact Nat.add_le_add_right fit _⟩

/-- The bounded prefix-row interpreter with its numeric geometry discharged.
Its fixed exponent is chosen before the controller scale, rate bound, or
particular reserve inequalities. Tree cells may use any positive record width. -/
theorem packedWindowRowsOn {X : Type} {r : Regime X} (R N K : X → ℕ)
    (hR : r.Has (tally ∘ R)) (hN : r.Has (tally ∘ N))
    (view : (x : X) → Adopt ((line 2 (R x)).cart (line 2 (N x))) (line 2 (K x)))
    (f g : (x : X) → Block 2 (K x) → Tree)
    {records packed : ((x : X) × Block 2 (R x)) → ℕ} {rate : ((x : X) × Block 2 (R x)) → ℝ}
    (row : Breeze rate (fixedRowRegime r R hR) records packed
      (fun z => Tree.fork ((fixedRowRegime r R hR).header z)
        (stripe (line 2 (N z.1)) fun b => f z.1 ((view z.1).cast (z.2,b))))
      (fun z => stripe (line 2 (N z.1)) fun b => g z.1 ((view z.1).cast (z.2,b)))) :
    ∃ D : ℕ, ∀ {Y : Type} (select : Y → X) (B m Q factor : Y → ℕ),
      (∀ y a, records ⟨select y,a⟩ ≤ 2^N (select y)) →
      (∀ y a, packed ⟨select y,a⟩ = pack (B y) (m y)) →
      (∀ y a, (f (select y) a).count ≤ 2*pack (B y) (m y)+1) →
      (∀ y a, (g (select y) a).count ≤ 2*pack (B y) (m y)+1) →
      (∀ y, r.scale (select y) ≤ Q y) → (∀ y, 0 < m y) → (∀ y, payloadBits D (Q y) ≤ B y) →
      (∀ y a, 2*rate ⟨select y,a⟩ ≤ factor y) → (∀ y, factor y ≤ 2^R (select y)) →
      let V y := volume (R (select y)) (N (select y)) (B y) (m y)
      BoundedTask (fun y => V y*(factor y+1)) V
        (together r.header (stackRun (fun x => line 2 (K x)) f) ∘ select)
        (stackRun (fun x => line 2 (K x)) g ∘ select) := by
  obtain ⟨p,e,run⟩ := packedPrefixRowsOn R N K hR hN view f g row
  obtain ⟨h,H,header⟩ := r.gauge.add hR.extent
  let D := max p (max e h)
  refine ⟨D,fun select B m Q factor rows packs inLeaves outLeaves scale hm low rateBound high => ?_⟩
  intro V
  have room (i x) (hi : i ≤ D) : payloadBits i (Q x) ≤ B x :=
    (Nat.mul_le_mul_right (Nat.clog 2 (Q x+1)) hi).trans (low x)
  have cell (x) : (r.scale (select x)+1)^h ≤ pack (B x) (m x) :=
    polynomial_le_pack (scale x) (hm x) (room h x ((le_max_right e h).trans (le_max_right ..)))
  have fits (x) : (r.header (select x)).count+2*R (select x) ≤ H*rowWidth (N (select x)) (B x) (m x) := by
    have head := header (select x)
    change (r.header (select x)).count+size (tally (R (select x))) ≤ H*(r.scale (select x)+1)^h at head
    simp only [size_tally,tally_length] at head
    have inner : pack (B x) (m x) ≤ rowWidth (N (select x)) (B x) (m x) := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
    have cap := Nat.mul_le_mul_left H ((cell x).trans inner)
    omega
  have cert (x) := packetBounds (scale:=r.scale (select x)) (hm x)
    (room p x (le_max_left ..)) (fits x)
    (metadata_le_volume (scale x) (hm x) (room e x ((le_max_left e h).trans (le_max_right ..))))
  have task := run select factor (fun x => (H+10)*V x) Q m (fun x => rowWidth (N (select x)) (B x) (m x))
    (fun x => 2*pack (B x) (m x)+1) scale hm (fun x a => (packs x a).symm ▸ (cert x).payload)
    (fun x a => by rw [packs]; exact Nat.mul_le_mul_right _ (rows x a))
    rateBound (fun x => (cert x).metadata) inLeaves outLeaves (fun x => (cert x).headerArea)
    (fun x => (cert x).rowArea) high
  apply task.bound (H+10) (H+10) <;> intro x
  · rw [Nat.mul_assoc, Nat.mul_succ (H+10) (V x*(factor x+1))]
    omega
  · rw [Nat.mul_succ]; omega

/-- Apply the reserved row program to its original family of windows. -/
theorem packedWindowRows {X : Type} {r : Regime X} (R N K B m : X → ℕ)
    (hR : r.Has (tally ∘ R)) (hN : r.Has (tally ∘ N))
    (view : (x : X) → Adopt ((line 2 (R x)).cart (line 2 (N x))) (line 2 (K x)))
    (f g : (x : X) → Block 2 (K x) → Tree)
    {records packed : ((x : X) × Block 2 (R x)) → ℕ} {rate : ((x : X) × Block 2 (R x)) → ℝ}
    (row : Breeze rate (fixedRowRegime r R hR) records packed
      (fun z => Tree.fork ((fixedRowRegime r R hR).header z)
        (stripe (line 2 (N z.1)) fun b => f z.1 ((view z.1).cast (z.2,b))))
      (fun z => stripe (line 2 (N z.1)) fun b => g z.1 ((view z.1).cast (z.2,b))))
    (rows : ∀ x a, records ⟨x,a⟩ ≤ 2^N x)
    (packs : ∀ x a, packed ⟨x,a⟩ = pack (B x) (m x))
    (inLeaves : ∀ x a, (f x a).count ≤ 2*pack (B x) (m x)+1)
    (outLeaves : ∀ x a, (g x a).count ≤ 2*pack (B x) (m x)+1) :
    ∃ D : ℕ, ∀ Q factor : X → ℕ,
      (∀ x, r.scale x ≤ Q x) → (∀ x, 0 < m x) → (∀ x, payloadBits D (Q x) ≤ B x) →
      (∀ x a, 2*rate ⟨x,a⟩ ≤ factor x) → (∀ x, factor x ≤ 2^R x) →
      let V x := volume (R x) (N x) (B x) (m x)
      BoundedTask (fun x => V x*(factor x+1)) V
        (together r.header (stackRun (fun x => line 2 (K x)) f)) (stackRun (fun x => line 2 (K x)) g) := by
  obtain ⟨D,applyOn⟩ := packedWindowRowsOn R N K hR hN view f g row
  exact ⟨D,fun Q factor => applyOn id B m Q factor rows packs inLeaves outLeaves⟩

end PhysicalWalsh.XorReserve

end NearSquareRoot
end Computability
end OAI
