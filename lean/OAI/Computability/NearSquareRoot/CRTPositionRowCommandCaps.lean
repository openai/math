import OAI.Computability.NearSquareRoot.CRTPositionWindowRow
import OAI.Computability.NearSquareRoot.CRTControlledReserveCutoff
import OAI.Computability.NearSquareRoot.CRTControlledBudget

/-! # Volumes of row packets for a table-driven position permutation -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionRows.Window.Packets

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
open IntegerMultiplication.Adic IntegerMultiplication.Loom

noncomputable section

def vol (x : Window) := 2^x.k*x.w

def rowIn (z : Row) : Tree :=
  .fork (rowRegime.header z) (ReservePack.raw natural (fun z => z.1.mid) (fun z => z.1.lo) src z)

def rowOut : Row → Tree := ReservePack.raw natural (fun z => z.1.mid) (fun z => z.1.lo) dst

def ins (x : Window) := stripe (line 2 x.hi) (fun a => rowIn ⟨x,a⟩)

def outs (x : Window) := stripe (line 2 x.hi) (fun a => rowOut ⟨x,a⟩)

def cells (x : Window) (z : Block 2 x.k) := strip (Series.natural x.w) (x.record z)

def flat (x : Window) := stripe (line 2 x.k) (cells x)

def result (x : Window) := stripe (line 2 x.k) (cells x ∘ x.routed)

private theorem raw_size (f : (z : Row) → Block 2 (z.1.mid+z.1.lo) → Fin z.1.w → Bead) (z : Row) :
    (ReservePack.raw natural (fun z => z.1.mid) (fun z => z.1.lo) f z).count ≤
      5 * (2^(z.1.mid+z.1.lo)*z.1.w) :=
  ReserveSmall.beadClothCap (fun z : Row => z.1.mid+z.1.lo) (fun z => z.1.w)
    natural f (fun z => z.1.pos) (fun _ => (Series.count_natural _).le) z

private theorem flat_size (x : Window) : (flat x).count ≤ 5*vol x :=
  ReserveSmall.beadClothCap k w (fun x => Series.natural x.w) record pos
    (fun _ => (Series.count_natural _).le) x

private theorem pow_capacity {d D k n : ℕ} (h : d ≤ D) (cut : payloadBits D k ≤ n) :
    (k+1)^d ≤ 2^n :=
  (Nat.pow_le_pow_right (by omega : 0 < k+1) h).trans
    ((by simpa using payload_capacity D k 1 (by decide) : (k+1)^D ≤ 2^(payloadBits D k)).trans
      (Nat.pow_le_pow_right (by decide) cut))

/-- Low and high address reservations pay for both the per-row headers and the
polynomial setup attached to the larger of the row count and the row length. -/
theorem caps (d : ℕ) : ∃ D C : ℕ, ∀ x : Window,
    payloadBits D x.k ≤ x.lo → payloadBits D x.k ≤ x.hi →
    max (2^x.hi) (2^(x.mid+x.lo))*(x.k+1)^d ≤ C*vol x ∧
      (ins x).count ≤ C*vol x ∧ (outs x).count ≤ C*vol x ∧ (flat x).count ≤ C*vol x := by
  obtain ⟨p,B,head⟩ := rowRegime.gauge
  let D := max d p
  refine ⟨D,B+8,?_⟩
  intro x low high
  let H := 2^x.hi
  let N := 2^(x.mid+x.lo)
  let W := N*x.w
  have shape : H*W = vol x := by
    dsimp only [H,W,N,vol]
    rw [← Nat.mul_assoc, ← pow_add, show x.hi+(x.mid+x.lo) = x.k by
      have := x.fit; unfold mid; omega]
  have wpos : 0 < W := Nat.mul_pos (Nat.two_pow_pos _) x.pos
  have vpos : 0 < vol x := Nat.mul_pos (Nat.two_pow_pos _) x.pos
  have lowCapacity : 2^x.lo ≤ N := Nat.pow_le_pow_right (by decide) (Nat.le_add_left ..)
  have records : N ≤ W := Nat.le_mul_of_pos_right _ x.pos
  have setup : max H N * (x.k+1)^d ≤ vol x := by
    rw [← shape, max_mul_of_nonneg _ _ (Nat.zero_le _)]
    apply max_le
    · exact Nat.mul_le_mul_left H ((pow_capacity (le_max_left ..) low).trans (lowCapacity.trans records))
    · calc
        _ ≤ N*H := Nat.mul_le_mul_left _ (pow_capacity (le_max_left ..) high)
        _ ≤ H*W := (Nat.mul_comm N H) ▸ Nat.mul_le_mul_left H records
  have header (a : Block 2 x.hi) : (rowRegime.header ⟨x,a⟩).count ≤ B*W :=
    (head ⟨x,a⟩).trans (Nat.mul_le_mul_left _ ((pow_capacity (le_max_right ..) low).trans
      (lowCapacity.trans records)))
  have pack (r : Block 2 x.hi → Tree) (hr : ∀ a, (r a).count ≤ (B+6)*W) :
      (stripe (line 2 x.hi) r).count ≤ (B+8)*vol x := by
    have cap := stripe_size (line 2 x.hi) r _ hr
    rw [lineSize] at cap
    refine cap.trans ?_
    have each : (B+6)*W+1 ≤ (B+7)*W := by rw [Nat.succ_mul (B+6)]; omega
    have whole := Nat.mul_le_mul_left H each
    rw [Nat.mul_left_comm H (B+7), shape] at whole
    change H*((B+6)*W+1)+1 ≤ (B+8)*vol x
    rw [Nat.succ_mul (B+7)]
    omega
  refine ⟨setup.trans (Nat.le_mul_of_pos_left _ (by omega)), pack _ ?_, pack _ ?_,
    (flat_size x).trans (Nat.mul_le_mul_right _ (by omega))⟩
  · intro a
    change (rowRegime.header ⟨x,a⟩).count + _ + 1 ≤ (B+6)*W
    have src_size := raw_size src ⟨x,a⟩
    change _ ≤ 5*W at src_size
    rw [Nat.add_mul]
    have := header a
    omega
  · intro a
    exact (raw_size dst ⟨x,a⟩).trans (Nat.mul_le_mul_right W (by omega))


end
end Controlled.PositionRows.Window.Packets

end NearSquareRoot
end Computability
end OAI
