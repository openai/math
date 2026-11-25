import OAI.Computability.NearSquareRoot.PhysicalWalshPieceExecution
import OAI.Computability.NearSquareRoot.PhysicalWalshNodeRouterRate

/-! # Compiling the rounded sweep at the individual piece rates

All levels operate on the same padded volume. The time sums their costs with
the exact multiplicities emitted by the schedule. The space takes the largest
single-piece area together with the polynomial-size geometry setup.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.Pieces

open IntegerMultiplication Code Space PhysicalWalshNode KernelPass

noncomputable def sweepVolume (A W k s w : ℕ) : ℝ := (extent A W k s : ℝ)*(w+1)

noncomputable def stageClock (A W calls : ℕ) (ρ B : ℝ) (L P : ℕ → ℝ) (k s w j : ℕ) : ℕ :=
  ⌊B*L w*sweepVolume A W k s w*((2:ℝ)*(A:ℝ)^j)^ρ + P w*(calls+1:ℝ)^j⌋₊

noncomputable def sweepArena (A W : ℕ) (c : ℝ) (P : ℕ → ℝ) (k s w : ℕ) : ℕ :=
  max (extent A W k s*(4*(w+1)+4)+1) ⌊2*c*sweepVolume A W k s w+(s+1:ℝ)*P w⌋₊

noncomputable def sweepSpace (A W : ℕ) (c : ℝ) (P : ℕ → ℝ) (C d k s w : ℕ) : ℕ :=
  C*(k+s+w+1)^d + sweepArena A W c P k s w

noncomputable def sweepTime (A W calls : ℕ) (ρ B c : ℝ) (L P : ℕ → ℝ) (C d k s w : ℕ) : ℕ :=
  let G := sweepSpace A W c P C d k s w
  2*(G+1) + ∑ j : Fin (walshPieceDigits A s).length,
    (walshPieceDigits A s).get j * (stageClock A W calls ρ B L P k s w j+G+1)

variable {a W : ℕ} (hw : 0 < W) (p : Plan (a+1) W W)

def input (b : Root) : Tree := send (((tally b.k,tally b.s),tally (b.w+1)),words (b.size (a:=a) (W:=W)) b.row)

def output (b : Root) : Tree := send (b.stream hw p (b.pieces (a:=a) hw).length)

/-- At a schedule entry, the node clock is the clock for that entry's level. -/
theorem stageClock_at (ha : 1 < a+1) (b : Root) (j : Fin (b.pieces (a:=a) hw).length)
    (calls : ℕ) (ρ B : ℝ) (L P : ℕ → ℝ) :
    let u := (b.pieces (a:=a) hw).get j
    pieceTimeBound (a+1) calls ρ B L P u = stageClock (a+1) W calls ρ B L P b.k b.s b.w u.level := by
  have geom := get_geometry hw ha b.k b.s b.w j
  simp only [pieceTimeBound,bitVolume,stageClock,sweepVolume,geom.1,geom.2.1]

/-- The common arena covers every scheduled node, including its level overhead. -/
theorem sweepArena_at (ha : 1 < a+1) (b : Root) (j : Fin (b.pieces (a:=a) hw).length)
    (c : ℝ) (P : ℕ → ℝ) (hP : ∀ w, 0 ≤ P w) :
    pieceSpaceBound (a+1) c P ((b.pieces (a:=a) hw).get j) ≤ sweepArena (a+1) W c P b.k b.s b.w := by
  let u := (b.pieces (a:=a) hw).get j
  have geom := get_geometry hw ha b.k b.s b.w j
  obtain ⟨z,t,eq⟩ := (mem_schedule hw b.k b.s b.w u).mp (List.get_mem _ j)
  have gap := offset_add_grow_le t.isLt
  have bits : z.val ≤ grow (a+1) z.val := z.val.lt_two_pow_self.le.trans
    ((Nat.pow_le_pow_left ha z.val).trans (Nat.le_mul_of_pos_left _ (by decide : 0 < 2)))
  have small : u.level ≤ b.s := by rw [←eq]; change z.val ≤ _; omega
  apply le_trans _ (le_max_right ..)
  apply Nat.floor_mono
  change 2*c*((count (a+1) u : ℝ)*(u.w+1))+(u.level+1:ℝ)*P u.w ≤ _
  rw [show u.w=b.w from geom.1, show count (a+1) u=extent (a+1) W b.k b.s from geom.2.1]
  have hrs : (u.level:ℝ)+1 ≤ b.s+1 := by exact_mod_cast Nat.succ_le_succ small
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hrs (hP _))

/-- The compiled sweep uses the closed piece rates on its actual, sequentially
rounded inputs. All arithmetic and recursive cost assumptions enter through
the piece release. -/
theorem roundedSweepRate {ρ c : ℝ} {L P : ℕ → ℝ} (hP : ∀ w, 0 ≤ P w)
    (release : PieceRelease hw p ρ c L P) {I : Type} (ha : 1 < a+1) (b : I → Root)
    (capacity : ∀ i, (b i).size (a:=a) (W:=W) ≤ 2^((b i).w+1)) (fits : ∀ i, (b i).Feasible hw p ha) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ d C : ℕ,
      BoundedTask (fun i => sweepTime (a+1) W p.calls ρ B c L P C d (b i).k (b i).s (b i).w)
        (fun i => sweepSpace (a+1) W c P C d (b i).k (b i).s (b i).w)
        (fun i => input (a:=a) (W:=W) (b i)) (fun i => output hw p (b i)) := by
  obtain ⟨B,hB,raw,_⟩ := release.2
  refine ⟨B,hB,?_⟩
  apply roundedSweep hw p ha b capacity fits (pieceTimeBound (a+1) p.calls ρ B L P) (pieceSpaceBound (a+1) c P) raw
    (fun i => stageClock (a+1) W p.calls ρ B L P (b i).k (b i).s (b i).w)
    (fun i => sweepArena (a+1) W c P (b i).k (b i).s (b i).w)
  · exact fun i j => (stageClock_at hw ha (b i) j p.calls ρ B L P).le
  · exact fun i j => sweepArena_at hw ha (b i) j c P hP
  · exact fun _ => le_max_left ..

end PhysicalWalsh.Pieces

end NearSquareRoot
end Computability
end OAI
