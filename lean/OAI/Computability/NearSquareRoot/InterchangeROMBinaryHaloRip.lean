import OAI.Computability.NearSquareRoot.InterchangeROMBinaryHeader

/-! # Charging halo adapter tasks to the compact binary header -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMBinary.Ticket

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip

private theorem row_charge {N u v p H C B : ℕ} (hn : 0 < N) (hh : 0 < H)
    (hpad : p ≤ B*H) (hwidth : v ≤ C*(u+p+1)) :
    (N+1)*(v+1)+1 ≤ (2*(C*(B+2)+1)+1)*(N*(u+H)) := by
  have base : 0 < u+H := by omega
  have poly : u+p+1 ≤ (B+2)*(u+H) := by
    have h := Nat.mul_le_mul_left B (show H ≤ u+H by omega)
    rw [Nat.add_mul]
    omega
  have width : v+1 ≤ (C*(B+2)+1)*(u+H) := by
    have z := hwidth.trans (Nat.mul_le_mul_left C poly)
    rw [Nat.add_mul,Nat.one_mul,Nat.mul_assoc]
    omega
  have hprod := Nat.mul_le_mul (show N+1 ≤ 2*N by omega) width
  calc
    _ ≤ 2*N*((C*(B+2)+1)*(u+H)) + N*(u+H) := by
      have := Nat.mul_pos hn base
      omega
    _ = _ := by ring

private theorem positive_total (x : Ticket) : 0 < x.total := by
  obtain ⟨hP,hbin,hG,hB,hde⟩ := grid_good x
  have hE : 0 < x.grid.E := hbin.trans_le hde
  change 0 < x.grid.P*x.grid.E*x.grid.G*x.grid.E*x.grid.B
  positivity

private theorem halo_budget {k C : ℕ} {w : Ticket → ℕ}
    (hw : ∀ x, w x ≤ C*(x.w+pad k x+1)) :
    ∃ m K : ℕ, ∀ x : Ticket, (((x.total+1)*(w x+1):ℕ):ℝ)+1 ≤
      (K:ℝ)*mass regime total (fun x => x.w) m x := by
  obtain ⟨m,D,hD⟩ := Regime.Small.extent (has_pad k)
  refine ⟨m,2*(C*(D+2)+1)+1,fun x => ?_⟩
  have hp := hD x
  change size (tally (pad k x)) ≤ D*(regime.scale x+1)^m at hp
  rw [size_tally,tally_length] at hp
  let H := (regime.scale x+1)^m
  have hH : 0 < H := Nat.pow_pos (Nat.succ_pos _)
  have hpad : pad k x ≤ D*H := by dsimp [H]; omega
  have u := row_charge (positive_total x) hH hpad (hw x)
  dsimp only [mass]
  exact_mod_cast u

/-- A scan whose records have the padded width fits the original binary Rip budget.
The input volume is supplied by its producer; the task itself bounds the output. -/
theorem halo_task_rip {k C : ℕ} {w : Ticket → ℕ} {p q : Ticket → Tree}
    (hw : ∀ x, w x ≤ C*(x.w+pad k x+1)) (hin : Alive regime total (fun x => x.w) p)
    (task : Task (fun x => (x.total+1)*(w x+1)) p q) : Rip regime total (fun x => x.w) p q := by
  obtain ⟨m,K,h⟩ := halo_budget hw
  obtain ⟨l,hi⟩ := hin
  let M := mass regime total (fun x => x.w) (l+m)
  have old : Carries M p p := hi.larger (mass_le (by omega))
  refine ⟨l+m, ⟨⟨old.budget, _, task, K, fun x => (h x).trans ?_⟩, old.small⟩⟩
  exact mul_le_mul_of_nonneg_left (mass_le (by omega : m ≤ l+m) x) (Nat.cast_nonneg K)

/-- A native reply of bounded total size can be carried into the cropping pass. -/
theorem halo_alive {k C C' : ℕ} (w : Ticket → ℕ) (hw : ∀ x, w x ≤ C*(x.w+pad k x+1))
    {p : Ticket → Tree} (hs : ∀ x, (p x).count ≤ C'*((x.total+1)*(w x+1)+1)) :
    Alive regime total (fun x => x.w) p := by
  obtain ⟨m,K,h⟩ := halo_budget hw
  refine ⟨m,Carries.idles (unit_mass positive_total _) ⟨C'*K, fun x => ?_⟩⟩
  calc
    _ ≤ (C':ℝ)*((((x.total+1)*(w x+1):ℕ):ℝ)+1) := by exact_mod_cast hs x
    _ ≤ (C':ℝ)*((K:ℝ)*mass regime total (fun x => x.w) m x) :=
      mul_le_mul_of_nonneg_left (h x) (Nat.cast_nonneg C')
    _ = _ := by rw [Nat.cast_mul,mul_assoc]

end InterchangeROMBinary.Ticket

end NearSquareRoot
end Computability
end OAI
