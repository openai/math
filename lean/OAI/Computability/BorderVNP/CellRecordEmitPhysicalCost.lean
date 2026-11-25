import OAI.Computability.BorderVNP.CellRecordEmitCost
import OAI.Computability.BorderVNP.CellCQFMeter
import OAI.Computability.BorderVNP.CellTypedDirectorySize

/-! # Public-record construction on the physical private clock

The complete directory can grow quadratically in the cell's load. A single
profile record is polylogarithmic for the fixed paid crossing dictionary.
Only that smaller word reaches the profile serializer. Consequently the
exponent in the load is twenty, independent of the profile leaf's clock.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Emit

open ExactQuantumFactoring.BitStackProgram

/-- An arbitrary binary width scale can be used for the bounded metadata fields;
the exponent in the physical cell size is the fixed value twenty. -/
theorem getRecordGuards_meter_physical (B j : ℕ) : ∃ K k : ℕ, ∀ (D : Directory) (M E L : ℕ),
    1 ≤ L → (Typed.directory D).length ≤ B*(M+E+1)^2*L^j → RowInputs D (B*L^j) →
    getRecordGuards.meter D ≤ K*(M+E+1)^20*L^k := by
  obtain ⟨C,hC⟩ := getRecordGuards_cost
  let d := smallGuard.bound.natDegree
  let a := smallGuard.bound.eval 1*(B+1)^d
  let c := 2*B+a+4
  let e := j*(d+1)
  refine ⟨2*C*c^10+2*B+1,e*10,?_⟩
  intro D M E L hL hd hr
  let N := M+E+1
  let Z := N^2*L^e
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hp : 1 ≤ Z := Nat.mul_pos (Nat.one_le_pow _ _ hN) (Nat.one_le_pow _ _ hL)
  have hj : j ≤ e := Nat.le_mul_of_pos_right _ (by omega)
  have hjd : j*d ≤ e := by dsimp [e]; rw [Nat.mul_succ]; omega
  have hpow (k : ℕ) (hk : k ≤ e) : L^k ≤ Z := (Nat.pow_le_pow_right (by omega) hk).trans
    (Nat.le_mul_of_pos_left _ (Nat.one_le_pow _ _ hN))
  have hplus : B*L^j+1 ≤ (B+1)*L^j := by
    rw [Nat.succ_mul]
    have := Nat.one_le_pow j L hL
    omega
  have heval : smallGuard.bound.eval (B*L^j) ≤ a*Z := by
    apply (Procedure.clock_eval_pow ..).trans
    calc _ ≤ smallGuard.bound.eval 1*((B+1)*L^j)^d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hplus _)
         _ = a*L^(j*d) := by rw [Nat.mul_pow,← Nat.pow_mul,Nat.mul_assoc]
         _ ≤ _ := Nat.mul_le_mul_left _ (hpow _ hjd)
  have hdata : (Typed.directory D).length ≤ B*Z :=
    hd.trans (by dsimp [Z,N]; rw [Nat.mul_assoc]; gcongr)
  have hscale : recordScale D (B*L^j) ≤ c*Z := by
    have h₁ := Nat.mul_le_mul_left B (hpow _ hj)
    dsimp [recordScale,c]
    nlinarith only [hdata,heval,h₁,hp]
  have hZ : Z^10 = N^20*L^(e*10) := by
    rw [show Z = N^2*L^e from rfl,Nat.mul_pow,← Nat.pow_mul,← Nat.pow_mul]
  have h₁ := (hC D (B*L^j) hr).trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hscale 10))
  rw [Nat.mul_pow,hZ,← Nat.mul_assoc] at h₁
  have hdom : Z ≤ N^20*L^(e*10) := by
    rw [← hZ]
    exact Nat.le_self_pow (by decide) _
  have hdata' := hdata.trans (Nat.mul_le_mul_left B hdom)
  have h1 : 1 ≤ N^20*L^(e*10) := hp.trans hdom
  have ho := getRecordGuards.output_length_le_cost D
  unfold Procedure.meter
  change _ ≤ (2*C*c^10+2*B+1)*N^20*L^(e*10)
  rw [Nat.mul_assoc (2*C*c^10+2*B+1),Nat.add_mul,Nat.add_mul,Nat.one_mul]
  rw [Nat.mul_assoc 2 C (c^10),Nat.mul_assoc 2 (C*c^10),Nat.mul_assoc 2 B]
  dsimp only [id_eq] at ho ⊢
  omega

/-- The stored one-copy mass, numerical field bounds, and fixed field count of each
physical record suffice for the clock of the native serializer. -/
theorem getRecordGuards_meter_of_fields (A B j R : ℕ) : ∃ K k : ℕ, ∀ (D : Directory) (p M E U n : ℕ),
    D.StaticBounds A M → storedMass D ≤ A*(M+1)^2 → RawFields D p U → U ≤ B*(n+2)^j →
    (∀ r ∈ D.records, (Packet.record r).length ≤ R) →
    getRecordGuards.meter D ≤ K*(M+E+1)^20*(n.size+1)^k := by
  let c₁ := 300*(8*A+4)*(B.size+j+1)
  let c₂ := (64*R+3)*(B.size+j+1)
  let c := max c₁ c₂
  obtain ⟨K,k,h⟩ := getRecordGuards_meter_physical c 1
  refine ⟨K,k,fun D p M E U n hs hstore hr hu hrows => h D M E (n.size+1) (by omega) ?_ ?_⟩
  · rw [pow_one]
    have ht := typed_directory_length_static D p hs hstore hr hu
    change (Typed.directory D).length ≤ c₁*(M+1)^2*(n.size+1) at ht
    exact ht.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul (le_max_left ..)
      (Nat.pow_le_pow_left (by omega) 2)))
  · rw [pow_one]
    intro r hx
    apply (rowInputs_of_fields D p hr hrows r hx).trans
    have hw := CellMacro.Generator.size_of_polynomial_field hu
    have hw' : U.size+1 ≤ (B.size+j+1)*(n.size+1) := by
      rw [Nat.add_mul,Nat.add_mul,Nat.one_mul,Nat.mul_succ B.size]
      omega
    calc
      _ ≤ (64*R+3)*((B.size+j+1)*(n.size+1)) := Nat.mul_le_mul_left _ hw'
      _ = c₂*(n.size+1) := (Nat.mul_assoc ..).symm
      _ ≤ c*(n.size+1) := Nat.mul_le_mul_right _ (le_max_right ..)

/-- The public pass also works with a binary width bound directly, allowing
record addresses to depend on both the base input and the stretching factor. -/
theorem getRecordGuards_meter_of_width (A B j R : ℕ) :
    ∃ K k : ℕ, 0 < K ∧ 0 < k ∧ ∀ (D : Directory) (p M E U L : ℕ),
      D.StaticBounds A M → storedMass D ≤ A*(M+1)^2 → RawFields D p U →
      1 ≤ L → U.size+1 ≤ B*L^j → (∀ r ∈ D.records, (Packet.record r).length ≤ R) →
      getRecordGuards.meter D ≤ K*(M+E+1)^20*L^k := by
  let c₁ := 300*(8*A+4)*B
  let c₂ := (64*R+3)*B
  let c := max c₁ c₂
  obtain ⟨K,k,h⟩ := getRecordGuards_meter_physical c j
  refine ⟨K+1,k+1,by omega,by omega,?_⟩
  intro D p M E U L hs hm hr hL hw hrows
  apply (h D M E L hL ?_ ?_).trans
  · exact Nat.mul_le_mul (Nat.mul_le_mul_right _ (by omega)) (Nat.pow_le_pow_right hL (by omega))
  · apply (typed_directory_length D p hr).trans
    have hW := words_length_from_static D p hs hm
    calc _ ≤ 300*((8*A+4)*(M+1)^2)*(B*L^j) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hW) hw
         _ = c₁*(M+1)^2*L^j := by dsimp [c₁]; ring
         _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul (le_max_left ..) (Nat.pow_le_pow_left (by omega) _))
  · intro r hx
    apply (rowInputs_of_fields D p hr hrows r hx).trans
    calc _ ≤ (64*R+3)*(B*L^j) := Nat.mul_le_mul_left _ hw
         _ = c₂*L^j := (Nat.mul_assoc ..).symm
         _ ≤ c*L^j := Nat.mul_le_mul_right _ (le_max_right ..)

end CellSparse.Packet.Emit

end BorderVNP
end Computability
end OAI
