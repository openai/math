import OAI.Hierarchy.DescentPrivateDonorBillNumbers

namespace OAI
/-! # Native cost of all three static donor installers, including executable literal slots -/

namespace Hierarchy.DescentCompiler.TerminalScale

theorem donor_install_bill {H groups amount h K W chunks pages tables words : ℕ}
    (hosts : 0<H) (word : W≤K*h) (rom : pages≤H)
    (input : H*chunks*h≤H*h+4*H*groups*amount)
    (extent : words≤2*(H*chunks)+tables*pages) :
    ((12+10*words)+15*(words+3))*W ≤
      H*h*(K*(107+25*tables))+H*groups*(K*(200*amount)) := by
  have twice : words*h≤2*(H*h+4*H*groups*amount)+tables*(H*h) :=calc
    _ ≤ (2*(H*chunks)+tables*pages)*h := Nat.mul_le_mul_right _ extent
    _ = 2*(H*chunks*h)+tables*(pages*h) :=by ring
    _ ≤ _ := Nat.add_le_add (Nat.mul_le_mul_left _ input) (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ rom))
  calc
    _ ≤ ((12+10*words)+15*(words+3))*(K*h) :=Nat.mul_le_mul_left _ word
    _ = K*(57*h+25*(words*h)) :=by ring
    _ ≤ K*(57*(H*h)+25*(2*(H*h+4*H*groups*amount)+tables*(H*h))) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hosts))
        (Nat.mul_le_mul_left _ twice))
    _ = _ :=by ring

/-- A single grade bounds the per-date host work after mounting all tables.
Choosing this grade from the literal number of tables and actual expression work is sufficient. -/
theorem donor_installed_row {H groups amount h K f tables radix row init : ℕ}
    (positive : 0<radix)
    (run : row≤H*h*(K*(1274+6*f))+H*(groups*radix)*(K*(4*amount*(342+2*f))))
    (setup : init≤H*h*(K*(107+25*tables))+H*groups*(K*(200*amount))) :
    let grade:=f+25*tables+200
    row+init≤H*h*(K*(1274+6*grade))+H*(groups*radix)*(K*(4*amount*(342+2*grade))) := by
  intro grade
  have ranked : H*groups≤H*(groups*radix) :=Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ positive)
  have overhead : 1274+6*f+(107+25*tables)≤1274+6*grade :=by unfold grade;omega
  have text : 4*amount*(342+2*f)+200*amount≤4*amount*(342+2*grade) :=calc
    _ = 4*amount*(392+2*f) :=by ring
    _ ≤ _ :=Nat.mul_le_mul_left _ (by unfold grade;omega)
  apply (Nat.add_le_add run setup).trans
  calc
    _ ≤ H*h*(K*(1274+6*f))+H*(groups*radix)*(K*(4*amount*(342+2*f)))+
        (H*h*(K*(107+25*tables))+H*(groups*radix)*(K*(200*amount))) :=
      Nat.add_le_add_left (Nat.add_le_add_left (Nat.mul_le_mul_right _ ranked) _) _
    _ = H*h*(K*(1274+6*f+(107+25*tables)))+
        H*(groups*radix)*(K*(4*amount*(342+2*f)+200*amount)) :=by ring
    _ ≤ _ :=Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ overhead))
        (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ text))

end Hierarchy.DescentCompiler.TerminalScale

end OAI
