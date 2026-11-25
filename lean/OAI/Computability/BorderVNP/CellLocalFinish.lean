import OAI.Computability.BorderVNP.CellReportedWordEmit
import OAI.Computability.BorderVNP.CellCQFPolynomialDegree
import OAI.Computability.BorderVNP.CellCQFMeterPair

/-! # The finite checker for a single local subtotal word

The checker receives the prefix-table base, physical offset, occurrence cap, and
addresses of the bits of one reported count. It does not read the rest of the
cell directory. This makes its full polynomial clock depend only on these fields.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Emit.Finish

open ExactQuantumFactoring.BitStackProgram

/-- Prefix base, relocated-data offset, total occurrence count, and the original
little-endian wires of one binary subtotal. -/
abbrev Input := ℕ × ℕ × ℕ × List ℕ

/-- The actual four-field stack encoding of one terminal check. -/
abbrev code := prodCode Nat.bits (prodCode Nat.bits (prodCode Nat.bits Typed.naturals))

/-- Fixed deterministic printer of the compact native subtotal statement. -/
noncomputable def printer : Statement code (fun x => finishCount x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  let base := Procedure.first Nat.bits (prodCode Nat.bits (prodCode Nat.bits Typed.naturals))
  let rest := Procedure.second Nat.bits (prodCode Nat.bits (prodCode Nat.bits Typed.naturals))
  let off := (Procedure.first Nat.bits _).comp rest
  let pair := (Procedure.second Nat.bits (prodCode Nat.bits Typed.naturals)).comp rest
  let cap := (Procedure.first Nat.bits Typed.naturals).comp pair
  let bits := (Procedure.second Nat.bits Typed.naturals).comp pair
  exact finishCountStmt base off cap bits

/-- Gathering the local arguments and invoking the fixed printer emits exactly
the source check, including empty words and every candidate above the bit mask. -/
noncomputable def localStmt {A : Type} {ea : A → List Bool} {base off cap : A → ℕ} {bits : A → List ℕ}
    (hb : Procedure ea Nat.bits base) (ho : Procedure ea Nat.bits off)
    (hc : Procedure ea Nat.bits cap) (hs : Procedure ea Typed.naturals bits) :
    Statement ea (fun x => finishCount (base x) (off x) (cap x) (bits x)) :=
  (printer.comp (hb.pair (ho.pair (hc.pair hs)))).congrFun (fun _ => rfl)

/-- The word's encoded length is linear in the number of addresses times
their maximum binary length. -/
theorem code_length_le (x : Input) {W B : ℕ} (hw : x.2.2.2.length ≤ W)
    (hb : x.1.bits.length ≤ B) (ho : x.2.1.bits.length ≤ B) (hc : x.2.2.1.bits.length ≤ B)
    (hbits : ∀ i ∈ x.2.2.2, i.bits.length ≤ B) :
    (code x).length+1 ≤ 10*(W+1)*(B+1) := by
  have h := listCode_length_map_bound Nat.bits id x.2.2.2 B hbits
  simp only [List.map_id_fun,id_eq] at h
  have hm := Nat.mul_le_mul_right (2*B+2) hw
  simp only [code,prodCode,pairBits_length,Typed.naturals]
  rw [show 10*(W+1)*(B+1) = 10*(W*(B+1))+10*(B+1) by ring]
  rw [show 2*B+2 = 2*(B+1) by ring,Nat.mul_left_comm _ 2,Nat.mul_left_comm W 2] at hm
  rw [show 2*B+2 = 2*(B+1) by ring,Nat.mul_left_comm _ 2] at h
  omega

/-- Any polynomial bound on the number and binary lengths of one report's
fields yields a polynomial in that same logarithmic scale for the actual local
printer. The constants do not depend on the larger directory. -/
theorem printer_polylog (C j : ℕ) : ∃ A k : ℕ, ∀ (x : Input) (L : ℕ),
    x.2.2.2.length ≤ C*(L+1)^j → x.1.bits.length ≤ C*(L+1)^j →
    x.2.1.bits.length ≤ C*(L+1)^j → x.2.2.1.bits.length ≤ C*(L+1)^j →
    (∀ i ∈ x.2.2.2, i.bits.length ≤ C*(L+1)^j) → printer.meter x ≤ A*(L+1)^k := by
  let d := printer.bound.natDegree+1
  let A := 10*(C+1)^2
  refine ⟨(2*printer.bound.eval 1+2)*A^d, (2*j)*d, fun x L hw hb ho hc hs => ?_⟩
  let R := (L+1)^j
  have hR : 1 ≤ R := Nat.one_le_pow j _ (Nat.succ_pos _)
  have hlen := code_length_le x hw hb ho hc hs
  change _ ≤ 10*(C*R+1)*(C*R+1) at hlen
  have hbnd : C*R+1 ≤ (C+1)*R := by rw [Nat.add_mul,Nat.one_mul]; omega
  have hscale : (code x).length+1 ≤ A*(L+1)^(2*j) := by
    apply hlen.trans
    calc 10*(C*R+1)*(C*R+1) ≤ 10*((C+1)*R)*((C+1)*R) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hbnd) hbnd
         _ = A*(L+1)^(2*j) := by dsimp [A,R]; rw [two_mul,pow_add]; ring
  have h1 : (code x).length+1 ≤ ((code x).length+1)^d := Nat.le_self_pow (by dsimp [d]; omega) _
  have hcost := printer.cost_pow x (show printer.bound.natDegree ≤ d by dsimp [d]; omega)
  have hout := printer.output_length_le_cost x
  simp only [id_eq] at hout
  have htop : printer.meter x ≤ (2*printer.bound.eval 1+2)*((code x).length+1)^d := by
    rw [Nat.add_mul,Nat.mul_assoc]; simp only [Procedure.meter,id_eq]; omega
  apply htop.trans
  have hh := Nat.pow_le_pow_left hscale d
  rw [Nat.mul_pow,← Nat.pow_mul] at hh
  rw [Nat.mul_assoc]
  exact Nat.mul_le_mul_left _ hh

/-- The outer invocation pays only the four source routines and the actual
clock of the fixed printer on the gathered fields. -/
theorem local_meter {A : Type} {ea : A → List Bool} {base off cap : A → ℕ} {bits : A → List ℕ}
    (hb : Procedure ea Nat.bits base) (ho : Procedure ea Nat.bits off)
    (hc : Procedure ea Nat.bits cap) (hs : Procedure ea Typed.naturals bits) (x : A) :
    (localStmt hb ho hc hs).meter x ≤ 10^32*(hb.meter x+ho.meter x+hc.meter x+hs.meter x+
      printer.meter (base x,off x,cap x,bits x)) := by
  have h₁ := Procedure.meter_pair hc hs x
  have h₂ := Procedure.meter_pair ho (hc.pair hs) x
  have h₃ := Procedure.meter_pair hb (ho.pair (hc.pair hs)) x
  apply (Procedure.meter_comp printer (hb.pair (ho.pair (hc.pair hs))) x).trans
  change 6*((hb.pair (ho.pair (hc.pair hs))).meter x+printer.meter (base x,off x,cap x,bits x)) ≤ _
  omega

end CellSparse.Packet.Emit.Finish

end BorderVNP
end Computability
end OAI
