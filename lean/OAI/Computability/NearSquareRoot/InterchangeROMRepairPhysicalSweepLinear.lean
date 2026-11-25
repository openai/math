import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalSweepPriceHeader

/-! # Template-computable linear time and peak space for a compiled spectral sweep -/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section
namespace InterchangeROMRepair.Sweep

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Port IntegerMultiplication.Adic IntegerMultiplication.Loom
  CommonRegisters Space InterchangeROMAddress InterchangeAddress GeneratorSyntax
open InterchangeROMRepair.Physical (Allowance)

def rate (b n p half : ℕ) (inv : Bool) := headerPrice b n+scanRate p half inv

theorem computable_rate {X : Type} [Primcodable X] {b n p half : X → ℕ} {inv : X → Bool}
    (hb : Computable b) (hn : Computable n) (hp : Computable p) (hh : Computable half) (hi : Computable inv) :
    Computable (fun x => rate (b x) (n x) (p x) (half x) (inv x)) :=
  Primrec.nat_add.to_comp.comp (computable_headerPrice hb hn) (computable_scanRate hp hh hi)

variable {I J D : Type} [DecidableEq J] {b n : ℕ}
  (ord : J ≃ Fin n) (P G B : I → Dims.Tape) (f l : I → ℕ) (pay : I → Series D)
  (j : J) (p half : ℕ) (inv : Bool)
  (x : (i : I) → domain (J:=J) (b:=b) P G B f i → D → ZMod (p+1)) (i : I)

theorem native_linear_cost (ac : Allowance) (hb : 2 ≤ b)
    (ok : ∀ k ∈ P i ++ G i ++ B i, 2 ≤ k ∧ k ≤ b) (hw : (pay i).count ≤ l i) :
    let rows := layoutRows (b:=b) ord P G B f i
    let a := nativeCost ord P G B f l pay j p half inv x i ac
    let v := rate b n p half inv*(rows.count*(l i+1)+1)
    a.time ≤ ac.time+v ∧ a.cap ≤ ac.cap+v ∧ a.depth ≤ ac.depth+v := by
  let q := request ord P G B f l pay j p x i
  let rows := layoutRows (b:=b) ord P G B f i
  let a := nativeCost ord P G B f l pay j p half inv x i ac
  let T := shapeCharge b n (ord j) (header (f i) (P i) (G i) (B i)) q.header rows.count
  let V := rows.count*(l i+1)+1
  have H : T ≤ headerPrice b n*rows.count :=
    shapeCharge_le ord P G B f l j (data P G B f pay p x) i hb ok
  have hv : rows.count ≤ V := by dsimp [V]; rw [Nat.mul_add,Nat.mul_one]; omega
  have bound : T ≤ headerPrice b n*V := H.trans (Nat.mul_le_mul_left _ hv)
  have hh := native_cost_le ord P G B f l pay j p half inv x i hw ac
  dsimp only at hh
  rw [charge_eq] at hh
  change a.time ≤ ac.time+(T+scanRate p half inv*V) ∧ a.cap ≤ ac.cap+(T+scanRate p half inv*V) ∧
    a.depth ≤ ac.depth+(T+scanRate p half inv*V) at hh
  change a.time ≤ ac.time+rate b n p half inv*V ∧ a.cap ≤ ac.cap+rate b n p half inv*V ∧
    a.depth ≤ ac.depth+rate b n p half inv*V
  rw [rate,Nat.add_mul]
  omega

/-- Run the selected spectral digit transformation with one native interchange callback. -/
theorem native_linear (parent : Cmd) (env : Env) (ac : Allowance) (hb : 2 ≤ b)
    (ok : ∀ k ∈ P i ++ G i ++ B i, 2 ≤ k ∧ k ≤ b) (hw : (pay i).count ≤ l i)
    (hc : let q := request ord P G B f l pay j p x i
      Run (parent::env) parent ((Request.job b).issue q) ((Request.job b).reply q) ac) :
    let rows := layoutRows (b:=b) ord P G B f i
    let h := send (header (f i) (P i) (G i) (B i))
    Run (parent::env) (nativeCommand b n (ord j) p half inv) (.fork h (row rows (pay i) (x i)))
      (row rows (pay i) fun k d =>
        InterchangeSpectralRequest.advance inv (half : ZMod (p+1)) j (fun k => x i k d) k)
      (charged ac (rate b n p half inv*(rows.count*(l i+1)+1))) := by
  apply native_linear_of_shape ord P G B f l pay j p half inv x i parent env ac _ hb
    (fun k hk => (ok k (by simp [hk])).1) (fun k hk => (ok k (by simp [hk])).1)
    (fun k hk => (ok k (by simp [hk])).1) hw _ hc
  exact shapeCharge_le ord P G B f l j (data P G B f pay p x) i hb ok

end InterchangeROMRepair.Sweep

end

end NearSquareRoot
end Computability
end OAI
