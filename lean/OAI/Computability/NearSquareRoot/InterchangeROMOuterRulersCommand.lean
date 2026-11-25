import OAI.Computability.NearSquareRoot.InterchangeROMOuterRulersPrice
import OAI.Computability.NearSquareRoot.InterchangeROMBankWires

/-! # Named entry and return commands for the native grouped center -/

namespace OAI
namespace Computability
namespace NearSquareRoot

set_option maxHeartbeats 1500000

namespace InterchangeROMOuter

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip IntegerMultiplication.Loom
  CommonRegisters GeneratorSyntax InterchangeROMExpose InterchangeROMRecursion InterchangeAddress Space

noncomputable def entry (W b n : ℕ) :=
  Wire.bank W b n InterchangeROMBankRulers.command (InterchangeROMBank.bank b W)
noncomputable def leave (W b n : ℕ) :=
  Wire.unbank W b n InterchangeROMBankRulers.command (InterchangeROMBank.unbank b W)

attribute [local irreducible] InterchangeROMBank.bank InterchangeROMBank.unbank
  InterchangeROMBankRulers.command Wire.bank Wire.unbank

theorem effective_entry {A : Type} [Primcodable A] {W b n : A → ℕ}
    (w : Computable W) (h : Computable b) (v : Computable n) :
    Effective ltr (fun x => entry (W x) (b x) (n x)) := by
  let pair (x:A) := (b x,W x)
  have base : Computable pair := h.pair w
  have use := Computable.comp (f:=fun u : ℕ × ℕ => file ltr (InterchangeROMBank.bank u.1 u.2)) InterchangeROMBank.effective_bank base
  unfold entry
  exact Wire.effective_bank (split:=fun x => InterchangeROMBank.bank (b x) (W x)) InterchangeROMBankRulers.command w h v
    use

theorem effective_leave {A : Type} [Primcodable A] {W b n : A → ℕ}
    (w : Computable W) (h : Computable b) (v : Computable n) :
    Effective ltr (fun x => leave (W x) (b x) (n x)) := by
  let pair (x:A) := (b x,W x)
  have base : Computable pair := h.pair w
  have use := Computable.comp (f:=fun u : ℕ × ℕ => file ltr (InterchangeROMBank.unbank u.1 u.2)) InterchangeROMBank.effective_unbank base
  unfold leave
  exact Wire.effective_unbank (merge:=fun x => InterchangeROMBank.unbank (b x) (W x)) InterchangeROMBankRulers.command w h v
    use

theorem wire_registers : ∃ R, ∀ W b n, Within R (entry W b n) ∧ Within R (leave W b n) := by
  obtain ⟨A,_,ha⟩ := InterchangeROMBank.bank_within
  obtain ⟨B,_,hb⟩ := InterchangeROMBank.unbank_within
  obtain ⟨R,hA,hB,hh⟩ := ((Filter.eventually_ge_atTop A).and
    ((Filter.eventually_ge_atTop B).and (Wire.registers InterchangeROMBankRulers.command))).exists
  exact ⟨R,fun W b n => hh W b n _ _ (RegisterSelect.within_mono hA _ (ha b W))
    (RegisterSelect.within_mono hB _ (hb b W))⟩

noncomputable def wireCost (K C k W b n data : ℕ) :=
  (K+InterchangeROMBank.bankTime b W+InterchangeROMBank.unbankTime b W+2)*
    (8*(C*(W+b+n+1)^k+data+2))

theorem computable_wireCost {A : Type} [Primcodable A] (K C k : ℕ) {W b n data : A → ℕ}
    (hw : Computable W) (hb : Computable b) (hn : Computable n) (hd : Computable data) :
    Computable (fun x => wireCost K C k (W x) (b x) (n x) (data x)) := by
  let add {f g : A → ℕ} (a : Computable f) (c : Computable g) := Primrec.nat_add.to_comp.comp a c
  let mul {f g : A → ℕ} (a : Computable f) (c : Computable g) := Primrec.nat_mul.to_comp.comp a c
  have charges := add (add (add (Computable.const K) (InterchangeROMBank.primrec_bankTime.to_comp.comp hb hw))
    (InterchangeROMBank.primrec_unbankTime.to_comp.comp hb hw)) (.const 2)
  have wbn := add (add (add hw hb) hn) (Computable.const 1)
  have pwr (e : ℕ) : Computable fun x => (W x+b x+n x+1)^e := by
    induction e with
    | zero => simpa only [pow_zero] using (Computable.const (α:=A) 1)
    | succ e ih => simpa only [pow_succ] using mul ih wbn
  exact mul charges (mul (.const 8) (add (add (mul (.const C) (pwr k)) hd) (.const 2)))

private theorem wireAt {X : Type} (j : Job X) (parent c : Cmd) {u v : Tree} {t K : ℕ}
    (h : ∀ env, Wire.LocalFits env c u v t) (ht : t+u.count ≤ K) :
    At parent c j [] [] u v K 0 0 := by
  apply At.local_run
  intro env deck base hd
  exact (BoundedFits.of_fits (h _ deck base hd) (cap:=base+K) (depth:=K)
    (fun i => by have := hd.pile 0 u i; omega) (by omega)).mono (by omega) le_rfl le_rfl

/-- If both flat and grouped buffers occupy at most the indicated multiple
of the native volume, entry and return fit one computably priced local step.
The bounds apply to the emitted commands under the actual recursive binder. -/
theorem priced_wires : ∃ k C K : ℕ, ∀ (i : Input) (W data : ℕ) (flat banked changed back : Tree),
    let tag := send (centerHeader i)
    let out := Wire.out i W
    let volume := localMass i.req k+1
    let price := wireCost K C k W i.b i.n data*volume
    flat.count ≤ data*volume → banked.count ≤ data*volume →
    changed.count ≤ data*volume → back.count ≤ data*volume →
    InterchangeROMBank.Run (InterchangeROMBank.bank i.b W) (InterchangeROMBank.bankTime i.b W)
      InterchangeROMBank.bankSpace (.fork out.1 flat) banked →
    InterchangeROMBank.Run (InterchangeROMBank.unbank i.b W) (InterchangeROMBank.unbankTime i.b W)
      InterchangeROMBank.unbankSpace (.fork out.2.1 changed) back →
    ∀ parent, At parent (entry W i.b i.n) (Request.job i.b) [] [] (.fork tag flat)
      (.fork tag (.fork out.2.2 banked)) price 0 0 ∧
      At parent (leave W i.b i.n) (Request.job i.b) [] [] (.fork tag (.fork out.2.2 changed))
        (.fork tag back) price 0 0 := by
  obtain ⟨k,C,ruler⟩ := Wire.ruler_cost
  obtain ⟨E,head⟩ := Wire.fits_bank
  obtain ⟨L,tail⟩ := Wire.fits_unbank
  let K := max E L
  refine ⟨k,C,K,?_⟩
  intro i W data flat banked changed back tag out vol price hf hb hc hback enter exit parent
  let a := C*(W+i.b+i.n+1)^k
  obtain ⟨hs,hp,hr⟩ := ruler i W
  change size out ≤ a*vol at hs
  change (Wire.template W i.b i.n).count+tag.count+1 ≤ a*vol at hp
  have tags : out.1.count+out.2.1.count+out.2.2.count ≤ size out := by
    change _ ≤ out.1.count+(out.2.1.count+out.2.2.count+1)+1; omega
  let B := 8*(a+data+2)*vol
  have vs : 1 ≤ vol := Nat.succ_pos _
  have expand : B = 8*(a*vol+data*vol+2*vol) := by dsimp [B]; ring
  have checks : Wire.work tag flat out W i.b i.n ≤ B ∧
      Wire.work tag (.fork out.2.2 changed) out W i.b i.n ≤ B ∧
      InterchangeROMBank.amount (.fork out.1 flat) banked ≤ B ∧
      InterchangeROMBank.amount (.fork out.2.1 changed) back ≤ B ∧
      a*vol+(.fork tag flat : Tree).count ≤ B ∧ a*vol+(.fork tag (.fork out.2.2 changed) : Tree).count ≤ B := by
    rw [expand]
    dsimp only [Wire.work,InterchangeROMBank.amount,Tree.count]; omega
  obtain ⟨h1,h2,h3,h4,h5,h6⟩ := checks
  let t := InterchangeROMBank.bankTime i.b W
  let u := InterchangeROMBank.unbankTime i.b W
  have ep : E * Wire.work tag flat out W i.b i.n ≤ K*B :=
    Nat.mul_le_mul (le_max_left ..) h1
  have lp : L * Wire.work tag (.fork out.2.2 changed) out W i.b i.n ≤ K*B :=
    Nat.mul_le_mul (le_max_right ..) h2
  have sum : price = K*B+t*B+u*B+2*B := by
    change (K+t+u+2)*(8*(a+data+2))*vol = _
    dsimp [B]; ring
  constructor
  · apply wireAt _ _ _ (fun env => head W i.b i.n _ _ tag flat banked out _ _ env (hr env)
      (fun d base live => (enter env d base live).fits))
    have := Nat.mul_le_mul_left t h3
    rw [sum]; change E*_+a*vol+t*_+_ ≤ _; omega
  · apply wireAt _ _ _ (fun env => tail W i.b i.n _ _ tag out.2.2 changed back out _ _ env (hr env)
      (fun d base live => (exit env d base live).fits))
    have := Nat.mul_le_mul_left u h4
    rw [sum]; change L*_+a*vol+u*_+_ ≤ _; omega

end InterchangeROMOuter

end NearSquareRoot
end Computability
end OAI
