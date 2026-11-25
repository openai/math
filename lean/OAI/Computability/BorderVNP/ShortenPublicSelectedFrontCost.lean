import OAI.Computability.BorderVNP.ShortenPublicSelectedFront

/-!
# Descriptor-linear gate cost of the complete physical selection circuit

At positive cover depth the input payload, field width and sort-key width
are polynomial in the logarithm of the expanded size and tile count. The
merged rows and the tile histograms enter only through a single linear factor.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicRelative.FrontCosts

private theorem lane_term {X R Y W e p : ℕ} (a : ℕ) (hx : X ≤ R) (hy : Y ≤ W) (hW : 1 ≤ W) (hp : p ≤ e) :
    X*a*Y^p ≤ (R*W^e)*a := by
  calc
    _ ≤ R*a*W^e := Nat.mul_le_mul (Nat.mul_le_mul_right a hx)
      ((Nat.pow_le_pow_left hy _).trans (Nat.pow_le_pow_right hW hp))
    _ = _ := by ac_rfl

private theorem bound_width (a : FrontCosts) (k V E w data kinds q l n vol T W : ℕ)
    (hw : w+1 ≤ W) (hs : Nat.clog 2 (k*V+2*(k*E))+w+data+1 ≤ W)
    (hr : l+2*n+1 ≤ W) (ht : Nat.clog 2 (T+vol+2)+1 ≤ W) (hsel : l+w+1 ≤ W) :
    let R := k*V+2*(k*E)+k*(vol+1)+1
    let e := 3+a.readerDegree+a.histogramDegree+a.selectorDegree+a.inverseDegree
    a.bound k V E w data kinds q l n vol T ≤
      (R*W^e)*(909+2*kinds+a.reader+a.histogram+a.selector+q*a.inverse) := by
  intro R e
  let U := R*W^e
  have he : 1 ≤ W := by omega
  have hR : 1 ≤ R := by dsimp [R]; omega
  have hU : R ≤ U := Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ he)
  have hrow : k*E ≤ R := by dsimp [R]; omega
  have hsite : k*V+2*(k*E)+1 ≤ R := by dsimp [R]; omega
  have hh : k*E+k*(vol+1) ≤ R := by dsimp [R]; omega
  have hk : k ≤ R := by dsimp [R]; rw [Nat.mul_add,Nat.mul_one]; omega
  have hv : k*vol ≤ R := by dsimp [R]; rw [Nat.mul_add,Nat.mul_one]; omega
  have c₂ := lane_term 600 hrow hw he (show 2 ≤ e by dsimp [e]; omega)
  have c₃ := lane_term 300 hsite hs he (show 3 ≤ e by dsimp [e]; omega)
  have cR := lane_term a.reader hrow hr he (show a.readerDegree ≤ e by dsimp [e]; omega)
  have cH := lane_term a.histogram hh ht he (show a.histogramDegree ≤ e by dsimp [e]; omega)
  have cS := lane_term a.selector hv hsel he (show a.selectorDegree ≤ e by dsimp [e]; omega)
  have cI := lane_term (q*a.inverse) hk ((by omega : l+1 ≤ l+2*n+1).trans hr) he
    (show a.inverseDegree ≤ e by dsimp [e]; omega)
  have cK := Nat.mul_le_mul_right (2*kinds+3) (hrow.trans hU)
  have h1 := hR.trans hU
  have hfan := hk.trans hU
  change a.bound k V E w data kinds q l n vol T ≤ U*_
  dsimp only [bound]
  change _ ≤ U*_ at c₂ c₃ cR cH cS cI cK
  nlinarith only [c₂,c₃,cR,cH,cS,cI,cK,h1,hfan]

/-- One copy of each merged site/cable and one tile-volume per child,
multiplied by a polynomial in the bit length of the expanded size. The
coefficients precede the tree fan-in, cover depth and row capacities. -/
theorem bound_le (a : FrontCosts) (kinds q n G g : ℕ) :
    ∃ A p : ℕ, ∀ (k V E w data l vol T : ℕ), k*V ≤ T → k*E ≤ T → w ≤ Nat.clog 2 (T+1) →
      l ≤ Nat.clog 2 vol+2 → data ≤ G*(l+2*n+1)^g →
      a.bound k V E w data kinds q l n vol T ≤
        (k*V+2*(k*E)+k*(vol+1)+1)*A*(Nat.clog 2 (T+vol+2)+1)^p := by
  let M := G*(3+2*n)^g+2*n+8
  let e := 3+a.readerDegree+a.histogramDegree+a.selectorDegree+a.inverseDegree
  let C := 909+2*kinds+a.reader+a.histogram+a.selector+q*a.inverse
  refine ⟨M^e*C,(g+1)*e,?_⟩
  intro k V E w data l vol T sites rows width depth payload
  let L := Nat.clog 2 (T+vol+2)+1
  have hL : 1 ≤ L := Nat.le_add_left _ _
  have power : L ≤ L^(g+1) := by simpa only [pow_one] using Nat.pow_le_pow_right hL (by omega : 1 ≤ g+1)
  have hword : w ≤ L := width.trans ((Nat.clog_mono_right 2 (by omega : T+1 ≤ T+vol+2)).trans (Nat.le_succ _))
  have hsort : Nat.clog 2 (k*V+2*(k*E)) ≤ L+2 := by
    apply Nat.clog_le_of_le_pow
    rw [pow_add]
    have padded : k*V+2*(k*E) ≤ (T+vol+2)*2^2 := by omega
    exact padded.trans (Nat.mul_le_mul_right _ ((Nat.le_pow_clog (by decide) (T+vol+2)).trans
      (Nat.pow_le_pow_right (by decide) (Nat.le_succ _))))
  have logvol := Nat.clog_mono_right 2 (by omega : vol ≤ T+vol+2)
  have hdep : l ≤ 3*L := by dsimp [L]; omega
  have hn := Nat.le_mul_of_pos_right (2*n) hL
  have hdeep : l+2*n+1 ≤ (3+2*n)*L := by
    dsimp [L] at hL hdep hn ⊢
    rw [Nat.add_mul]
    omega
  have hd : data ≤ (G*(3+2*n)^g)*L^(g+1) := calc
    _ ≤ G*((3+2*n)*L)^g := payload.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hdeep _))
    _ = (G*(3+2*n)^g)*L^g := by rw [mul_pow]; ac_rfl
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hL (Nat.le_succ _))
  let W := M*L^(g+1)
  have hW : (G*(3+2*n)^g)*L^(g+1) + 2*n*L^(g+1) + 8*L^(g+1) = W := by simp [W,M,Nat.add_mul]
  have hn' := Nat.le_mul_of_pos_right (2*n) (hL.trans power)
  have h := bound_width a k V E w data kinds q l n vol T W (by omega) (by omega)
    (by omega) (by change L ≤ W; omega) (by omega)
  refine h.trans_eq ?_
  change (_*(M*L^(g+1))^e)*C = _*(M^e*C)*L^((g+1)*e)
  rw [mul_pow,← pow_mul]
  ring

end Shortening.PublicRelative.FrontCosts

end BorderVNP
end Computability
end OAI
