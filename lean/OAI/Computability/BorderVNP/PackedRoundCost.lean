import OAI.Computability.BorderVNP.PackedCheckedGeometry
import OAI.Computability.BorderVNP.ShortenPublicPopulationBudget

/-! # Uniform sparse cost of the complete checked successor

The population, exclusive offsets and all inverse-seed reads run sorting networks on
rectangles of real rows and bins. Their gate bounds and the fixed paid template costs
are linear in the site, cable and seed counts together, up to a polynomial in the
address and count widths.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.DirectoryCircuit

open Shortening Shortening.SeedIntervals Shortening.StaticRows Shortening.PublicEndpoints.Successor
open Crossing BankCircuit

private theorem power_le {x l p j : ℕ} (hx : x ≤ l) (hl : 1 ≤ l) (hj : j ≤ p) :
    x^j ≤ l^p := (Nat.pow_le_pow_left hx _).trans (Nat.pow_le_pow_right hl hj)

private theorem offset_lanes (b k w : ℕ) :
    (k+w)*3 + ((w+b)+1+k) + b^2*(24*((w+b)+1+k)+1) + w*(60*k+40*w+63) +
      b^2*(24*(w+b)+1) ≤ 200*(b+k+w+1)^3 := by ring_nf; omega

private theorem padding (m : ℕ) : 2^(Nat.clog 2 m) ≤ 2*(m+1) := by
  by_cases hm : m = 0
  · simp [hm]
  · exact (TeamSorting.padding_lt_twice (Nat.pos_of_ne_zero hm)).le.trans (by omega)

private theorem counts_costs {σ : Type*} {A : Type} [Fintype σ] [Fintype A] {M k w l s : ℕ}
    (p : PublicPopulation.Pins (Fin M) σ k w) (code : A ↪ Fin (2^k))
    (hl : 1 ≤ l) (hs : 3 ≤ s) (words : Nat.clog 2 (Fintype.card A+M)+k+w+1 ≤ l) :
    let Q := Fintype.card A+M+1
    (PublicPopulation.offsets p).size ≤ 1+400*Q*l^s ∧
      (PublicPopulation.frame p code).size ≤ 400*Q*l^s ∧
      2*Q*PublicPopulation.laneCost (Nat.clog 2 (Fintype.card A+M)) k w ≤ 400*Q*l^s := by
  intro Q
  let b := Nat.clog 2 M
  have hb : b ≤ Nat.clog 2 (Fintype.card A+M) := Nat.clog_mono_right _ (Nat.le_add_left _ _)
  have h3 := power_le (show b+k+w+1 ≤ l by omega) hl hs
  have hq : 2^b ≤ 2*Q := (padding M).trans (by dsimp [Q]; omega)
  have h : (PublicPopulation.offsets p).size ≤ 1 + 2*Q*(200*l^s) :=
    (PublicPopulation.offsets_size p).trans (Nat.add_le_add_left
      (Nat.mul_le_mul hq ((offset_lanes _ _ _).trans (Nat.mul_le_mul_left 200 h3))) 1)
  have hc := (PublicPopulation.laneCost_le (Nat.clog 2 (Fintype.card A+M)) k w).trans
    (Nat.mul_le_mul_left 200 (power_le words hl hs))
  have sort : 2*Q*PublicPopulation.laneCost (Nat.clog 2 (Fintype.card A+M)) k w ≤ 400*Q*l^s :=
    (Nat.mul_le_mul_left _ hc).trans_eq (by ring)
  have hp := PublicPopulation.frame_size p code
  simp only [Fintype.card_fin,Nat.add_comm M (Fintype.card A)] at hp
  exact ⟨h.trans_eq (by ring), hp.trans sort, sort⟩

private theorem guard_cost (t w l p : ℕ) (hl : 1 ≤ l) (hw : w+Nat.clog 2 (t+1)+1 ≤ l) (hp : 2 ≤ p) :
    guardBudget t w ≤ ((t+1)+(2*t+1)*100+33)*l^p := by
  let W := w+Nat.clog 2 (t+1)
  have h1 : W ≤ l^p := by simpa only [pow_one] using power_le (j := 1) (show W ≤ l from by omega) hl (show 1 ≤ p from by omega)
  have h2 := power_le (show W+1 ≤ l from hw) hl hp
  have hpos := Nat.one_le_pow p l hl
  change (t+1)*W + (2*t+1)*(100*(W+1)^2) + (30*W+3) ≤ _
  nlinarith only [Nat.mul_le_mul_left (t+1) h1, Nat.mul_le_mul_left ((2*t+1)*100) h2,
    h1,hpos]

/-- Concrete single-round estimate, with constants before the variable level, seed and port
types. The incoming site batch is charged separately and can be shared across all outputs. -/
theorem round_cost_polylog {D m : ℕ} {K : Type*} [Field K] (e : PaidIdentity K D m)
    (C E C' E' G H : ℕ) :
    ∃ F s : ℕ, ∀ {A : Type} {σ : Type*} [Fintype A] [Fintype σ] (M V k w d l : ℕ)
      (p : PublicPopulation.Pins (Fin M) σ k w) (code : A ↪ Fin (2^k)), 1 ≤ l → d+1 ≤ l →
      Nat.clog 2 (Fintype.card A+M)+k+w+1 ≤ l → w+Nat.clog 2 (e.count+1)+1 ≤ l →
      let a := Fintype.card A
      roundSourceCost a D M k w C E C' E' e.count (PublicPopulation.offsets p).size (PublicPopulation.frame p code).size +
        ((1+siteCapacity e V a)*G*(d+1)^H + (cost e M a w + 3*edgeCapacity e M a)) ≤ (V+M+a+1)*F*l^s := by
  let s := max (max E E') (max H 3)
  let b := Fintype.card (Band D)
  let f := Fintype.card (Band D × Bool)
  let v := Fintype.card (TemplateSite e)
  let z := Fintype.card (TemplateEdge e)
  let ops := ∑ u : TemplateEdge e, BankCircuit.nodeBudget e u
  let guard := (e.count+1)+(2*e.count+1)*100+33
  let scatter := 400+2+C+1+PoolCircuit.endpointNodes D*100+1+f*400
  let src := 401+scatter+b*48+1+b*3300+(1+D*400)+(400+2+C')+(1+guard)+3
  let geom := (2+v)*G + (3+(2*D+1)*3*(2*StaticTerminalCircuit.nodeBudget e*100+256)+4*ops*100) +
    3*(3*(2*D+1)+z)
  refine ⟨src+geom,s,?_⟩
  intro A σ _ _ M V k w d l pins code hl hd hw hg a
  let N := V+M+a+1
  let L := l^s
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hL : 1 ≤ L := Nat.one_le_pow s l hl
  have ha : a ≤ N := by dsimp [N]; omega
  have hM : M ≤ N := by dsimp [N]; omega
  have hV : V ≤ N := by dsimp [N]; omega
  have hab : a+M+1 ≤ N := by dsimp [N]; omega
  have h3 : 3 ≤ s := by dsimp [s]; omega
  have hw' : w+1 ≤ l := by omega
  have h₁ : w ≤ L := by simpa only [pow_one] using power_le (j := 1) (show w ≤ l from by omega) hl (show 1 ≤ s from by omega)
  have h₂ : (w+1)^2 ≤ L := power_le hw' hl (by omega)
  have hE : (w+1)^E ≤ L := power_le hw' hl (by dsimp [s]; omega)
  have hE' : (w+1)^E' ≤ L := power_le hw' hl (by dsimp [s]; omega)
  have hH : (d+1)^H ≤ L := power_le hd hl (by dsimp [s]; omega)
  obtain ⟨offset,pop,sort⟩ := counts_costs pins code hl h3 hw
  have hq : 400*(a+M+1)*L ≤ 400*N*L := Nat.mul_le_mul_right L (Nat.mul_le_mul_left 400 hab)
  have ho : (PublicPopulation.offsets pins).size ≤ 401*N*L :=
    (offset.trans (Nat.add_le_add_left hq 1)).trans (by nlinarith only [Nat.mul_pos hN hL])
  have hpop := pop.trans hq
  have hsort := sort.trans hq
  have one : 1 ≤ N*L := Nat.mul_pos hN hL
  have Aprod (t : ℕ) {x : ℕ} (hx : x ≤ L) : a*(t*x) ≤ N*(t*L) :=
    Nat.mul_le_mul ha (Nat.mul_le_mul_left t hx)
  have Mprod (t : ℕ) {x : ℕ} (hx : x ≤ L) : M*t*x ≤ N*t*L :=
    Nat.mul_le_mul (Nat.mul_le_mul_right _ hM) hx
  have hsc : PoolCircuit.scatterCost a M D C E k w ≤ scatter*N*L := by
    unfold PoolCircuit.scatterCost
    dsimp only [scatter,f]
    nlinarith only [hsort, one, Aprod C hE, Aprod (PoolCircuit.endpointNodes D*100) h₂,
      Nat.mul_le_mul_left (Fintype.card (Band D × Bool)) hsort]
  have hg' := guard_cost e.count w l s hl hg (by omega)
  have hguard : a*guardBudget e.count w ≤ N*(guard*L) := Nat.mul_le_mul ha hg'
  have haL : a ≤ N*L := ha.trans (Nat.le_mul_of_pos_right _ hL)
  have hs : roundSourceCost a D M k w C E C' E' e.count (PublicPopulation.offsets pins).size
      (PublicPopulation.frame pins code).size ≤ src*N*L := by
    unfold roundSourceCost
    dsimp only [src,b]
    nlinarith only [ho,hsc,Mprod (Fintype.card (Band D)*48) h₁,one,
      Mprod (Fintype.card (Band D)*3300) h₂,Nat.mul_le_mul_left D hsort,hpop,Aprod C' hE',hguard,haL]
  have hsite : 1+siteCapacity e V a ≤ (2+v)*N := by
    change 1+(V+a*v) ≤ _
    nlinarith only [hN,hV,Nat.mul_le_mul_right v ha]
  have hgeo := Nat.mul_le_mul (Nat.mul_le_mul_right G hsite) hH
  have hterm : 1+3*w ≤ 4*L := by omega
  have hnodes : 2*StaticTerminalCircuit.nodeBudget e*(100*(w+1)^2)+64*(1+3*w) ≤
      (2*StaticTerminalCircuit.nodeBudget e*100+256)*L := by
    nlinarith only [Nat.mul_le_mul_left (2*StaticTerminalCircuit.nodeBudget e*100) h₂,hterm]
  have htcost := Nat.mul_le_mul (Nat.mul_le_mul_right 3 (Nat.mul_le_mul_right (2*D+1) hM)) hnodes
  have hcost : cost e M a w ≤ (3+(2*D+1)*3*(2*StaticTerminalCircuit.nodeBudget e*100+256)+4*ops*100)*N*L := by
    change 3 + M*(2*D+1)*3*(2*StaticTerminalCircuit.nodeBudget e*(100*(w+1)^2)+64*(1+3*w)) +
      a*(4*ops*(100*(w+1)^2)) ≤ _
    nlinarith only [one,htcost,Aprod (4*ops*100) h₂]
  have hedge : edgeCapacity e M a ≤ (3*(2*D+1)+z)*N := by
    rw [edgeCapacity_eq]
    change 3*(2*D+1)*M+z*a ≤ _
    nlinarith only [Nat.mul_le_mul_left (3*(2*D+1)) hM,Nat.mul_le_mul_left z ha]
  have heL := hedge.trans (Nat.le_mul_of_pos_right _ hL)
  change _ ≤ N*(src+geom)*L
  dsimp only [geom]
  nlinarith only [hs,hgeo,hcost,heL]

end Packing.DirectoryCircuit

end BorderVNP
end Computability
end OAI
