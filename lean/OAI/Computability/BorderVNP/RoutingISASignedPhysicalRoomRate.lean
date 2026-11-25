import OAI.Computability.BorderVNP.RoutingISASignedPhysicalRoomParameters

/-! # Uniform polynomial size of the chosen signed report and task windows -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

open BorderVNP.Cube BorderVNP.Cube.Tally

private theorem vertex_before_stop (c : CubeArena.Layout) : c.vertexCap ≤ c.stop := by
  obtain ⟨_,_,v,p,b,s⟩ := c.separated
  omega

/-- A single polynomial envelope covers the chosen geometry, all report
slots and the private scratch and burst windows. The coefficients depend
only on the fixed cube format. -/
theorem parameters_polynomial (dim b h K sym : ℕ) :
    ∃ C D : ℕ, ∀ (n z : ℕ) (p : CubeArena.Sizes), 1 ≤ z → n+1 ≤ z → p.Le (4*z^2) →
      let arena := p.selected dim b h K sym
      ∀ (id : TableEntry arena.n arena.b arena.h arena.K arena.s → ℕ) (g : GeometryDirectories)
        (bundles marked params expBits gadgets w header body u v gates : ℕ),
        bundles ≤ z → marked ≤ 2*(4*z)^60 → p.teams*(params*expBits) ≤ z →
        params ≤ z → gadgets ≤ z → w ≤ z → u ≤ z → v ≤ z → gates ≤ z →
        let l : Layout := ⟨arena,id,physicalParameters arena g n bundles marked params expBits gadgets w header body⟩
        p.Le (C*z^D) ∧ l.ScalarRoom w u v gates (C*z^D) := by
  obtain ⟨e,stop⟩ := CubeArena.uniform_exponent dim b h K sym
  let D := max 61 (2*e)
  let C := max (max 8 (6^e)) (max (18*4^60+6) (argumentWidth dim b h K sym))
  refine ⟨C,D,?_⟩
  intro n z p hz hn source arena id g bundles marked params expBits gadgets w header body u v gates
    bundle mark uses par labels hw hu hv hg l
  let scale := z^D
  have c8 : 8 ≤ C := (le_max_left ..).trans (le_max_left ..)
  have c6 : 6^e ≤ C := (le_max_right ..).trans (le_max_left ..)
  have cs : 18*4^60+6 ≤ C := (le_max_left ..).trans (le_max_right ..)
  have cw : argumentWidth dim b h K sym ≤ C := (le_max_right ..).trans (le_max_right ..)
  have e61 : 61 ≤ D := le_max_left ..
  have e2 : 2*e ≤ D := le_max_right ..
  have raises (a : ℕ) (leD : a ≤ D) : z^a ≤ scale := Nat.pow_le_pow_right hz leD
  have pos : 1 ≤ scale := Nat.one_le_pow _ _ hz
  have linear : z ≤ scale := by simpa using raises 1 (by omega)
  have quadratic := raises 2 (by omega)
  have const : 4*scale ≤ C*scale := Nat.mul_le_mul_right _ (show 4 ≤ C from le_trans (by decide : 4≤8) c8)
  have simple := (Nat.le_mul_of_pos_left scale (lt_of_lt_of_le (by decide : 0<8) c8))
  have thin := linear.trans simple
  have small := (Nat.mul_le_mul_left 4 quadratic).trans const
  have bits := Nat.le_mul_of_pos_right (argumentWidth dim b h K sym) (show 0<scale by omega)
  have width : argumentWidth dim b h K sym ≤ C*scale := bits.trans
    (Nat.mul_le_mul_right _ cw)
  have p2 : 1 ≤ z^2 := Nat.one_le_pow _ _ hz
  have A : 4*z^2+2 ≤ 6*z^2 := by omega
  have V := (vertex_before_stop arena).trans ((stop _ p source).trans (Nat.pow_le_pow_left A e))
  rw [Nat.mul_pow,←pow_mul] at V
  have vertex := V.trans (Nat.mul_le_mul c6 (raises _ e2))
  rw [Nat.mul_pow] at mark
  have mBound : marked ≤ (2*4^60)*z^60 := by rwa [Nat.mul_assoc]
  have markedRoom := mBound.trans (Nat.mul_le_mul (le_trans (by decide : 2*4^60≤18*4^60+6) cs) (raises 60 (by omega)))
  have z60 : 1 ≤ z^60 := Nat.one_le_pow _ _ hz
  have add : 9*marked+6 ≤ (18*4^60+6)*z^60 := by rw [Nat.add_mul]; omega
  have supp := Nat.mul_le_mul bundle add
  rw [show z*((18*4^60+6)*z^60)=(18*4^60+6)*z^61 by ring] at supp
  have finalSupp := supp.trans (Nat.mul_le_mul cs (raises 61 e61))
  have cell := source.2.2.2.1.trans small
  obtain ⟨ab,sy,tr,ce,ca,ro,te,st⟩ := source
  refine ⟨⟨ab.trans small,sy.trans small,tr.trans small,ce.trans small,ca.trans small,ro.trans small,
    te.trans small,st.trans small⟩,⟨?_,par.trans thin,?_,?_,hw.trans thin,hu.trans thin,hv.trans thin,hg.trans thin⟩⟩
  · exact ⟨cell,bundle.trans thin,markedRoom,uses.trans thin,labels.trans thin,hw.trans thin,vertex,width,finalSupp⟩
  · exact (Nat.pow_le_pow_left hn 2).trans (quadratic.trans simple)
  · exact hn.trans thin

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
