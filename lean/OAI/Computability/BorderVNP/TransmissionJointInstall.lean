import OAI.Computability.BorderVNP.TransmissionJointReads

/-! # Compatibility of the joint physical input with each native striped reader -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open RoutingISA RoutingISA.Pins

variable {D : Packing.Directory.Layout} {start a team : ℕ} {boot geom : GeometryAdvice.Stripe}
    {bootBits geomBits : List Bool} {strings : Fin D.entries → Fin D.description → Bool}
    {L : Pins.Layout} {F : Pins.ProcessorFields L}

/-- Installing the requested serialized public payload over the jointly constructed
processor fields recovers exactly the existing physical fields, including the other
stripe, the common program prefix and all private tail words. -/
theorem JointImage.stripe_install_eq (im : JointImage D start a boot geom bootBits geomBits strings team F)
    (first : Bool) (target : GeometryAdvice.Stripe) (xs : List Bool)
    (pick : if first then target = boot ∧ xs = bootBits else target = geom ∧ xs = geomBits)
    (pos : 0 < target.width) (cap : xs.length ≤ L.processors*target.width) :
    target.install F xs = F := by
  have keep (p : Fin L.processors) : target.literal xs p.val (F.literal p) = F.literal p := by
    apply List.ext_getElem
    · exact target.literal_length ..
    · intro j _ hj
      simp only [GeometryAdvice.Stripe.literal,List.getElem_ofFn]
      split
      next hit =>
        let t := j-target.offset
        have ht : t < target.width := by dsimp only [t]; omega
        let i : Fin xs.length := ⟨p.val*target.width+t, hit.2.2⟩
        have hp : i.val/target.width = p.val := by
          simp only [i,Nat.mul_comm p.val target.width,Nat.mul_add_div pos,Nat.div_eq_of_lt ht,Nat.add_zero]
        have hj' : target.offset+i.val%target.width = j := by
          dsimp only [i]
          rw [Nat.mul_comm p.val target.width,Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt ht]
          dsimp only [t]; omega
        let p' : Fin L.processors := ⟨i.val/target.width,(Nat.div_lt_iff_lt_mul pos).mpr (i.isLt.trans_le cap)⟩
        have eq : p' = p := Fin.ext hp
        have read := im.stripe_get first target xs pick pos cap i
        change (F.literal p')[target.offset+i.val%target.width]? = some xs[i.val] at read
        rw [eq,hj',List.getElem?_eq_getElem hj,Option.some_inj] at read
        exact read.symm
      next => rfl
  cases F
  unfold GeometryAdvice.Stripe.install
  congr 1
  exact funext keep

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI
