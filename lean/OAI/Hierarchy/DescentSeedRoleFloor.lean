import OAI.Hierarchy.DescentSeedTokenStartup
import OAI.Hierarchy.DescentSeedTokenRate
import OAI.Hierarchy.DescentDatedSeedAperture

namespace OAI
/-! # The physical, ballot-independent upper fence at the first dated stage -/
namespace Hierarchy.DescentDatedSeedStartup
open DescentDyadicSpan DescentSIMDLookup DescentPackedSeed DescentSeedRoot DescentInitialHost DescentDatedAddressBook Filter
noncomputable section

def roleSourceFloor (base old copies width payload : ℕ) :=
  let pitch:=DescentPackedSeed.Primitive.pieces payload width
  let n:=old*chunks copies pitch
  let dictionary:=DescentPackedSeed.Primitive.cols width pitch
  base+span dictionary+2*span n+span n

def seededRoleFloor (base old H G copies d width payload M : ℕ) :=
  DescentSeedTokenTransposition.endAddress (roleSourceFloor base old copies width payload) old H G (2^d)
    (DescentPackedSeed.Primitive.roleBits width) (DescentPackedSeed.Primitive.pieces payload width) M

theorem initial_role_floor {F : Type} [Field F] {k p : ℕ} (X : Catalyst.Approximation F k p)
    (R s payload d H G M base : ℕ) :
    Primitive.initialEnd X R s payload d H G M base=
      seededRoleFloor base (Fintype.card (Old X)) H G R d s payload M :=rfl

theorem role_rate {ι : ℕ → Type*} {base O H G copies d width payload M : ∀ h,ι h → ℕ}
    (first : Bounded base) (vertices : Bounded O) (actors : Bounded H) (groups : Bounded G)
    (replicas : Bounded copies) (blocks : Bounded (fun h i=>2^(d h i))) (native : Bounded payload)
    (newPitch : Bounded M)
    (physical : ∃K : ℕ,∀ᶠ h : ℕ in atTop,∀i,payload h i ≤ K*h)
    (output : ∃K : ℕ,∀ᶠ h : ℕ in atTop,∀i,
      (DescentPackedSeed.Primitive.roleBits (width h i)*2^(d h i))*M h i ≤ K*h) :
    Bounded (fun h i=>seededRoleFloor (base h i) (O h i) (H h i) (G h i) (copies h i) (d h i)
      (width h i) (payload h i) (M h i)) :=by
  let a:=fun h i=>DescentPackedSeed.Primitive.roleBits (width h i)
  let A:=fun h i=>DescentPackedSeed.Primitive.pieces (payload h i) (width h i)
  have oldPitch : Bounded A:=native.of_le (fun _ _=>Nat.div_le_self ..)
  obtain ⟨K,machine⟩:=physical
  have input : ∃K : ℕ,∀ᶠ h : ℕ in atTop,∀i,a h i*A h i≤K*h :=
    ⟨K,machine.mono fun h bound i=>(DescentPackedSeed.Primitive.result_fit _ _).trans (bound i)⟩
  have dictexp : ∀ᶠ h : ℕ in atTop,∀i,digitsNeeded (width h i)*8*A h i≤K*h :=by
    filter_upwards [machine] with h bound i
    have bound':=lanes_fit (payload h i) (8*digitsNeeded (width h i))
    dsimp only [A,DescentPackedSeed.Primitive.pieces]
    apply le_trans _ ((Nat.div_le_self (payload h i) 2).trans (bound i))
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using bound'
  have count : Bounded (fun h i => chunks (copies h i) (A h i)) :=((replicas.add oldPitch).of_le (fun h i=>(Nat.div_le_self (copies h i+A h i-1) _).trans (Nat.sub_le ..)))
  have words:=(vertices.mul count).padded
  have source:=(first.add (((Bounded.const (Fintype.card DescentPackedSeed.Primitive.Plan)).mul
    (Bounded.pow_of_linear dictexp)).padded)).add ((Bounded.const 2).mul words)
  have full:=DescentSeedTokenTransposition.rate vertices actors groups blocks oldPitch newPitch
    (fun _ _=>Nat.two_pow_pos _) input output
  apply ((source.add words).add full.1).of_le
  intro h i
  unfold seededRoleFloor
  rw [DescentSeedTokenTransposition.address_affine]
  exact le_rfl

end
end Hierarchy.DescentDatedSeedStartup

end OAI
