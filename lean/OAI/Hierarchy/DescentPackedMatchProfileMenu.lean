import OAI.Hierarchy.DescentPackedMatchProfilePass

namespace OAI
/-! # The fixed shift, count, and dense-window ROM and their physical invoice -/

namespace Hierarchy.DescentPacking.PackedMatch.ProfileTable
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {w : ℕ}

def install {d : ℕ} (base : ℕ) (x : Cell d→Word w) (m : Memory w) (p : ℕ) : Word w :=
  if live : base≤p ∧ p<base+2^d then x ⟨p-base,by omega⟩ else m p

theorem install_hit {d : ℕ} (base : ℕ) (x : Cell d→Word w) (m : Memory w) (j : Cell d) :
    install base x m (base+j.val)=x j := by
  have low := Nat.le_add_right base j.val
  have high := Nat.add_lt_add_left j.isLt base
  simp only [install,dite_eq_left (And.intro low high),Nat.add_sub_cancel_left]

theorem install_low {d : ℕ} (base : ℕ) (x : Cell d→Word w) (m : Memory w) {j : ℕ} (low : j<base) :
    install base x m j=m j := dite_eq_right (fun h=>low.not_ge h.1)

def banks (lo a b : ℕ) : Tables :=
  ⟨⟨lo+2^a,a⟩,⟨lo+2*(2^a),b⟩,⟨lo+2*(2^a)+2^b,b⟩,⟨lo+2*(2^a)+2*(2^b),bits a b⟩⟩

def footprint (a b : ℕ) := 2*2^a+2*2^b+2^(bits a b)

def mount (s : Shape) (M R lo : ℕ) (m : Memory w) :=
  let a:=s.outputBits*M
  let b:=s.digit*R
  let T:=banks lo a b
  let a₀:=install lo (fun i=>(chunkCount s M i:Word w)) m
  let a₁:=install T.topology.base (fun i : Cell a=>((2^(b+(b+b))*i.val:ℕ):Word w)) a₀
  let a₂:=install T.offset.base (fun i : Cell b=>((2^(b+b)*i.val:ℕ):Word w)) a₁
  let a₃:=install T.low.base (fun i : Cell b=>((2^b*i.val:ℕ):Word w)) a₂
  install T.result.base (fun i=>(table s M R i).val) a₃

theorem mounted (s : Shape) (M R lo : ℕ) (m : Memory w) :
    let a:=s.outputBits*M
    let b:=s.digit*R
    let T:=banks lo a b
    let out:=mount s M R lo m
    (∀i : Cell a,out (lo+i.val)=(chunkCount s M i:Word w)) ∧ static s M R T out ∧ ∀z<lo,out z=m z := by
  have topologySize : 0 < (2 : ℕ) ^ (s.outputBits * M) := Nat.two_pow_pos _
  have windowSize : 0 < (2 : ℕ) ^ (s.digit * R) := Nat.two_pow_pos _
  dsimp only [mount,static]
  refine ⟨?_,⟨?_,?_,?_,?_⟩,?_⟩
  · intro i
    have hi:=i.isLt
    rw [install_low _ _ _ (by dsimp [banks];omega),install_low _ _ _ (by dsimp [banks];omega),
      install_low _ _ _ (by dsimp [banks];omega),install_low _ _ _ (by dsimp [banks];omega),install_hit]
  · intro i
    have hi:=i.isLt
    rw [install_low _ _ _ (by dsimp [banks];omega),install_low _ _ _ (by dsimp [banks];omega),
      install_low _ _ _ (by dsimp [banks];omega),install_hit]
  · intro i
    have hi:=i.isLt
    rw [install_low _ _ _ (by dsimp [banks];omega),install_low _ _ _ (by dsimp [banks];omega),install_hit]
  · intro i
    have hi:=i.isLt
    rw [install_low _ _ _ (by dsimp [banks];omega),install_hit]
  · intro i;apply install_hit
  · intro z hz
    rw [install_low _ _ _ (by dsimp [banks];omega),install_low _ _ _ (by dsimp [banks];omega),
      install_low _ _ _ (by dsimp [banks];omega),install_low _ _ _ (by dsimp [banks];omega),install_low _ _ _ hz]

theorem fee (s : Shape) (H G payload W ratio : ℕ) (nonzero : 0<envelope s) (wide : 2*envelope s≤payload)
    (compare : W≤ratio*payload) :
    let M:=lanes payload (envelope s)
    let n:=H*chunks G M
    let R:=M*s.pairs
    (clock n)*W ≤ ratio*(424*payload+592*(H*payload+4*H*G*envelope s)) ∧
      footprint (s.outputBits*M) (s.digit*R)*W≤ratio*(5*2^(payload/2)*payload) := by
  let M:=lanes payload (envelope s)
  let n:=H*chunks G M
  let b:=s.digit*(M*s.pairs)
  let a:=s.outputBits*M
  have rate : clock n≤424+592*n := by
    unfold clock
    have c:=PackedProfileCursor.ticks_bound n
    omega
  have vol:=volume H G payload (envelope s) nonzero wide
  have kb : bits a b≤payload/2 := key_budget s payload
  have aBound := Nat.pow_le_pow_right (by decide : 0<2) (show a≤payload/2 by dsimp [bits] at kb;omega)
  have bBound := Nat.pow_le_pow_right (by decide : 0<2) (show b≤payload/2 by dsimp [bits] at kb;omega)
  have keyBound := Nat.pow_le_pow_right (by decide : 0<2) kb
  have ROM : footprint a b≤5*2^(payload/2) := by unfold footprint;omega
  have physical : clock n*payload≤424*payload+592*(H*payload+4*H*G*envelope s) := by
    have k:=Nat.mul_le_mul_right payload rate
    change n*payload≤_ at vol
    nlinarith only [k,vol]
  constructor
  · exact (Nat.mul_le_mul_left _ compare).trans (by simpa only [mul_left_comm] using Nat.mul_le_mul_left ratio physical)
  · exact (Nat.mul_le_mul_left _ compare).trans (by simpa only [mul_left_comm] using Nat.mul_le_mul_left ratio (Nat.mul_le_mul_right payload ROM))

theorem issue_cheap (w R n : ℕ) (l : Layout) : CheapCode (issue w R n l) :=
  cheap_seq (cheap_seq (@scan_cheap _ _ _ _) (@PackedProfileCursor.cheap w R l.counts l.cursor.base n)) (@scan_cheap _ _ _ _)

end
end Hierarchy.DescentPacking.PackedMatch.ProfileTable

end OAI
