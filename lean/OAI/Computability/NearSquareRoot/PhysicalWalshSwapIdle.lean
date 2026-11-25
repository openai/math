import OAI.Computability.NearSquareRoot.PhysicalWalshSwapGeometry
import OAI.Computability.NearSquareRoot.FixedCandidateGuard

/-! # Removing an empty interchange from a packed Walsh slot swap

The branch flag is computed from the unary width already in the compact
geometry. When neither wing contains a bit the underlying records retain
their physical order. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode.SlotSwap

open IntegerMultiplication Code Strip Strip.Dims Adic Space

private def value (t : Packet) := (t.geometry.header,(List.range t.geometry.grid.count).map t.bits)

private theorem input_bound (t : Packet) (wide : 0 < t.width) :
    size (value t) ≤ 8*(t.volume+1) := by
  have sizeBits (l : List ℕ) : size (l.map t.bits) = l.length*(2*t.width+2)+1 := by
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons,size_cons,Bits.size_word,t.exactWidth,ih,List.length_cons,Nat.succ_mul]
      omega
  have exponent : t.geometry.pre+t.geometry.wing+t.geometry.gap+t.geometry.wing ≤ t.geometry.grid.count := by
    rw [geometry_count]; exact Nat.lt_two_pow_self.le
  have vol : t.geometry.grid.count ≤ t.volume := Nat.le_mul_of_pos_right _ wide
  simp only [value,size_prod,Geometry.header,size_tally,tally_length,sizeBits,List.length_range]
  unfold Packet.volume at vol ⊢
  ring_nf at vol ⊢
  omega

private theorem idle (t : Packet) (h : t.geometry.wing=0) :
    t.output = send (value t).2 := by
  have act (n : ℕ) : SwapOrdinal.source (2^t.geometry.wing) (room (field 2 t.geometry.gap)) 1 n = n := by
    simp [h,SwapOrdinal.source,SwapOrdinal.rank,Nat.mod_one,Nat.div_add_mod']
  unfold Packet.output value
  simp only [Function.comp_def,act]

/-- One command handles the unguarded empty-wing case and all nonempty
wings whose packed payload absorbs their setup cost. The degree is selected
before the family of inputs. -/
theorem packed_or_idle {ρ : ℝ} (rate : 1/2 < ρ) : ∃ D : ℕ, ∀ {I : Type} (data : I → Packet),
    (∀ i, 0 < (data i).width) →
    (∀ i, (data i).geometry.wing = 0 ∨ (size (data i).geometry.header + 1)^D ≤ (data i).width) →
    BoundedTask (fun i => ⌈((data i).volume : ℝ) * (((data i).geometry.wing+1 : ℕ):ℝ)^ρ⌉₊)
      (Packet.volume ∘ data) (Packet.input ∘ data) (Packet.output ∘ data) := by
  obtain ⟨D,rect⟩ := packed rate
  refine ⟨D,fun {I} data positive fit => ?_⟩
  let V i := (data i).volume
  let time i := ⌈(V i : ℝ) * (((data i).geometry.wing+1 : ℕ):ℝ)^ρ⌉₊
  let tag i := (tally (data i).geometry.wing).isEmpty
  have small (i : I) : size (value (data i)) ≤ 8*(V i+1) := input_bound _ (positive i)
  have vt (i : I) : V i ≤ time i := by
    apply (Nat.cast_le (α:=ℝ)).mp
    exact (le_mul_of_one_le_right (Nat.cast_nonneg _) (Real.one_le_rpow
      (by exact_mod_cast Nat.le_add_left 1 (data i).geometry.wing) (by linarith : 0≤ρ))).trans (Nat.le_ceil _)
  have tag_iff (i : I) : tag i = true ↔ (data i).geometry.wing = 0 := by
    simp only [tag,List.isEmpty_iff_length_eq_zero,tally_length]
  have high := rect (fun i : {i : I // tag i=false} => data i.val) (fun i =>
    (fit i).resolve_left (fun h => Bool.noConfusion (i.property.symm.trans ((tag_iff i).mpr h))))
  have projected := PhysicalWalshGrid.easyWithin (fun i : {i : I // tag i=true} => V i.val) Easy.snd
    (fun i => value (data i.val)) 8 (fun i => small i.val)
  have low : BoundedTask (fun i : {i : I // tag i=true} => time i.val) (fun i => V i.val)
      (fun i => (data i.val).input) (fun i => (data i.val).output) := by
    have body := projected.mono (fun i => vt i.val) (fun _ => le_rfl)
    exact body.conform (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun i => (idle _ ((tag_iff i).mp i.property)).symm)
  have branch := BoundedTask.control (t:=time) (s:=V) (src:=Packet.input ∘ data)
    (dst:=Packet.output ∘ data) tag high low
  let flag := fun z : (Tally × Tally × Tally) × List (List Bool) => (z.1.2.2.isEmpty,z)
  have ez : Easy flag := ((Easy.fst.compose (Easy.snd.compose Easy.snd)).compose (Carry.vacant Unit)).pair Easy.identity
  have prepare := PhysicalWalshGrid.easyWithin V ez (value ∘ data) 8 small
  have both := prepare.compose branch
  apply both.bound 2 10
  · intro i; change V i+time i+1 ≤ 2*(time i+1); have := vt i; omega
  · intro i
    change max (V i) (V i+size (value (data i)))+1 ≤ 10*(V i+1)
    have := small i; omega

end PhysicalWalshNode.SlotSwap

end NearSquareRoot
end Computability
end OAI
