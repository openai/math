import OAI.Computability.BorderVNP.RoutingISABroadcastModel
import OAI.Computability.BorderVNP.RoutingISAAddressFit

/-!
# Reading a named physical input bit

The endpoint and flat index are actual register values. The address kernel
computes a processor and in-processor offset and the final load fetches the
word at that address. The input and all other low registers are unchanged
by this fragment.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open VPVNP.BurstRAM

/-- Every physical read is the actual word in the selected processor input.
The destination is the only low register that changes. -/
theorem readPhysical_run {w : ℕ} (f : BroadcastFrame) (pub : Arg → Word w)
    (macros : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    (partner position dst : Reg) (hj : position.val < 30)
    (image : f.At (readings pub) (readings m)) (fit : f.Fits w (pub 0).val)
    (realTeam : (s partner).val < f.teams) (other : (s partner).val ≠ f.team)
    (inBlock : (s position).val < f.capacity) :
    ∃ es t, Runs pub macros (readPhysical partner position dst) s m es t m ∧
      traceCost es ≤ (readPhysical partner position dst).slots ∧
      ∀ k : Reg, k.val < 30 → t k = if k = dst then m (f.addr (s partner).val (s position).val) else s k := by
  let a : Bank w := Function.update s 30 (s partner)
  let b : Bank w := Function.update a 31 (a position)
  have hpos : a position = s position := Function.update_of_ne (by
    intro he
    rw [he] at hj
    contradiction) ..
  have bx : (b 30).val = (s partner).val := by simp [b,a,Function.update]
  have bj : (b 31).val = (s position).val := by simp [b,hpos]
  obtain ⟨hteam,hcount,_,hlit,hlink,_,_⟩ := image
  have input := f.addr_lt_input fit realTeam other inBlock
  have hs : physicalAddress.safeReadOnly w (readings pub) (readings m) (readings b) := by
    apply physicalAddress_safe
    · change (pub 0).val+4 < _
      have := fit.frame; have := fit.out; omega
    · rw [hcount]; exact zero_lt_two.trans fit.three
    · rw [hlink]; exact fit.width
    · change (b 30).val ≠ _
      rwa [bx,hteam]
    · rw [hcount,hlink,hlit]
      change f.stride < 2^w
      exact lt_of_le_of_lt ((Nat.le_mul_of_pos_left _ fit.procs).trans fit.input) (pub 0).isLt
    · rw [hteam,hcount,hlit,hlink]
      change f.addr (b 30).val (b 31).val < 2^w
      rw [bx,bj]
      exact input.trans_le (fit.input.trans (pub 0).isLt.le)
  obtain ⟨es,t,run,cost,addr,bank,_⟩ := physicalAddress_run pub macros m b hs
  change (t 48).val = physicalBitAddress _ _ _ _ _ _ at addr
  rw [hteam,hcount,hlit,hlink,bx,bj] at addr
  change (t 48).val = f.addr (s partner).val (s position).val at addr
  have x : Runs pub macros (.copy 30 partner) s m [tick w] a m := Runs.localStep m rfl rfl
  have y : Runs pub macros (.copy 31 position) a m [tick w] b m := Runs.localStep m rfl rfl
  let z := Function.update t dst (m (t 48).val)
  refine ⟨_,z,x.seq (y.seq (run.seq (Runs.load pub macros dst 48 t m))),?_,?_⟩
  · change 1 + (1 + traceCost (es ++ [_])) ≤ 1 + (1 + (physicalAddress.slots+1))
    rw [show traceCost (es++[_]) = traceCost es+1 from VPVNP.RAMBuckets.cost_append ..]
    omega
  · intro k hk
    have h30 : k ≠ 30 := by intro he; rw [he] at hk; contradiction
    have h31 : k ≠ 31 := by intro he; rw [he] at hk; contradiction
    by_cases hd : k = dst
    · simp [z,hd,addr]
    · rw [ite_eq_right hd, show z k = t k from Function.update_of_ne hd .., bank k hk]
      simp [b,a,h30,h31]

end RoutingISA

end BorderVNP
end Computability
end OAI
