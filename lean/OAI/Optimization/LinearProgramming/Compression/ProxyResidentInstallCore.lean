import OAI.Optimization.LinearProgramming.Compression.ProxyResidentControls
import OAI.Optimization.LinearProgramming.Compression.ProxyResidentLoop

/-! Exact output cells of the same native cache scatter over any ordered field. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace SignWire

open RAM ResidentInstall

private theorem installClock (cap R : ℕ) :
    12*cap+16+((cap-15)*(12*R+27)+1+4) ≤ 100*(cap+R+1)^2 := by
  let X := cap+R+1
  have positive : 1 ≤ X := by dsimp [X]; omega
  have c : cap ≤ X := by dsimp [X]; omega
  have mul := Nat.mul_le_mul (show cap-15 ≤ X by omega) (show 12*R+27 ≤ 39*X by dsimp [X]; omega)
  have prod : X*(39*X) = 39*X^2 := by ring
  rw [prod] at mul
  have lin : X ≤ X^2 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < X) (show 1 ≤ 2 by decide)
  change 12*cap+16+((cap-15)*(12*R+27)+1+4) ≤ 100*X^2
  omega

theorem installResident_frames {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K→Prop) (caller raw : Memory K) (R cap : ℕ) (bound : ∀ j,caller.index j≤R)
    (hcap : 105≤cap) (inputCap : raw.index 0=cap) (safe : raw.AllData P) (zero : P 0)
    (data : ∀ j,16≤j → j≤cap → raw.data j=caller.data j)
    (address : ∀ j,60≤j → j≤cap → raw.index j=caller.index j)
    (tail : ∀ i,2*cap+1 < i → raw.index (2*i)%2=0) :
    ∃ t k,k≤100*(cap+R+1)^2 ∧ Block.Eval (Memory.AllData P) installResident raw k t ∧
      (∀ j,16≤j → j≤cap → PhysicalPair j caller t) ∧
      (∀ i,2*cap+1 < i → t.index (2*i)%2=0) ∧ (∀ i<4,t.index (57+2*i)=caller.index (102+i)) ∧
      ∀ j,16≤j → j%2=1 → j≠57 → j≠59 → j≠61 → j≠63 → t.index j=raw.index j := by
  obtain ⟨a,ea,start⟩ := startBlock_eval P raw cap inputCap safe zero
  have cu : Cursor cap a :=
    ⟨start.source,start.outer,start.inner,start.zeroIndex,start.stop,start.cutoff,start.zeroScalar⟩
  obtain ⟨b,l,hl,el,expanded⟩ := scatterResidentLoop_eval P a caller cap R (by omega) ea.safe_end cu
    (fun j lo hi => (start.scalar j (by omega)).trans (data j lo hi))
    (fun j lo hi => (start.highIndex j (by omega)).trans (address j lo hi)) bound
    (fun i hi => by rw [start.highIndex _ (by omega)]; exact tail i hi)
  obtain ⟨t,ef,finish⟩ := finishBlock_eval P b el.safe_end
  have stable (i : ℕ) (hi : 64 ≤ i) : t.index i = b.index i :=
    finish.frame i (by simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]; omega)
  have pair (j : ℕ) (lo : 16≤j) (hi : j≤cap) : PhysicalPair j caller t := by
    have old := expanded.pairs j lo hi
    exact ⟨(congrFun finish.data _).trans old.innerData,(stable _ (by omega)).trans old.innerIndex,
      (congrFun finish.data _).trans old.outerData,(stable _ (by omega)).trans old.outerIndex⟩
  have metadata (i : ℕ) (hi : i<4) : t.index (57+2*i) = caller.index (102+i) :=
    (finish.metadata i hi).trans ((expanded.metadata i hi).trans
      ((start.metadata i hi).trans (address (102+i) (by omega) (by omega))))
  have time := Nat.add_le_add_left (Nat.add_le_add_right hl 4) (12*cap+16)
  refine ⟨t,_,time.trans (installClock cap R),ea.seq (el.seq ef),pair,?_,metadata,?_⟩
  · intro i hi;rw [stable _ (by omega)];exact expanded.exterior i hi
  · intro j hj odd h57 h59 h61 h63
    exact (finish.frame j (by simp [h57,h59,h61,h63])).trans ((expanded.odd j hj odd).trans (start.highIndex j hj))

end SignWire
end Compression
end LinearProgramming
end Optimization
end OAI
