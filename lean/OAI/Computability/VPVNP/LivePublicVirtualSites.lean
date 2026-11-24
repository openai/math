import OAI.Computability.VPVNP.LivePublicExpr
import OAI.Computability.VPVNP.RAMVirtualParameterBounds
import OAI.Computability.VPVNP.CursorBounds

/-!
# Computing the virtual site count from the live address width

The least admissible virtual address width is the ceiling logarithm of the
probe budget minus the virtual bucket exponent. Adding the live address
width after taking the logarithm keeps the largest operand of the logarithm
at `n * clog₂ n`.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram

open BurstRAM

/-- A fixed expression for the number of virtual sites in Sections 11 and 14. -/
def virtualSites : PublicExpr :=
  let c := PublicExpr.clog2 .n
  .pow2 (.sub (.add .d (.clog2 (.mul .n c))) (.divConst (.add c (.lit 3)) 4))

theorem virtualSites_eval (g : Geometry) (hn : 2 ≤ g.n) :
    virtualSites.eval g = 2^virtualSiteExponent g.d g.n := by
  rw [virtualSiteExponent_eq_add_sub _ _ hn]
  rfl

/-- The input, product, two logarithmic counters and both division operands
fit the same word as the resulting site count. -/
theorem virtualSites_fits {B n H : ℕ} (hB : 1 ≤ B) (hn : 2 ≤ n)
    (hcount : 2^virtualSiteExponent (addressWidth B n) n < 2^CursorBounds.wordBits B n) :
    virtualSites.Fits ⟨n,addressWidth B n,H,CursorBounds.wordBits B n⟩
      (2^CursorBounds.wordBits B n) := by
  let r := addressWidth B n
  let w := CursorBounds.wordBits B n
  let c := Nat.clog 2 n
  let g : Geometry := ⟨n,r,H,w⟩
  let Fit := PublicExpr.Fits g (2^w)
  obtain ⟨hprod,hsum,hnum⟩ := virtualParameterOperands_lt hB n
  change n * c + 1 < 2^w at hprod
  change r + Nat.clog 2 (n*c) < 2^w at hsum
  change c + 3 < 2^w at hnum
  have hc : 0 < c := Nat.clog_pos Nat.one_lt_two hn
  have hsub := Nat.le_mul_of_pos_right n hc
  have fN : Fit .n := ⟨by change n < _; omega,trivial⟩
  have fD : Fit .d := ⟨by change r < _; omega,trivial⟩
  have fC : Fit (.clog2 .n) := ⟨by change c < _; omega,fN⟩
  have fNC : Fit (.mul .n (.clog2 .n)) := ⟨by change n*c < _; omega,fN,fC⟩
  have flog : Fit (.clog2 (.mul .n (.clog2 .n))) := ⟨by change Nat.clog 2 (n*c) < _; omega,fNC⟩
  have fsum : Fit (.add .d (.clog2 (.mul .n (.clog2 .n)))) := ⟨hsum,fD,flog⟩
  have fnum : Fit (.add (.clog2 .n) (.lit 3)) := ⟨hnum,fC,⟨by change 3 < _; omega,trivial⟩⟩
  have fdiv : Fit (.divConst (.add (.clog2 .n) (.lit 3)) 4) :=
    ⟨by change (c+3)/4 < _; omega,fnum,by omega⟩
  refine ⟨?_, ?_, fsum, fdiv⟩
  · change virtualSites.eval g < _
    rw [virtualSites_eval g hn]
    exact hcount
  · change r + Nat.clog 2 (n*c) - (c+3)/4 < _
    exact (Nat.sub_le _ _).trans_lt hsum

end LiveProgram

end VPVNP
end Computability
end OAI
