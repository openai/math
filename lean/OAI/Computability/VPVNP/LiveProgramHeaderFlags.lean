import OAI.Computability.VPVNP.LiveProgramHandoffs
import OAI.Computability.VPVNP.LiveHeaderComplete

/-! # Reading the physical header flags used by the outer routers -/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.HeaderFlags
open BurstRAM LiveHeaderProgram LiveHeaderSchedule LiveHeaderWidths ChainAssignments
open scoped Fin.CommRing

variable (c : Constants) (g : Geometry) (lit : LiteralPrefix)

/-- The evaluated header dimensions used to locate the physical router flags in this group. -/
abbrev size := c.lengths.eval g
/-- Header workspace base for locating the mode, first-tail and last-group flags after the
processor array and outer tag. -/
abbrev base := 2^g.d+1

/-- The loaded router flag word names the same checked physical metadata cell
as the standalone header parser. The address arithmetic fits before resizing. -/
theorem flag_address (r : Router) (fit : LiveHeaderSchedule.limit (size c g) (base g) < 2^g.w) :
    ((r.data g lit) 0).val = match r with
    | .mode => tagAddr (base g)
    | .firstTail => firstTailAddr (base g)
    | .last => flagAddr (base g) .last := by
  rw [LiveHeaderSchedule.limit_eq] at fit
  cases r with
  | mode => exact Nat.mod_eq_of_lt (by change base g+11 < 2^g.w; omega)
  | firstTail => exact Nat.mod_eq_of_lt (by change base g+10 < 2^g.w; omega)
  | last => exact Nat.mod_eq_of_lt (by change base g+9 < 2^g.w; omega)

variable {hw : 4 ≤ g.w} {advice : CutSchedule.Bits (size c g).advice}
variable {cuts : AllCuts (size c g).h (size c g).delta}
variable {site : Fin (2^((size c g).h+1))} {tag : LiveHeader.Mode.Tag} {m : Memory g.w}

/-- The native mode router reads the exact zero/unit, one/pair, two/tail code. -/
theorem mode (fit : LiveHeaderSchedule.limit (size c g) (base g) < 2^g.w)
    (out : Output (size c g) (base g) g.d hw advice cuts site tag m) :
    m ((Router.mode.data g lit) 0).val = Fin.ofNat (2^g.w) tag.code.val := by
  rw [flag_address c g lit .mode fit]
  exact out.scalars .mode

/-- The middle cut supplies exponents exactly to the group immediately after it. -/
theorem firstTail (fit : LiveHeaderSchedule.limit (size c g) (base g) < 2^g.w)
    (out : Output (size c g) (base g) g.d hw advice cuts site tag m) :
    m ((Router.firstTail.data g lit) 0).val =
      (if site.val+1 = 2^(size c g).h+1 then 1 else 0) := by
  rw [flag_address c g lit .firstTail fit]
  simpa [Metadata.Correct,Metadata.Field.address,PrimedInputRAM.encodeBit] using out.scalars .firstTail

/-- The last flag distinguishes a prescribed accepting endpoint from an
outgoing configuration stored on a physical cut. -/
theorem last (fit : LiveHeaderSchedule.limit (size c g) (base g) < 2^g.w)
    (out : Output (size c g) (base g) g.d hw advice cuts site tag m) :
    m ((Router.last.data g lit) 0).val =
      (if site.val+1 = 2^((size c g).h+1) then 1 else 0) := by
  rw [flag_address c g lit .last fit]
  by_cases h : site.val+1 = 2^((size c g).h+1) <;>
    simpa [Metadata.Correct,Metadata.Field.address,Flag.holds,PrimedInputRAM.encodeBit,h] using out.scalars (.flag .last)

end LiveProgram.HeaderFlags

end VPVNP
end Computability
end OAI
