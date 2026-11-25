import OAI.Computability.BorderVNP.FiniteEvaluatorCubeBanks
import OAI.Computability.BorderVNP.FiniteDiagonalOwnedCellProduct
import OAI.Computability.BorderVNP.CubeScatterPaddingBanksFrame
import OAI.Computability.BorderVNP.CubeScatterPaddingTail

/-! # The native padding guard and the actual finite-field term

The completed group scans expose both physical end words of every unused
slot. The native padding caches use the same occupied intervals as the
selected sparse geometry. Their joint validity is therefore the exact pin
test in the field contraction term.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal.FieldRawLayout

open Crossing BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Tally Padding.Banks
open NativeIntervals RoutingISA VPVNP.BurstRAM
open scoped Classical

variable {D w : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {N : Network D P bits}
variable {F : Type*} [Field F] {T : N.Tables F} {L : FieldPacketPlan N F} {S : FieldSiteDirectory N T}
variable (V : FieldRawLayout L S) (R : ℕ) (raw : V.Raw R)
variable {interval : NativeIntervals.Layout} {before dir : ℕ → ℕ}
variable {row : Fin L.count ↪o Fin interval.count} {cells : L.Cell ↪ ℕ}
variable {hz : L.alphabet^(L.dimension+1)=interval.alphabet}
local notation "axis" => chosen L.bitWidth L.supply (Sigma.fst (Prod.fst raw))
local notation "owner" => V.owners R (Sigma.fst (Prod.fst raw))

/-- On the actual routed assignment, all native padding passes return exactly
when both ends of every unused packed slot have the required zero bit. -/
theorem padding_valid_iff
    (physical : PhysicalRows N L.cell interval before L.order row cells L.label
      (productCode L.dimension L.alphabet interval.alphabet hz))
    (widths : interval.Image before interval.count dir) (pub : Fin (R+1) → Arg → Word w)
    (out : Fin (R+1) → Memory w) (hw : 0<w)
    (views : ∀ t (x : View L.dimension L.alphabet L.blocks (L.copies*L.bitWidth)),
      owner (x.row axis).1=t →
        let l := Padding.Layout.fromFrame (pub t 0).val (readings (out t))
        (V.bankData R raw l.packets l.singles).Holds (out t) x)
    (headers : ∀ t, Padding.TailHeader axis owner Fin.valEmbedding t
      (Padding.Layout.fromFrame (pub t 0).val (readings (out t))) (readings (out t))
      (fun j => dir (interval.widths+j)) L.blocks L.bitWidth L.copies L.alternatives L.supply) :
    (∀ t, (Padding.Layout.fromFrame (pub t 0).val (readings (out t))).Valid (readings (out t))) ↔
      FieldSiteDirectory.pinsPass L (V.owners R) raw.1 := by
  let l (t : Fin (R+1)) := Padding.Layout.fromFrame (pub t 0).val (readings (out t))
  let A := V.bankData R raw 0 0
  have endWords := A.endBanks_of_views hw owner (fun t => (l t).packets) (fun t => (l t).singles) out views
  have result := Padding.valid_iff_pins physical widths L.capacity endWords headers
  let z := FieldSiteDirectory.cubeInputs L (V.owners R) raw.1
  have singles : (fun q => A.value q.1.val q.2)=z.1 := funext (V.bank_single R raw 0 0)
  rw [singles] at result
  exact result

end FiniteDiagonal.FieldRawLayout

end BorderVNP
end Computability
end OAI
