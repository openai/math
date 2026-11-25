import OAI.Hierarchy.TaggedWireTerminalPriorBit
import OAI.Hierarchy.TaggedWireFinish

namespace OAI
/-! # Previous barrel bit of the actual reported terminal matrix -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProbeStage.CoreBoard.Report
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open AdaptiveProbe ReportSockets HistoryRoles WireTelescope CalendarTape ProtocolRAM.Calendar
open scoped Classical

private theorem rebase_twice {n : ℕ} {A B C : Widths n} (one : A=B) (two : B=C) (s : Fin n) (v : State C s) :
    cast (congrArg (fun V=>State V s) one.symm) (cast (congrArg (fun V=>State V s) two.symm) v)=
      cast (congrArg (fun V=>State V s) (one.trans two).symm) v := by subst B;subst C;rfl

variable {X : Type} {h W k w R attempts M den : ℕ} (p : Equiv.Perm (Tagged.Row h)) (depth : ℕ)
    (marked : Marks h W k attempts) (unique : Exclusive marked)
local notation "N" => siteLast h (2^W) k+1
variable (slot : Event→Slot X) (wire : X→Widths (siteLast h (2^W) k+1)) (es : List Event) (x : X) (j : Path slot es x)
variable (Z : Report p (2^W) k w R M den (wire (terminal slot es x j)))
local notation "π" => p.symm
local notation "S" => Z.sampler
local notation "L" => Z.mount.matrixLayout (siteNumber h (2^W) k).injective (publicChord h (2^W) k)
local notation "counts" => SettledMatrix.Layout.bits Z.fixed Z.stock Z.reserved Z.used
variable (ident : {i // 0<Z.fixed i} ↪ Catalogue Z.sampler p.symm depth marked)
local notation "role" => Terminal.ports S π depth marked unique Z.fixed Z.stock Z.reserved Z.used ident
variable (cap : Public Z.sampler h W k attempts→ℕ)
    (room : ∀q : NamedAperture.LiveEnd (SettledMatrix.Layout.bits Z.fixed Z.stock Z.reserved Z.used),
      SettledMatrix.Layout.bits Z.fixed Z.stock Z.reserved Z.used q.val.1 ≤
        cap (Terminal.ports Z.sampler p.symm depth marked unique Z.fixed Z.stock Z.reserved Z.used ident q))
variable (cells : ∀y,(Σs,SiteBit (wire y) s) ↪ (Σu,Fin (cap u)))

theorem previousBit
    (packing : cells (terminal slot es x j) = (NamedAperture.transport Z.ledger.symm).toEmbedding.trans
      (Terminal.place S π depth marked unique Z.mount (publicChord h (2^W) k) Z.fixed Z.stock Z.reserved Z.used ident Z.receipt cap room))
    (z : SiteChoices slot wire es x j) {s : Fin N} (q : (bitGraph (rowGraph (L).family) counts).Port s) :
    let key : NamedAperture.LiveEnd counts:=⟨(q.1.1.1,q.1.2),Nat.zero_lt_of_lt q.1.1.2.isLt⟩
    let address:=bodyIndex es (Fin.last es.length) (⟨role key,q.1.1.2.castLE (room key)⟩ : Σu,Fin (cap u))
    placedBits slot wire es x j (timelineFin slot wire cells es x j) z address=
      rowBits (L).family counts (Z.initialState (lastState slot wire s es x j (z s))) q := by
  intro key location
  have prior:=Terminal.prior_bit S π depth marked unique Z.mount (publicChord h (2^W) k)
    Z.fixed Z.stock Z.reserved Z.used ident Z.receipt cap room slot wire cells es x j z Z.ledger.symm packing q
  exact prior.trans (congrArg (fun a=>rowBits (L).family counts a q)
    (rebase_twice (Z.receipt.old_width (siteNumber h (2^W) k).injective (publicChord h (2^W) k)) Z.ledger s _))

end Hierarchy.ProbeStage.CoreBoard.Report
end

end OAI
