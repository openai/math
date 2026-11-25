import OAI.Computability.BorderVNP.CubeScatterPaddingBanksRow
import OAI.Computability.BorderVNP.CubeISADeclaredRowTally

/-! # Preserving scattered words through the vertex directory and row tally -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Padding.Banks

open Physical Physical.Owned HostAddress RoutingISA VPVNP.BurstRAM DiagonalResidueRAM Tally

variable {n d blocks b h K s w : ℕ} (A : Data n d blocks b h K s)

/-- Actual words needed by the team's scattered singleton and packet banks. -/
def Data.BankWord (a : ℕ) : Prop :=
  (∃ q : SingleSlot n d blocks (h*b), a = A.singleAddr q) ∨
    ∃ p : Packet n d blocks, ∃ j : Fin (bankWidth n b h K s), a = A.packetAddr p+j.val

/-- A subsequent native memory update with the same reserved words preserves every local view. -/
theorem Data.holds_of_words {m m' : Memory w} (eq : ∀ a, A.BankWord a → m' a = m a)
    (x : View n d blocks (h*b)) (old : A.Holds m x) : A.Holds m' x := by
  cases x with
  | single q side => exact (eq _ (Or.inl ⟨q,rfl⟩)).trans old
  | vertex p v => exact A.vertex_congr p v (fun j => eq _ (Or.inr ⟨p,j,rfl⟩)) old

/-- The actual append-only vertex directory preserves every bank word below its start,
and the subsequent native row tally preserves every bank word outside its scratch and totals. -/
theorem Data.post_row_words {scatter final : Memory w} (pair : Symbols d) (high : Bool) (out base scratch : ℕ)
    (below : ∀ a, A.BankWord a → a < out)
    (away : ∀ a, A.BankWord a → PacketTally.Outside n h base scratch a)
    (tally : ∀ a, PacketTally.Outside n h base scratch a →
      readings final a = (OwnedVertex.rowImage (blocks := blocks) A.axis pair high A.packetBase
        (bankWidth n b h K s) (selectorWidth n K h) out (readings scatter) (packetTrials n d blocks)).2 a) :
    ∀ a, A.BankWord a → final a = scatter a := by
  intro a word
  apply Fin.ext
  exact (tally a (away a word)).trans
    ((OwnedVertex.rowImage_frame (blocks := blocks) A.axis pair high A.packetBase (bankWidth n b h K s)
      (selectorWidth n K h) out (readings scatter) (packetTrials n d blocks)).2 a (below a word))

/-- One physical assignment with the native reservations of its current team. -/
def Data.atTeam {Team : Type*} (pack singles : Team → ℕ) (t : Team) : Data n d blocks b h K s :=
  {A with packetBase := pack t, singleBase := singles t}

/-- Extract the two kinds of actual endpoint words from completed owned packet and
singleton views, in the address convention of the padded host. -/
theorem Data.endBanks_of_views {Team : Type*} (hw : 0 < w) (group : Fin d → Team)
    (pack singles : Team → ℕ) (mem : Team → Memory w)
    (views : ∀ t (x : View n d blocks (h*b)), group (x.row A.axis).1 = t →
      (A.atTeam pack singles t).Holds (mem t) x) :
    EndBanks A.axis group pack singles (fun t => readings (mem t))
      (fun q => A.value q.1.val q.2) A.demand K s := by
  constructor
  · intro q side t
    have own : group (((View.single q side).row A.axis).1) = t := by
      cases side <;> rfl
    have ok := views t (.single q side) own
    change mem t ((A.atTeam pack singles t).singleAddr q) = wordBit w (A.value q.1.val q.2) at ok
    exact (congrArg Fin.val ok).trans (Nat.mod_eq_of_lt
      ((A.value q.1.val q.2).toNat_le.trans_lt (one_lt_pow₀ (by decide) hw.ne')))
  · intro p v side j t
    let vertex := if side then stop v else start v
    have own := congrArg group (View.vertex_row_owner (b := b) (h := h) A.axis p vertex)
    have read := views t (.vertex p vertex) own
    exact read.demand (v,side) rfl j

end Cube.Padding.Banks

end BorderVNP
end Computability
end OAI
