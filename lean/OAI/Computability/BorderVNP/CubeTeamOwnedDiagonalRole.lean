import OAI.Computability.BorderVNP.CubeScatterPaddingBanksSide
import OAI.Computability.BorderVNP.CubeTeamOwnedSelectorRows
import OAI.Computability.BorderVNP.CubeISALocalRowChecked
import OAI.Computability.BorderVNP.CubeTeamOwnedGroups

/-! # The complete native diagonal role on an authentic declaration

A repeated-symbol row draws its singleton bits from this team's private
tape. Its subsequent unsigned verifier reconstructs every coordinate of the
declared row. The protected inputs, scattered banks and all outer cursors
survive the two stages.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.TeamRows

open Crossing Physical Physical.Owned Scatter Padding.Banks Tally
open RoutingISA RoutingISA.Owned RoutingISA.OwnedStages VPVNP.BurstRAM
open private packet_end_le from OAI.Computability.BorderVNP.CubeScatterPaddingBanksSide

variable {w n d blocks b h K s : ℕ} (A : Data n d blocks b h K s)

/-- The actual packets are below the tally descriptor and every real singleton
word is above it when the singleton bank starts after the descriptor and digits. -/
theorem checker_bank_protected (power header actual claimed frame : ℕ)
    (space : LocalRow.Space (⟨d,blocks,h*b,power,header,A.packetBase⟩ : OwnedRowSetup.Layout)
      w n b h K s frame actual claimed)
    (afterScratch : LocalRow.head (⟨d,blocks,h*b,power,header,A.packetBase⟩ : OwnedRowSetup.Layout)
      n b h K s+8+h ≤ A.singleBase) (x : ℕ) (hx : A.BankWord x) :
    LocalRow.Protected n h actual (LocalRow.head
      (⟨d,blocks,h*b,power,header,A.packetBase⟩ : OwnedRowSetup.Layout) n b h K s) x := by
  let l : OwnedRowSetup.Layout := ⟨d,blocks,h*b,power,header,A.packetBase⟩
  have lower : actual+(n+1) ≤ A.packetBase :=
    space.beforeClaim.trans ((Nat.le_add_right _ _).trans space.beforeBank)
  have bank : A.packetBase ≤ LocalRow.head l n b h K s := LocalRow.bank_le_head l n b h K s
  rcases hx with ⟨q,rfl⟩|⟨p,j,rfl⟩
  · have start : A.singleBase ≤ A.singleAddr q := by unfold Data.singleAddr; omega
    exact ⟨.inr (lower.trans (bank.trans ((Nat.le_add_right ..).trans
      ((Nat.le_add_right ..).trans (afterScratch.trans start))))),.inr (afterScratch.trans start)⟩
  · have start : A.packetBase ≤ A.packetAddr p := Nat.le_add_right ..
    have stop : A.packetAddr p+j.val < LocalRow.head l n b h K s := by
      rw [LocalRow.head_eq]
      exact (Nat.add_lt_add_left j.isLt _).trans_le (packet_end_le A p)
    exact ⟨.inr (lower.trans (start.trans (Nat.le_add_right ..))),.inl stop⟩

/-- The two native diagonal stages consume the exact local singleton tape,
write the authentic row into H[0], restore the caller's vertex and iteration
cursors, and agree with the true scatter on every physical bank address. -/
theorem diagonalRole_run (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (src : Set ℕ)
    (r : Bank w) (m : Memory w) (g : Fin d) (sel cross power header actual claimed : ℕ)
    (rows : Sym2 (Fin d) → Fin (n+1) → ℕ) :
    let l : OwnedRowSetup.Layout := ⟨d,blocks,h*b,power,header,A.packetBase⟩
    let D := A.single g g sel cross
    let desc := LocalRow.head l n b h K s
    let row := Sym2.mk g g
    let vals := subtotals itemRow (crossCount b s A.select) A.axis row
    let scattered := A.rowMem g g sel cross m
    Entry A.axis g g r → r 36 = DiagonalResidueRAM.word w sel → r 37 = DiagonalResidueRAM.word w cross →
    l.Loaded n (readings pub) (readings m) → OwnedStages.Protected l n (pub 0).val src →
    (pub 0).val+56 ∈ src → (pub 0).val+88 ∈ src →
    readings m ((pub 0).val+56) = d^(n+1) → readings m ((pub 0).val+88) = A.singleBase →
    SingleRoom w n d (blocks*(h*b)) (pub 0).val A.singleBase →
    (∀ (t : Fin (singlePairTrials n d)), D.selected t → ∀ j < blocks*(h*b),
      D.address t+j ∉ src ∧ D.address t+j < 2^w) →
    CheckImage l src n actual claimed rows m → passesLengths b s A.select (A.axis,rows) →
    LocalRow.Space l w n b h K s (readings pub 0) actual claimed →
    d^(n+1) ≤ 2^w → declarationCap n d blocks b h s < 2^w →
    desc+8+h ≤ A.singleBase → (∀ x ∈ src, LocalRow.Protected n h actual desc x) →
    TraceRun pub mac (diagonalRole n b h K s) r m (rowChoices D.selected D.localBits)
      (singleStageCost D + LocalRow.diagonalTicks n b h K s blocks A.axis g)
      (fun t mt => LocalRow.Return h actual desc (readings r) (readings scattered) vals (.ofWords t mt) ∧
        (∀ j : Fin (n+1), readings mt (actual+j.val) = rows row j) ∧
        (∀ x, A.BankWord x → mt x = scattered x) ∧ ∀ x ∈ src, mt x = m x) := by
  intro l D desc row vals scattered entry rs rc loaded protect fz fb zAt bankAt room dest image pass space labelFit capFit
    bankAfter sourceSafe
  have empty : D.crossingWords = [] := by simp only [D,Data.single,SingleRowData.crossingWords,ite_true]
  have prepared := D.preparedRow_of_streams src m (empty ▸ Resident.nil src m D.crossing) dest
  have eqMem : scattered = (D.before m (singlePairTrials n d)).2 := by
    simp only [scattered,Data.rowMem,dite_eq_right (lt_irrefl g),D]
  have keepSrc : ∀ x ∈ src, scattered x = m x := eqMem ▸ D.before_source m prepared _
  have im := image.transfer keepSrc
  have frame := protect.loaded loaded keepSrc
  have truth (j : Fin (n+1)) : vals j = rows row j := (pass.1 row j).symm
  have first := A.diagonalSide_run_words pub mac src r m g sel cross power header entry rs rc loaded space.frameFit
    prepared fz fb zAt bankAt room
  have next (u : Bank w) (mu : Memory w) (held : Keeps r u) (muEq : mu = scattered) :
      TraceRun pub mac (LocalRow.diagonalChecked n b h K s) u mu [] (LocalRow.diagonalTicks n b h K s blocks A.axis g)
        (fun t mt => LocalRow.Return h actual desc (readings r) (readings scattered) vals (.ofWords t mt) ∧
          (∀ j : Fin (n+1), readings mt (actual+j.val) = rows row j) ∧
          (∀ x, A.BankWord x → mt x = scattered x) ∧ ∀ x ∈ src, mt x = m x) := by
    subst mu
    have en := entry.keep held
    have ck := LocalRow.diagonalChecked_run pub mac u scattered l A.axis g b h K s actual claimed A.select rows
      frame im.actualAt im.claimedAt im.table space rfl labelFit capFit en.zero en.one en.axis en.left en.right
    apply (traceRun_unsigned (ck.complete truth) (LocalRow.diagonalChecked_unsigned n b h K s)).mono le_rfl
    intro t mt ret
    refine ⟨⟨ret.vertex.trans (congrArg Fin.val (held 7 (by decide))),
      ret.cursor.trans (congrArg Fin.val (held 22 (by decide))),
      ret.bound.trans (congrArg Fin.val (held 23 (by decide))),ret.row,ret.outside⟩,
      fun j => (ret.row j).trans (truth j),fun x hx => Fin.ext (ret.outside x ?_),fun x hx => ?_⟩
    · exact checker_bank_protected A power header actual claimed _ space bankAfter x hx
    · exact (Fin.ext (ret.outside x (sourceSafe x hx))).trans (keepSrc x hx)
  simpa only [diagonalRole,List.append_nil] using first.seq (fun u mu ret => next u mu ret.1 ret.2.2.2)

end Cube.TeamRows

end BorderVNP
end Computability
end OAI
