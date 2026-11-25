import OAI.Computability.BorderVNP.CubeScatterPaddingBanksFold
import OAI.Computability.BorderVNP.CubeISAOwnedStrictSide

/-! # Actual strict-side return words below the vertex-directory append cursor -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Padding.Banks

open Physical Physical.Owned Scatter RoutingISA RoutingISA.OwnedStages
open VPVNP.BurstRAM Tally
open private singleAddr_range from OAI.Computability.BorderVNP.CubeScatterPaddingBanks

variable {n d blocks b h K s w : ℕ} (A : Data n d blocks b h K s)

/-- Primary and secondary addresses supplied to the actual strict-side return. -/
def Data.side (power header out : ℕ) : SideData n d blocks b h :=
  ⟨power,header,A.singleBase,out,A.value⟩

private theorem packet_end_le (p : Packet n d blocks) : A.packetAddr p + bankWidth n b h K s ≤
    A.packetBase+(d*d)^(n+1)*2*blocks*bankWidth n b h K s := by
  let pair := p.1.1 A.axis
  let t := (packetRowEquiv A.axis pair).symm ⟨p,rfl⟩
  have he : (packetRowEquiv A.axis pair t).val = p := congrArg Subtype.val (Equiv.apply_symm_apply ..)
  have idx := trialPacketIndex_lt A.axis pair t.val
  rw [trialPacketIndex_eq A.axis pair t,he] at idx
  have cap := Nat.mul_le_mul_right (bankWidth n b h K s) idx
  rw [Nat.succ_mul] at cap
  change A.packetBase+packetIndex p*bankWidth n b h K s+bankWidth n b h K s ≤ _
  omega

/-- A disjoint whole-bank allocation gives the separation used by all folded row proofs. -/
theorem Data.separate_of_allocated (cap : A.packetBase+(d*d)^(n+1)*2*blocks*bankWidth n b h K s ≤ A.singleBase) :
    A.Separate := fun p => Or.inl ((packet_end_le A p).trans cap)

/-- All physical input words lie below the genuine append cursor. -/
theorem Data.bankWord_lt {out : ℕ}
    (pack : A.packetBase+(d*d)^(n+1)*2*blocks*bankWidth n b h K s ≤ A.singleBase)
    (singles : A.singleBase+d^(n+1)*d^(n+1)*(blocks*(h*b)) ≤ out) (a : ℕ) (word : A.BankWord a) : a < out := by
  rcases word with ⟨q,rfl⟩ | ⟨p,j,rfl⟩
  · exact (singleAddr_range A q).2.trans_le singles
  · exact (Nat.add_lt_add_left j.isLt _).trans_le ((packet_end_le A p).trans
      (pack.trans ((Nat.le_add_right _ _).trans singles)))

/-- The memory of an actual native strict-side return agrees on every reserved bank
word with its genuine packet and two consecutive singleton scatter updates. -/
theorem Data.strictSide_words {pub : Arg → Word w} {src : Set ℕ} {r t : Bank w} {m mt : Memory w}
    (pair : Symbols d) (high : Bool) (sel cross power header out : ℕ)
    (ready : SideReady (A.packet pair high sel cross) (A.side power header out) pub src r m)
    (result : SideResult (A.packet pair high sel cross) (A.side power header out) src r m t mt) :
    ∀ a, A.BankWord a → mt a = A.strictMem pair high sel cross m a := by
  intro a ha
  have below := A.bankWord_lt ready.packetsBeforeSingletons ready.singletonsBeforeDirectory a ha
  have keep := (OwnedVertex.rowImage_frame (blocks := blocks) A.axis pair high A.packetBase
    (bankWidth n b h K s) (selectorWidth n K h) out (readings (A.strictMem pair high sel cross m))
    (packetTrials n d blocks)).2 a below
  exact Fin.ext ((congrFun result.image a).trans keep)

/-- The real positive strict-row trace gives the reserved words, including when a
single team will execute the opposing side later in the ordered scan. -/
theorem Data.strictSide_run_words (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (src : Set ℕ)
    (r : Bank w) (m : Memory w) (pair : Symbols d) (high : Bool) (sel cross power header out : ℕ)
    (ready : SideReady (A.packet pair high sel cross) (A.side power header out) pub src r m) :
    let D := A.packet pair high sel cross
    let S := A.side power header out
    Owned.TraceRun pub mac (strictSide n b h K s) r m (Owned.rowChoices packetTrialValid D.choices) (sideCost D S)
      (fun t mt => SideResult D S src r m t mt ∧ ∀ a, A.BankWord a → mt a = A.strictMem pair high sel cross m a) := by
  intro D S
  apply (strictSide_run D S pub mac src r m ready).mono le_rfl
  intro t mt result
  exact ⟨result,A.strictSide_words pair high sel cross power header out ready result⟩

/-- The diagonal program's returned memory is exactly the one-family scatter image,
with the original selector cursor and the true updated crossing cursor. -/
theorem Data.diagonalSide_run_words (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (src : Set ℕ) (r : Bank w) (m : Memory w) (g : Fin d) (sel cross power header : ℕ)
    (entry : Entry A.axis g g r) (rs : r 36 = DiagonalResidueRAM.word w sel)
    (rc : r 37 = DiagonalResidueRAM.word w cross)
    (loaded : (⟨d,blocks,h*b,power,header,A.packetBase⟩ : OwnedRowSetup.Layout).Loaded n (readings pub) (readings m))
    (fit : (⟨d,blocks,h*b,power,header,A.packetBase⟩ : OwnedRowSetup.Layout).Fits w n (readings pub 0))
    (prepared : (A.single g g sel cross).PreparedRow src m)
    (frameZ : (pub 0).val+56 ∈ src) (frameBank : (pub 0).val+88 ∈ src)
    (zAt : readings m ((pub 0).val+56) = d^(n+1)) (base : readings m ((pub 0).val+88) = A.singleBase)
    (room : SingleRoom w n d (blocks*(h*b)) (pub 0).val A.singleBase) :
    let D := A.single g g sel cross
    Owned.TraceRun pub mac (diagonalSide n) r m (Owned.rowChoices D.selected D.localBits) (singleStageCost D)
      (fun t mt => Keeps r t ∧ t 36 = DiagonalResidueRAM.word w sel ∧
        t 37 = DiagonalResidueRAM.word w (D.before m (singlePairTrials n d)).1 ∧ mt = A.rowMem g g sel cross m) := by
  intro D
  let layout : OwnedRowSetup.Layout := ⟨d,blocks,h*b,power,header,A.packetBase⟩
  have run := singleStage_run pub mac layout D src r m entry rs rc loaded fit prepared frameZ frameBank
    zAt base room.frameFit room.keys room.allocation
  simpa only [Data.rowMem,dite_eq_right (lt_irrefl g),diagonalSide,singleStageCost,layout,D,Data.single] using run

end Cube.Padding.Banks

end BorderVNP
end Computability
end OAI
