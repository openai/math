import OAI.Computability.BorderVNP.CubeScatterPaddingArenaFields
import OAI.Computability.BorderVNP.CubeScatterPaddingTableReadback
import OAI.Computability.BorderVNP.RoutingISACellBanks

/-! # Preserving the actual width, owner and three-word directory images

The native scheduler writes its weights, team totals and owners after the width
array. Cell-bank setup writes at or above the host directory. The three packet
fields sit between the owner array and that directory.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Padding

open RoutingISA Tally

/-- Exactly the three ranges read by the metadata stages of the native padding guard. -/
def Pointers.Metadata (P : Pointers) (n d a : ℕ) : Prop :=
  (P.owners ≤ a ∧ a < P.owners+d) ∨
  (P.widths ≤ a ∧ a < P.widths+d^(n+1)*d^(n+1)) ∨
  (P.triples ≤ a ∧ a < P.triples+3*(d^(n+1)*d^(n+1)))

/-- Transfer the three actual native producer readouts through an arbitrary later pass
that leaves these addresses intact. -/
theorem TableReadback.transfer {P : Pointers} {d n : ℕ} {before after sched widths triples : ℕ → ℕ}
    {teams : TeamNative.Layout} {interval : NativeIntervals.Layout} {pair : PairDirectory.Layout}
    (initial : TableReadback P d n before teams sched interval widths pair triples)
    (preserved : ∀ a, P.Metadata n d a → after a = before a) :
    TableReadback P d n after teams sched interval widths pair triples := by
  constructor
  · intro g
    exact (preserved _ (Or.inl ⟨Nat.le_add_right ..,Nat.add_lt_add_left g.isLt _⟩)).trans (initial.owner g)
  · intro k hk
    exact (preserved _ (Or.inr (Or.inl ⟨Nat.le_add_right ..,Nat.add_lt_add_left hk _⟩))).trans (initial.width k hk)
  · intro k hk f hf
    exact (preserved _ (Or.inr (Or.inr ⟨by omega,by omega⟩))).trans (initial.fields k hk f hf)

/-- Every addressed padding metadata word precedes the true transmission directory
and lies outside both packet and singleton output reservations. -/
theorem arena_metadata_range (L : CubeArena.Layout) (a : ℕ)
    (hit : (arenaPointers L).Metadata L.n L.header.d a) :
    L.vertexBase ≤ a ∧ a < L.records := by
  have cut : L.vertexBase ≤ L.widthBase := by
    unfold CubeArena.Layout.widthBase CubeArena.Layout.dataMean CubeArena.Layout.cableMean
      CubeArena.Layout.demands CubeArena.Layout.nodes CubeArena.Layout.heads CubeArena.Layout.publicBase
    omega
  rcases hit with h | h | h
  all_goals
    dsimp only [arenaPointers,CubeArena.Layout.records,CubeArena.Layout.hostDirectory,CubeArena.Layout.pairDirectory,
      CubeArena.Layout.ownerBase,CubeArena.Layout.teamTotals,CubeArena.Layout.groupWeights,
      CubeArena.Layout.powerBase,CubeArena.Layout.ordinalBase,CubeArena.Layout.alphabet] at h ⊢
    simp only [pow_two] at h ⊢
    omega

/-- After real group-weight scheduling, cell-bank installation and packet-directory
construction, all three original readouts coexist at the actual arena addresses. -/
theorem tableReadback_after_pair (L : CubeArena.Layout) {weights : GroupWeights.Layout} {teams : TeamNative.Layout}
    {interval : NativeIntervals.Layout} {pair : PairDirectory.Layout} {cellBanks : CellBanks.Layout}
    {before scheduled directed table : ℕ → ℕ} (count : ℕ)
    (aligned : weights.groups = L.header.d ∧ weights.weights = L.groupWeights ∧ teams.totals = L.teamTotals ∧
      teams.owners = L.ownerBase ∧ interval.widths = L.widthBase ∧ cellBanks.dest = L.hostDirectory ∧ pair.table = L.pairDirectory)
    (widthsKept : ∀ k < L.alphabet^2, before (L.widthBase+k) = directed (interval.widths+k))
    (schedule : GroupWeights.ScheduleResult weights teams before scheduled)
    (image : PairDirectory.Image pair (cellBanks.written scheduled count) pair.count table) :
    TableReadback (arenaPointers L) L.header.d L.n table teams scheduled interval directed pair table := by
  obtain ⟨groups,ws,totals,os,_,cs,ps⟩ := aligned
  have widthsEnd : L.widthBase+L.alphabet^2 ≤ L.groupWeights := by
    unfold CubeArena.Layout.groupWeights CubeArena.Layout.powerBase CubeArena.Layout.ordinalBase; omega
  have mid : L.groupWeights ≤ L.teamTotals ∧ L.teamTotals ≤ L.ownerBase := by
    dsimp only [CubeArena.Layout.teamTotals,CubeArena.Layout.ownerBase]; omega
  have oh : L.ownerBase+L.header.d ≤ L.pairDirectory := le_rfl
  have ph : L.pairDirectory ≤ L.hostDirectory := Nat.le_add_right ..
  have kept (a : ℕ) (low : a < L.pairDirectory) : table a = scheduled a :=
    (image.outside a (Or.inl (ps ▸ low))).trans
      (cellBanks.written_outside scheduled count a (Or.inl (cs ▸ low.trans_le ph)))
  constructor
  · intro g
    change table (L.ownerBase+g.val) = _
    rw [os]
    exact kept _ ((Nat.add_lt_add_left g.isLt _).trans_le oh)
  · intro k hk
    change table (L.widthBase+k) = _
    change k < L.alphabet*L.alphabet at hk
    rw [← pow_two] at hk
    have low := (Nat.add_lt_add_left hk L.widthBase).trans_le widthsEnd
    rw [kept _ (low.trans_le (mid.1.trans (mid.2.trans ((Nat.le_add_right _ _).trans oh))))]
    apply (schedule.other _ ?_ ?_ ?_).trans (widthsKept k hk)
    · intro u _; rw [ws]; omega
    · intro j; rw [totals]; omega
    · intro u _; rw [os]; omega
  · intro k _ f _
    rw [ps]; rfl

/-- Between the native directed-interval return and the greedy scheduler, the powers
install and both declaration stages leave all occupied-width words intact. -/
theorem widths_after_prepare (L : CubeArena.Layout) (directed : ℕ → ℕ) (broadcast k : ℕ)
    (hk : k < L.alphabet^2) :
    (L.header.decoder broadcast).finalImage
      (L.header.image L.n (selectorWidth L.n L.K L.h)
        (CubePowers.image L.header.d L.powerBase (L.n+1) directed)) (L.widthBase+k) = directed (L.widthBase+k) := by
  have start : L.header.packetBase ≤ L.widthBase := by
    have packet : L.header.packetBase ≤ L.packetEnd := Nat.le_add_right ..
    have single : L.packetEnd ≤ L.singleBank := by unfold CubeArena.Layout.singleBank; omega
    have pub : L.vertexBase ≤ L.widthBase := by
      unfold CubeArena.Layout.widthBase CubeArena.Layout.dataMean CubeArena.Layout.cableMean
        CubeArena.Layout.demands CubeArena.Layout.nodes CubeArena.Layout.heads CubeArena.Layout.publicBase
      omega
    exact packet.trans (single.trans (L.separated.2.1.trans pub))
  change L.header.header+13+2*L.header.entries+L.header.a ≤ L.widthBase at start
  rw [HeaderDecode.Layout.finalOutside _ _ (by change _ ≠ L.header.header+5; omega)
    (Or.inr (by change L.header.header+13+L.header.entries+(L.header.decoder broadcast).entries ≤ _;
                 have eq : (L.header.decoder broadcast).entries=L.header.entries := rfl; rw [eq]; omega))
    (Or.inr (by change L.header.header+13+2*L.header.entries+L.header.a ≤ _; omega))]
  have upper : L.widthBase+k < L.powerBase := by unfold CubeArena.Layout.powerBase CubeArena.Layout.ordinalBase; omega
  simp [CubeHeaderInstall.Inputs.image,CubePowers.image,show ¬L.widthBase+k < L.header.header+13 by omega,upper.not_ge]

end Cube.Padding

end BorderVNP
end Computability
end OAI
