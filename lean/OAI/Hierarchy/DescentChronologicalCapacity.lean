import OAI.Hierarchy.DescentPrivateShapeNumbers
import OAI.Hierarchy.DescentCensusResetRows
import OAI.Hierarchy.DescentOrderedReentry
import OAI.Hierarchy.DescentIssuedChronology
import OAI.Hierarchy.DescentStageAllWidths

namespace OAI
/-! # Branch-independent physical census extents for the chronological compiler -/

namespace Hierarchy.DescentSixParty
open DescentCompiler DescentColonies DescentKernelHistory
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d k : ℕ} {bits : P→ℕ} {G : PoweredGadget F} {q ε : ℝ}
    {S : AtomSchedule} {W A : MarkedWorld F d P bits} {i z D w s : ℕ}

namespace Reached



def edgeLimit (S : AtomSchedule) := siteLimit S*(2^(8+S.capGain*S.length)+1)

theorem slot_limit (r : Reached W G q ε S k i z D w s) (age : i≤S.length) (radix : S.radix=2^k) :
    (S.groupCount i*Fintype.card r.V)*2^k≤ siteLimit S := by
  have h:=Nat.mul_le_mul_right (S.groupCount i*S.radix) r.valid.host
  simpa [radix,siteLimit,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using h.trans (S.slot_reserve age)

theorem sites_le (r : Reached W G q ε S k i z D w s) (age : i≤S.length) (radix : S.radix=2^k) :
    Fintype.card W.graph.Site≤ siteLimit S := by
  have count:=Fintype.card_le_of_embedding (r.placement.siteSlot r.vertex r.valid.coordinates)
  exact (by simpa only [Fintype.card_fin] using count : Fintype.card W.graph.Site≤(S.groupCount i*Fintype.card r.V)*2^k).trans (r.slot_limit age radix)

/-- This applies simultaneously to all profiles, including empty paint classes. -/
theorem core_le (r : Reached W G q ε S k i z D w s) (age : i≤S.length) (radix : S.radix=2^k) :
    W.core.card≤ siteLimit S*2^(8+S.capGain*i) := by
  let A:=r.placement
  have bound:=W.census_paid W.core A.pos A.block (fun u=>A.hub (A.pos u).2) A.records A.wire A.hist (A.z*G.b) A.cap
    A.wirePos (Nat.mul_pos A.unitPos G.base_pos) (fun e he=>(A.widths e he).ge) A.small
  simpa [A,Fintype.card_prod] using bound.trans (Nat.mul_le_mul (by simpa using r.slot_limit age radix) r.valid.capacity)

theorem pairs_le {u : ℝ} (r : Reached W G q ε S k i z D w s) (age : i≤S.length)
    (radix : S.radix=2^k) (he : 0≤ε) (T : StageInput W G u ε) :
    2*Fintype.card (BitDescription.scannedRows he T).pairs ≤
      siteLimit S*2^(8+S.capGain*i) := by
  let pairs:=BitDescription.scannedRows he T
  let wires : (pairs.pairs×Fin 2)↪↥W.core :=
    ⟨fun x=>⟨pairs.pick x,pairs.picked x⟩,
      fun _ _ eqn=>pairs.pick.injective (congrArg Subtype.val eqn)⟩
  have count := Fintype.card_le_of_embedding wires
  have hit : 2*Fintype.card pairs.pairs≤W.core.card := by
    simpa only [Fintype.card_prod,Fintype.card_fin,Fintype.card_coe,Nat.mul_comm 2] using count
  exact hit.trans (r.core_le age radix)

theorem edge_limit_of_blank (r : Reached W G q ε S k i z D w s) (age : i≤S.length) (radix : S.radix=2^k)
    (blank : W.blank.card≤ siteLimit S) : Fintype.card W.graph.Edge≤edgeLimit S := by
  let A:=r.placement
  have cap := r.valid.capacity.trans (Nat.pow_le_pow_right (by decide : 0<2)
    (Nat.add_le_add_left (Nat.mul_le_mul_left S.capGain age) 8))
  have bound:=W.census_all A.pos A.block (fun u=>A.hub (A.pos u).2) A.records A.wire A.hist (A.z*G.b) A.cap
    A.wirePos (Nat.mul_pos A.unitPos G.base_pos) r.valid.divides A.widths A.small
  have slots : (Fintype.card (Fin (S.groupCount i)×r.V)*2^k)≤ siteLimit S := by simpa using r.slot_limit age radix
  simpa [edgeLimit,Nat.mul_add] using bound.trans (Nat.add_le_add (Nat.mul_le_mul slots cap) blank)

end Reached

namespace Chronology
variable {a b z' D' : ℕ} {first : Reached W G q ε S k a z D w s} {last : Reached A G q ε S k b z' D' w s}

theorem start_blank {cp pins : ℕ} (X : Catalyst.Approximation F cp pins) (m s : ℕ)
    (positive : 0<s) (c : (DescentInitialHost.initialGroup X m s).Choice) :
    ((DescentInitialHost.initialGroup X m s).state c).blank=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  have zero:=((MarkedWorld.mem_blank _ _).mp he).2
  rw [DescentInitialHost.source_all_widths X c e] at zero
  omega

theorem OrdinaryLink.blank {hε : 0≤ε} {val : ℝ} {T : StageInput W G val ε} {c : (T.result hε).Choice}
    {n : Normalize ((T.result hε).state c)}
    {next : Reached n.result G q ε S k (a+1) z' D' w s} (_issued : OrdinaryLink first hε T c n next) :
    n.result.blank.card≤W.blank.card := by
  apply (MarkedWorld.blank_normalize _ n).trans
  let rows:=BitDescription.scannedRows hε T
  rw [rows.state c]
  exact W.blank_selected G _ _ _ _ _ _

theorem ClosedReset_blank {n h C f g cut tail : ℕ} {ctl : ResetRates G S k D n h C f g cut tail}
    (closed : ClosedReset first ctl) : closed.reblock.result.blank.card≤Fintype.card closed.reblock.result.graph.Site := by
  let Z:=closed.reset
  let T:=closed.terminals
  let key:=DescentOrderedReset.grains W closed.count closed.order
  have positive:0<Z.unit := by rw [closed.unit,←first.grain];exact Nat.mul_pos first.placement.unitPos G.base_pos
  have old:=Z.ordered_blank T key positive
  unfold ClosedReset.reblock ResetInput.namedReset
  rw [Normalize.appendNames_result]
  apply (MarkedWorld.blank_normalize _ (.named _ _ _ (.done _))).trans
  exact old

theorem Path.blank_le (path : Path first last) (radix : S.radix=2^k) (age : b≤S.length) (initial : W.blank.card≤Reached.siteLimit S) :
    A.blank.card≤Reached.siteLimit S := by
  induction path with
  | here=>exact initial
  | ordinary prev link ih=>exact link.blank.trans (ih (by omega))
  | reset prev closed ih=>exact (ClosedReset_blank closed).trans (closed.next.sites_le age radix)

theorem Path.public_census (path : Path first last) (radix : S.radix=2^k) (age : b≤S.length)
    (initial : W.blank.card≤Reached.siteLimit S) :
    Fintype.card A.graph.Edge≤Reached.edgeLimit S ∧ Fintype.card A.graph.Site≤Reached.siteLimit S :=
  ⟨last.edge_limit_of_blank age radix (path.blank_le radix age initial),last.sites_le age radix⟩

end Chronology
end
end Hierarchy.DescentSixParty

end OAI
