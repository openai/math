import OAI.Hierarchy.DescentPackedEpochReader
import OAI.Hierarchy.DescentPackedProfileArchive
import OAI.Hierarchy.DescentPackedInputNumber

namespace OAI
/-! # The ordinary matcher's input on an original chronological profile shelf -/

namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.Prepared
open DescentSixParty DescentSixParty.Chronology DescentKernelHistory.BitDescription DescentStageEdgeReceipt
open DescentTerminalEpochChart DescentTerminalEpochDecoder DescentTerminalEpochBits
open DescentPackedProfileArchive DescentPackedProfileWide DescentPackedProfileWindow
open ProtocolRAM Computability.VPVNP.BurstRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option maxHeartbeats 1200000

variable {F P Pin J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k G H w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {gadget : PoweredGadget F} {price ε : ℝ}

/-- The chooser may round the host and group extents up to the next complete
packed row. The occupied source ordering and every original pin ordinal stay equal. -/
theorem padded_inputNumber {G' H' : ℕ} (A : GroupStage W gadget price ε J V k) (he : 0≤ε)
    (groups : J↪Fin G) (hosts : V↪Fin H) (groups' : J↪Fin G') (hosts' : V↪Fin H')
    (groupRoom : G≤G') (hostRoom : H≤H')
    (sameG : ∀g,(groups' g).val=(groups g).val) (sameH : ∀h,(hosts' h).val=(hosts h).val) :
    inputNumber he A groups hosts=inputNumber he A groups' hosts' := by
  let a:=(sourceChart he A groups hosts).trans Fin.valEmbedding
  let b:=(sourceChart he A groups' hosts').trans Fin.valEmbedding
  have order (u v : ScanColonies he A.stage) : a u<a v ↔ b u<b v := by
    let s:=DescentStageEdgeReceipt.nativeAddress he A.stage u
    let t:=DescentStageEdgeReceipt.nativeAddress he A.stage v
    change (sourceChart he A groups hosts u).val<(sourceChart he A groups hosts v).val ↔
      (sourceChart he A groups' hosts' u).val<(sourceChart he A groups' hosts' v).val
    simp only [sourceChart_val,sameG,sameH]
    exact padded_order _ _ _ _ _ _ (groups s.1.1).isLt (groups t.1.1).isLt
      (hosts s.1.2).isLt (hosts t.1.2).isLt groupRoom hostRoom
  apply Equiv.ext
  rintro ⟨c,e⟩
  apply Fin.ext
  rw [rank_address he A groups hosts c e,rank_address he A groups' hosts' c e]
  exact congrArg (fun n=>n+_) (before_padded a b (countIn he A) order c)

def ranked (A : GroupStage W gadget price ε J V k) (he : 0≤ε) (groups : J↪Fin G) (hosts : V↪Fin H)
    (choice : (A.stage.result he).Choice) (reblock : Normalize ((A.stage.result he).state choice)) :
    RankedSelection F P d bits gadget ε :=
  ⟨⟨W,price*A.wire,he,A.stage,choice,reblock⟩,inputNumber he A groups hosts⟩

theorem ticket_ranked {q : ℝ} {S : DescentCompiler.AtomSchedule} {age z D wire hist z' D' H' G' : ℕ}
    (source : Reached W gadget q ε S k age z D wire hist) (he : 0≤ε)
    {choice : (source.placement.stage.result he).Choice} {reblock : Normalize ((source.placement.stage.result he).state choice)}
    {target : Reached reblock.result gadget q ε S k (age+1) z' D' wire hist}
    (step : OrdinaryLink source he source.placement.stage choice reblock target)
    (groups : Fin (S.groupCount age)↪Fin G') (hosts : source.V↪Fin H')
    (groupRoom : S.groupCount age≤G') (hostRoom : Fintype.card source.V≤H')
    (sameG : ∀g,(groups g).val=g.val) (sameH : ∀v,(hosts v).val=(source.vertex v).val) :
    (⟨step.selection,step.inputPair⟩ : RankedSelection F P d bits gadget ε)=
      ranked source.placement he groups hosts choice reblock := by
  have old : step.inputPair=inputNumbers he source:=eq_of_heq step.inputRows
  have equal:=padded_inputNumber source.placement he (Function.Embedding.refl _) source.vertex groups hosts
    groupRoom hostRoom sameG sameH
  change (⟨step.selection,step.inputPair⟩ : RankedSelection F P d bits gadget ε)=
    ⟨step.selection,inputNumber he source.placement groups hosts⟩
  exact congrArg (fun num=> (⟨step.selection,num⟩ : RankedSelection F P d bits gadget ε)) (old.trans equal)

/-- For an ordinary step, the raw words in the incoming memory and the typed
choice on the selected path come from the same original profile pins. -/
theorem old_pins (A : GroupStage W gadget price ε J V k) (he : 0≤ε) (groups : J↪Fin G) (hosts : V↪Fin H)
    (choice : (A.stage.result he).Choice) (reblock : Normalize ((A.stage.result he).state choice))
    (headers : List (Source Pin)) (path : List (RankedSelection F P d bits gadget ε)) (z : Pin→Bool)
    (honest : headers.map (rawAt z)=path.map (issuedProfile gadget))
    (i : ℕ) (src : Source Pin) (origin : headers[i]?=some src)
    (entered : path[i]?=some (ranked A he groups hosts choice reblock))
    (digit grain : ℕ) (extend : width src.C≤digit) (raw : Bank) (start current : Memory w)
    (loaded : Stored src digit grain extend raw z start)
    (unchanged : ∀j < raw.size,current (raw.base+j)=start (raw.base+j)) :
    let stream:=wideCell src.pin z digit extend
    (∀j,(stream j).val=profileAt (inputNumber he A groups hosts) ((scannedRows he A.stage).profile choice) j) ∧
      ∀j < raw.size,current (raw.base+j)=((word digit grain stream j).val:Word w) := by
  exact ⟨original_fields src z headers path honest origin entered,
    preserve src digit grain extend raw z start current loaded unchanged⟩

/-- A native stage with the two-sided frame from `Prepared.run` preserves
every original profile shelf in the subsequent part of the calendar. -/
theorem future_pins (src : Source Pin) (digit grain : ℕ) (extend : width src.C≤digit) (raw : Bank)
    (z : Pin→Bool) (old later : Memory w) (initial limit : ℕ)
    (previous : Stored src digit grain extend raw z old)
    (frame : ∀a,a < initial ∨ limit ≤ a → later a=old a)
    (disjoint : raw.base+raw.size ≤ initial ∨ limit≤raw.base) :
    Stored src digit grain extend raw z later := by
  apply preserve src digit grain extend raw z old later previous
  intro j hj
  apply frame
  rcases disjoint with below|above
  · exact Or.inl (by omega)
  · exact Or.inr (above.trans (Nat.le_add_right ..))

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage.Prepared

end OAI
