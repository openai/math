import OAI.Hierarchy.DescentTerminalBookPrivateEntry

namespace OAI
/-! # Exact six-field geometry before the row plan, including empty physical homes -/
namespace Hierarchy.DescentTerminalLocalPortBook.Board
open DescentSixParty DescentCompiler DescentSharedCableNames DescentColonies DescentChosenRouter DescentPacking
open DescentTerminalPeerChronology DescentTerminalPointerDigits DescentTerminalGrainProfiles DescentTerminalPaidHeaderEvents
open DescentTerminalGraphPositions DescentTerminalCableOrder DescentSortedRoster DescentPackedTicketChronology
open DescentStageEdgeReceipt DescentPacking.PackedMatch.Local.Stage DescentKernelHistory Computability.BorderVNP.Crossing
open ThreeFlat.Routing
open scoped Classical BigOperators
noncomputable section

variable {F P V:Type} [Field F] [Fintype P] [Fintype V] [DecidableEq V] {groups d k i H p scale:ℕ}
    {bits:P→ℕ} {W:MarkedWorld F d P bits} {G:PoweredGadget F} {price ε:ℝ}
    (A:GroupStage W G price ε (Fin groups) V k) (hosts:V↪Fin H) (S:AtomSchedule) (ready:A.StateBounds S i)
    (native:W.graph.Edge↪Fin (Fintype.card W.graph.Edge)) (raw:Fin H→Fin A.degree→Option (Fin H))
local notation "ord" => native.trans Fin.valEmbedding
local notation "names" => cableNames k (groupRank (Fin.valEmbedding (n:=groups)) (hosts.trans Fin.valEmbedding))
local notation "atH" => fun v:W.graph.Site=>hosts (Prod.snd (A.pos v))

/-- Each premise is a read of geometry that exists before the directory is
issued. Roster entries use public host identifiers; signed entries measure
the two short arm banks, and population distinguishes arity zero from vacancy. -/
structure Observed (boards:Fin H→Board A.degree groups (2^k) A.cap) : Prop where
  roster : ∀o,present raw (hosts o)=(A.near o).map hosts
  side : ∀h j z,indexed raw h j=some z→(boards h).side j=compare h.val z.val
  signed : ∀o g b,(boards (hosts o)).ports g b=Stage.signedPanel A ord S ready names ((g,o),b)
  blank : ∀h,(∀o,hosts o≠h)→∀g b t,(boards h).ports g b t=none
  resident : ∀h,Resident (p:=p) A hosts S ready ord names h (boards h)

variable (boards:Fin H→Board A.degree groups (2^k) A.cap)
    (seen:Observed (p:=p) A hosts S ready native raw boards)
    (coords:Function.Injective (fun s=>(A.pos s,A.block s))) (birth:SiteOrder A hosts) (sorted:SourceSorted W native)
    (hp:0<p) (whole:A.z*G.b=scale*p) («public»:ℕ) (size:∀z,bits z=«public»*p)

include seen coords birth sorted hp whole size in
theorem counts_read (h:Fin H) (j:Fin (A.degree+1)) :
    (boards h).counts scale j=grainCount (p:=p) (indexed raw) W.graph atH h j := by
  refine Fin.cases ?_ (fun l=>?_) j
  · exact public_count A hosts S ready ord names coords scale «public» hp whole size h (boards h) (seen.resident h)
  · change ((boards h).keys l).card*scale=grainCount (p:=p) (indexed raw) W.graph atH h l.succ
    cases tag:indexed raw h l with
    | none=>
      have no: (boards h).keys l=∅ := by
        by_cases live:∃o,hosts o=h
        · obtain ⟨o,rfl⟩:=live
          exact missing_keys A hosts S ready native raw seen.roster o (boards _) l tag (seen.signed o)
        · ext z
          simp [keys,peerKeys,mem_keys,seen.blank h (not_exists.mp live)]
      simp [no,grainCount,DescentTerminalPaidHeaderEvents.label,tag]
    | some z=>
      have value:((boards h).keys l).card*scale=pairMass W.graph atH (pair h z)/p := by
        by_cases live:∃o,hosts o=h
        · obtain ⟨o,rfl⟩:=live
          rw [reached_keys A hosts S ready native raw seen.roster o (boards _) l z tag (seen.side _ _ _ tag)
            (seen.signed o)]
          exact entire_pair A hosts S ready native birth sorted hp whole _ z
        · have no:(boards h).keys l=∅:=by ext z;simp [keys,peerKeys,mem_keys,seen.blank h (not_exists.mp live)]
          simp only [no,Finset.card_empty,Nat.zero_mul,Counter.absent_mass A hosts h z (not_exists.mp live),Nat.zero_div]
      simpa [grainCount,DescentTerminalPaidHeaderEvents.label,tag] using value

end
end Hierarchy.DescentTerminalLocalPortBook.Board

end OAI
