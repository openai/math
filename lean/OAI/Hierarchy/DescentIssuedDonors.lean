import OAI.Hierarchy.DescentIssuedCommonChart
import OAI.Hierarchy.DescentDonorPublicCounts
import OAI.Hierarchy.DescentIssuedDonorChart
import OAI.Hierarchy.DescentIssuedPanelRegister
import OAI.Hierarchy.DescentOrdinaryDonorRows

namespace OAI
/-! # The bounded eleven-role donors of the actual chronological branch -/

namespace Hierarchy.DescentSixParty.Chronology
open Computability.BorderVNP.Crossing DescentKernelHistory DescentStageEdgeReceipt DescentPacking DescentHostDirectory
open DescentSIMDLookup DescentRawCablePanel DescentHostDegree DescentSixParty.StarKeys
open scoped Classical
noncomputable section
set_option quotPrecheck false

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
variable {S : DescentCompiler.AtomSchedule} {q u ε : ℝ} {k i z D wire hist : ℕ}
variable {W : MarkedWorld F d P bits} {source : Reached W G q ε S k i z D wire hist}
variable {he : 0≤ε} {T : StageInput W G u ε} {c : (T.result he).Choice}
variable {n : Normalize ((T.result he).state c)} {z' D' : ℕ}
variable {target : Reached n.result G q ε S k (i+1) z' D' wire hist} (ticket : OrdinaryLink source he T c n target)
variable {H : ℕ} (vertex : source.V↪Fin H)

local notation "A" => source.placement
local notation "r" => BitDescription.scannedRows he T
local notation "cellBits" => normBits (A).cap G.b G.C G.k
local notation "J" => S.groupCount i*2^k*(A).cap
local notation "lay" => bestLayout (branchWidth G (fun _ : (r).pairs=>T.z) ((r).profile c))
local notation "venue" => newSite W.graph (r).pick lay (r).pack
local notation "rank" => groupRank Fin.valEmbedding (source.vertex.trans Fin.valEmbedding)
local notation "shelf" => 2^(packExponent 20 T.Δ)+2
local notation "gain" => gainExponent 20 T.Δ
local notation "receipt" => IssuedRows.common_chart he T c ticket.issued ((r).state c)

def OrdinaryLink.donorChart : IssuedDonorChart he T (Fin (S.groupCount i)×source.V) := (receipt).choose

def OrdinaryLink.donorKey : (scanWorld he T c).graph.Site↪Key (Fin (S.groupCount i)×source.V) :=
  ticket.donorChart.key he T c

def OrdinaryLink.donorHub : Fin (S.groupCount i)×source.V→Bool := ticket.donorChart.hub

/-- The colony coordinates are precisely the scanned physical directory. -/
theorem OrdinaryLink.donor_source_position (u : W.graph.Site) :
    (ticket.donorChart.col (scanHomeAt he T u)).1=(A).pos u :=
  eq_of_heq ((ticket.donorChart.old u).1.trans (ticket.sourcePosition u))

/-- Both the group/host and the exact dyadic depth and prefix are the old
actor's physical mounted scan coordinates. -/
theorem OrdinaryLink.donor_source_colony (u : W.graph.Site) :
    ticket.donorChart.col (scanHomeAt he T u)=((A).pos u,(nativeAddress he T (scanHomeAt he T u)).2) :=
  Prod.ext (ticket.donor_source_position u) (ticket.donorChart.code _)

theorem OrdinaryLink.donor_source_hub (u : W.graph.Site) :
    ticket.donorHub (ticket.donorChart.col (scanHomeAt he T u)).1=(A).hub ((A).pos u).2 :=
  (ticket.donorChart.old u).2.trans (congrFun ticket.sourceFlags u)

/-- At every occupied resolved key, including a thin donor transported to a
chosen center, the advertised bit is the actual earlier group's own hub bit. -/
theorem OrdinaryLink.donor_key_hub (x : (scanWorld he T c).graph.Site) :
    ticket.donorHub (ticket.donorKey x).1=(A).hub (ticket.donorKey x).1.2 := by
  obtain ⟨u,atHost⟩:=ticket.donorChart.key_host he T c x
  change (ticket.donorKey x).1=(ticket.donorChart.col (scanHomeAt he T u)).1 at atHost
  rw [atHost,ticket.donor_source_hub,ticket.donor_source_position]

/-- The local donor sample resolves each old site and each of the six added
party sites through the same physical thick/thin pairing used by the stage. -/
theorem OrdinaryLink.donor_old_key (x : W.graph.Site) :
    ticket.donorKey (venue (.inl x))=
      packAddress W.graph W.core (scanHomeAt he T) (scanColorAt he T) T.cap ticket.donorChart.col
        (resolve (chosenSlot W.graph W.core (scanHomeAt he T) (scanColorAt he T) T.cap)
          (chosenCenter W.graph W.core (scanHomeAt he T) (scanColorAt he T) T.cap lay) ((r).pack x)) := rfl

theorem OrdinaryLink.donor_born_key (p : (r).pairs) (j : Fin 6) :
    ticket.donorKey (venue (.inr (p,j)))=
      ticket.donorKey (venue (.inl (endpoint W.graph (r).pick p (cluster lay j)))) := rfl


/-- The local venue has one dyadic prefix and one pack slot. Its width
does not depend on the number of hosts or old edges. -/
theorem donorNameBits_le (age degree : ℕ) :
    donorNameBits age degree≤age+packExponent 20 degree+3 := by
  let a:=packExponent 20 degree
  apply (Nat.clog_le_iff_le_pow (by decide : 1<2)).2
  change 2^(age+1)*(2^a+2)≤2^(age+a+3)
  rw [show age+a+3=(age+1)+(a+2) by omega,pow_add (2:ℕ) (age+1) (a+2)]
  apply Nat.mul_le_mul_left
  have h:=Nat.two_pow_pos a
  rw [pow_add]
  omega

theorem donorFormat_le (age degree cap b C pad : ℕ) :
    max (bundleBits 3 (donorNameBits age degree) (normBits cap b C pad)) ((2+normBits cap b C pad)*11)≤
      39+5*(age+packExponent 20 degree)+11*normBits cap b C pad := by
  have bound:=donorNameBits_le age degree
  unfold bundleBits
  exact Nat.max_le.mpr ⟨by omega,by omega⟩

/-- This input row uses precisely the old first grain, both old endpoints and
the three measured anchors of the matched motif. Its relative host code uses three bits. -/
def OrdinaryLink.measuredDonors : Fin H→Fin J→Donor 3 (donorNameBits T.k T.Δ) cellBits :=
  physicalRows (hCode:=T.k) A S source.valid (source.order.trans Fin.valEmbedding) vertex (Equiv.refl _)
    (r).pick lay (r).pack ticket.donorKey ticket.donorHub shelf ((r).profile c)
    (relative (r).pick lay (r).pack ticket.donorKey)

/-- The row writer can use its prior placement's public hub function directly,
including inside all five rooted endpoints of a donor. -/
theorem OrdinaryLink.measuredDonors_publicHub :
    ticket.measuredDonors vertex =
      physicalRows (hCode:=T.k) A S source.valid (source.order.trans Fin.valEmbedding) vertex (Equiv.refl _)
        (r).pick lay (r).pack ticket.donorKey (fun v=>(A).hub v.2) shelf ((r).profile c)
        (relative (r).pick lay (r).pack ticket.donorKey) := by
  funext v j
  by_cases present : ∃e,oldSlot A S source.valid (source.order.trans Fin.valEmbedding) vertex (Equiv.refl _) e=(v,j)
  · have same (u : W.graph.Site) : ticket.donorHub (ticket.donorKey (venue (.inl u))).1 =
        (A).hub (ticket.donorKey (venue (.inl u))).1.2 := ticket.donor_key_hub _
    simp only [OrdinaryLink.measuredDonors,physicalRows,dite_eq_left present,measuredDonor,rooted,same]
  · simp only [OrdinaryLink.measuredDonors,physicalRows,dite_eq_right present]

/-- The resulting lookup matches the two actual contracted endpoint comparisons,
including when the parent tape was subsequently reordered. -/
theorem OrdinaryLink.donor_words (v : Fin H) (j : Fin (J*11)) :
    report T.k gain shelf (ticket.measuredDonors vertex v (finProdFinEquiv.symm j).1) (finProdFinEquiv.symm j).2=
      ticket.issuedPanel vertex v j := by
  let key:=ticket.donorKey
  let hub:=ticket.donorHub
  have fits (x) : key x∈keys T.k shelf := (receipt).choose_spec.1.1 x
  have post (x y) := (receipt).choose_spec.1.2 x y
  have room : 2^(T.k+1)*shelf≤2^(donorNameBits T.k T.Δ) := Nat.le_pow_clog (by decide : 1<2) _
  let N:=rawGraph he T c
  let prior:=(originalId ((T.result he).state c).graph.Site) ∘ rawInput he T c ((r).state c)
  let next:=rawOwner he T c n ((r).state c) (originalId _)
  have coded (x y : Key (Fin (S.groupCount i)×source.V)) (hx : x∈keys T.k shelf) (hy : y∈keys T.k shelf) :
      packedNumber rank T.k shelf x=packedNumber rank T.k shelf y ↔ x=y :=
    ⟨packed_inj (rank).injective hx hy,congrArg _⟩
  have before (x y : N.Site) :
      packedNumber rank T.k shelf (key (venue x))=packedNumber rank T.k shelf (key (venue y)) ↔ prior x=prior y := by
    exact (coded _ _ (fits (venue x)) (fits (venue y))).trans
      (key.injective.eq_iff.trans ((rawInput_eq_iff he T c ((r).state c) x y).symm.trans
        (originalId _).injective.eq_iff.symm))
  have after_ (x y : N.Site) :
      packedNumber rank T.k shelf (mergeHub hub T.k gain (key (venue x)))=
      packedNumber rank T.k shelf (mergeHub hub T.k gain (key (venue y))) ↔ next x=next y := by
    exact (coded _ _ (merged_mem_keys hub T.k gain shelf (fits (venue x)))
      (merged_mem_keys hub T.k gain shelf (fits (venue y)))).trans
      ((post x y).symm.trans (originalId _).injective.eq_iff.symm)
  have labels := donor_panel (hCode:=T.k) A S source.valid (source.order.trans Fin.valEmbedding) vertex (Equiv.refl _)
    (r).pick lay (r).pack rank key hub gain shelf fits room ((r).profile c)
    (relative (r).pick lay (r).pack key) (fun e _ _ hx hy=>relative_eq (r).pick lay (r).pack key e hx hy) v j
  refine labels.trans ?_
  let trueCell (e : Live A (r).pick) := cell
    (decide (prior (N.src e.val)=prior (N.dst e.val)))
    (decide (next (N.src e.val)=next (N.dst e.val)))
    (⟨normalized A ((r).profile c) e.val,normalized_fits A S source.valid ((r).profile c) e.val⟩:Cell cellBits)
  have each (e : Live A (r).pick) :
      sample (hCode:=T.k) A S source.valid (r).pick lay (r).pack rank key hub gain shelf ((r).profile c) e=trueCell e := by
    exact congrArg₂ (fun x y => cell x y
      (⟨normalized A ((r).profile c) e.val,normalized_fits A S source.valid ((r).profile c) e.val⟩ : Cell cellBits))
      (decide_eq_decide.mpr (before (N.src e.val) (N.dst e.val)))
      (decide_eq_decide.mpr (after_ (N.src e.val) (N.dst e.val)))
  exact congrArg (fun field=>place (slot A S source.valid (source.order.trans Fin.valEmbedding)
    vertex (Equiv.refl _) (r).pick) field v j) (funext each)

end
end Hierarchy.DescentSixParty.Chronology

end OAI
