import OAI.Computability.BorderVNP.DiagonalTallyAllocatedSuffix

/-! # Native selection and materialization of all cell and cube operands -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open VPVNP.BurstRAM RoutingISA BorderVNP.Cube BorderVNP.Cube.Tally DiagonalTallyAllocation DiagonalTallyMaterialize
open DiagonalTallyPacketEmit DiagonalTallyRAM

/-- Exact bound for the consecutive finite cube lookup and the five-word suffix writer. -/
def selectedOperandsTicks (count width : ℕ) :=
  DiagonalTallyPacketEmit.setup.slots+DiagonalTallyPacket.setup.slots+4+
    count*(2*(descStep.slots+1)+11)+(count*width)*(refStep.slots+1+8)+
    (DiagonalTallyCubeSuffix.setup.slots+count*(DiagonalTallyCubeSuffix.step.slots+1)+1+
      (writeFrame 15 62 63 35).slots)

/-- From the real packet bits and owned-vertex triples, execute both consecutive native
programs. The source supplied to the allocator now contains the IDs of those very
selected cube table entries. All previously routed common fields below the fresh
lookup area survive except the designated runtime count. -/
theorem ReportAllocation.selectedOperands {pre : BeforeTasks} {post : AfterTasks} {banks : CellBanks.Layout}
    {l : ReportLayout} {cs : List (ReportCell l)} {q : ReportCursor}
    (a : ReportAllocation pre post banks l cs q) {w n b h K s count : ℕ} (pub : Arg → Word w)
    (mac : TeamOpcode.Macros w 8) (bank : Bank w) (m : Memory w) (visits : Fin count → Visit n b h K s)
    (id : TableEntry n b h K s → ℕ) (D triples recipes trueAddr table : ℕ)
    (fp : (pub 0).val=l.frame) (vertices : count ≤ post.bound.vertices)
    (digits : argumentWidth n b h K s ≤ post.bound.cubeWidth)
    (zeroLo : banks.bankStart+banks.cells*banks.stride ≤ l.zeroAddr) (zeroHi : l.zeroAddr<pre.start)
    (oneLo : banks.bankStart ≤ trueAddr) (oneHi : trueAddr<pre.start)
    (old : DiagonalTallyMaterialize.supplied m (cellEnd cs q) q.descriptors (cellOperands cs q))
    (frameRoom : l.frame+101<post.start) (room : post.fresh<2^w)
    (h47 : (m (l.frame+47)).val=table) (tableFit : table+2^argumentWidth n b h K s ≤ post.start)
    (tableRead : ∀ k<2^argumentWidth n b h K s,(m (table+k)).val=idTable (selectorOrder n K h) (vertexOrder _) id k)
    (z : (m l.zeroAddr).val=0) (o : (m trueAddr).val=1)
    (banksAt : ∀ i,VertexAt m (visits i).base (visits i).selector (visits i).vertex (visits i).ends (visits i).supply)
    (sourceLo : ∀ i,∀ r∈recipe (visits i).selector (visits i).vertex b s,
      r.address (visits i).base l.zeroAddr trueAddr<post.start)
    (wordFit : ∀ i,l.parameters+id ((visits i).entry D)<2^w) :
    let packet := {(post.packetFrame count triples recipes l.zeroAddr trueAddr (Fintype.card (Vertex (n+1))))
      with width := argumentWidth n b h K s}
    let cells := cellOperands cs q
    let suffix := post.suffixFrame cells.length count l.zeroAddr l.parameters
    let os := cells++suffix.packetOperands l.frame trueAddr (fun i => id ((visits i).entry D))
    packet.resident (readings pub) (readings m) → packet.Fits (readings m) w l.frame →
    packet.recipeAt (readings m) n b h K s →
    (∀ i, (visits i).tripleAt (readings m) (triples+3*i.val)) →
    suffix.resident l.frame (readings m) →
    ∃ es t mt, Runs pub mac (.seq producePacketIDs DiagonalTallyCubeSuffix.appendCubeOperands) bank m es t mt ∧
      traceCost es ≤ selectedOperandsTicks count (argumentWidth n b h K s) ∧
      (∀ e∈es,e.choices=[] ∧ e.sign=.plus ∧ e.action.extra=0) ∧
      DiagonalTallyMaterialize.supplied mt post.fresh post.descriptors os ∧
      (mt (l.frame+35)).val=os.length ∧ os.length ≤ post.bound.operands ∧
      (∀ k,operandReads post.descriptors os k → outsidePointers l.frame k ∧ k≠l.frame+34) ∧
      ∀ k, k<post.start → k≠l.frame+35 → mt k=m k := by
  intro packet cells suffix os packetAt packetRoom recipeAt triplesAt suffixAt
  have ⟨_,gap,ids,packed,refs,desc⟩ := post.lookup_separated vertices
  have refRoom : post.lookupRefs+count*argumentWidth n b h K s ≤ post.ids :=
    (Nat.add_le_add_left (Nat.mul_le_mul_left count digits) _).trans gap
  have lower : post.start ≤ post.ids := by simp only [AfterTasks.ids,AfterTasks.lookupRefs,AfterTasks.lookupRows]; omega
  have hw : 0<w := by
    by_contra! bad
    have eq : w=0 := by omega
    rw [eq,pow_zero] at room
    omega
  obtain ⟨first,u,mu,run₁,cost₁,selected,keep,tr₁⟩ := producePacketIDs_runs_separated pub mac bank m packet visits id
    table post.ids D packetAt (fp ▸ packetRoom) recipeAt triplesAt banksAt z o sourceLo (fp ▸ h47)
    (fp ▸ suffixAt.2.2.2.1) tableRead tableFit refRoom (by change post.ids+count<2^w; omega)
  have word (k : ℕ) (low : k<post.start) : readings mu k=readings m k :=
    congrArg Fin.val (keep k (.inl low))
  have suffixAt' : suffix.resident (pub 0).val (readings mu) := by
    rw [fp]
    simp only [DiagonalTallyCubeSuffix.Frame.resident,word _ (show l.frame+35<post.start by omega),
      word _ (show l.frame+46<post.start by omega),word _ (show l.frame+44<post.start by omega),
      word _ (show l.frame+71<post.start by omega),word _ (show l.frame+81<post.start by omega),
      word _ (show l.frame+95<post.start by omega)]
    exact suffixAt
  obtain ⟨bound,idSpace⟩ := post.suffix_room a.cellCount vertices l.zeroAddr l.parameters
  obtain ⟨last,t,mt,run₂,cost₂,image,tr₂⟩ := DiagonalTallyCubeSuffix.appendCubeOperands_runs suffix pub mac u mu
    suffixAt' (by rw [fp]; omega) (bound.trans room) (by change post.ids+count<2^w; omega)
  rw [fp] at image
  have prefit : pre.start ≤ post.start := by have := a.preBefore; rw [pre.footprint] at this; omega
  have ptr : (mu (l.frame+82)).val=trueAddr := by
    change readings mu (l.frame+82)=_
    rw [word _ (by omega)]
    have he := packetAt.2.2.2.2.2.2.1
    change (m ((pub 0).val+82)).val=trueAddr at he
    exact fp ▸ he
  have z' : (mu l.zeroAddr).val=0 := (word _ (by omega)).trans z
  have o' : (mu trueAddr).val=1 := (word _ (by omega)).trans o
  have old' := a.supplied_after_lookup m mu count zeroLo zeroHi old vertices keep
  obtain ⟨valid,total,capacity,sep⟩ := a.fullSource mu mt trueAddr (fun i => id ((visits i).entry D)) vertices
    zeroLo zeroHi oneLo oneHi old' ptr z' o' selected wordFit hw image
  refine ⟨first++last,t,mt,run₁.seq run₂,?_,?_,valid,total,capacity,sep,?_⟩
  · rw [show traceCost (first++last)=traceCost first+traceCost last from VPVNP.RAMBuckets.cost_append ..]
    exact Nat.add_le_add cost₁ cost₂
  · intro e he
    exact (List.mem_append.mp he).elim (tr₁ e) (tr₂ e)
  · intro k low off
    apply Fin.ext
    change readings mt k=readings m k
    rw [image,suffix.image_before _ _ _ off,word k low]
    change k<post.descriptors+5*cells.length
    omega

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
