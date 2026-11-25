import OAI.Hierarchy.TraceResourceComposite
import OAI.ThreeFlat.Diagonal.TraceNodePublishRun

namespace OAI
/-! # A single native procedure publishes charged roots and registers their input fibers -/
namespace Hierarchy.TraceAdmission.Resources
open ThreeFlat Diagonal PhysicalStage NavigationDirectory NavigationPass
open RAM RAM.NavigationNodeRows RAM.PhysicalProcedure Computability.VPVNP.BurstRAM TraceNodeHeaders NodePublication
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {d l W : ℕ} {A : State d l}

/-- The leading pointer followed by the thirteen public compaction fields. -/
def nodeWords (ctrl : ℕ) (a : NodeArchive) (n dir : ℕ) (s : Layer) : List ℕ :=
  (ctrl+1)::List.ofFn (fun j : Fin 13=>scanFields a.banks n dir a.headerBase s j.val)

private theorem stage44 {f : ℕ→ℕ} (K : ℕ) (pre : List Stage) (op : Stage) (tail : List Stage)
    (c : Cursor) (tape : MountedAt f K (pre++op::tail) c) :
    f ((finish K pre c).header+44)=(allocate K (finish K pre c) op).words 44 := by
  induction pre generalizing c with
  | nil => exact tape.1 44 (by decide) (by decide)
  | cons x xs ih => exact ih _ tape.2

private theorem seed_head (K : ℕ) (ops : List Stage) (c : Cursor) (s : Layer) :
    ∀ h : 0<(nodeLayers K ops c s).length,((nodeLayers K ops c s).get ⟨0,h⟩).actual=s := by
  cases ops <;> exact fun _=>rfl

private theorem compactWords_fit {nodeCtrl K budget : ℕ} (a : NodeArchive) (ops : List Stage)
    (c : Cursor) (s : Layer) {rs : List Layers} (eqn : rs=nodeLayers K ops c s)
    (scan : ScanRoom W nodeCtrl (nodeCtrl+1) c.header a.headerBase ops.length)
    (room : RunBounds W a rs budget) (tape : TapeBounds W a rs) (j : Fin 13) :
    scanFields a.banks ops.length c.header a.headerBase s j.val<2^W := by
  have pos : 0<rs.length := by rw [eqn,nodeLayers_length];omega
  let origin : Fin rs.length := ⟨0,pos⟩
  have actual : (rs.get origin).actual=s := by subst rs;exact seed_head ..
  have cols (k : Fin 14) := tape.fields origin k
  change ∀ k : Fin 14,NavigationNodeRows.header a.banks (rs.get origin).actual (rs.get origin).parent
    (hdr a (origin.val+1)) k.val<2^W at cols
  rw [actual] at cols
  have bottom:=scan.sourceFits
  have high:=scan.targetFits
  have ch:=cols 0
  have no:=cols 2
  have nsites:=cols 1
  change a.banks.charges+2*s.first<2^W at ch
  change a.banks.nodes+8*s.first<2^W at no
  change 2*s.count<2^W at nsites
  fin_cases j
  · change a.headerBase < 2^W
    omega
  · change 16*(ops.length+1) < 2^W
    omega
  · change c.header < 2^W
    omega
  · change ops.length < 2^W
    omega
  · change a.banks.charges < 2^W
    omega
  · change a.banks.nodes < 2^W
    omega
  · exact cols 5
  · change s.count < 2^W
    omega
  · exact cols 6
  · exact cols 7
  · exact cols 8
  · exact cols 9
  · exact cols 10

/-- The padding check publishes only the terminal wire prefix sums. The recovered
selected rows and the native descriptor directory survive that physical write. -/
theorem after_terminal_guard {K S T H : ℕ} (x : TerminalWireArchive.Layout) (ops : List Stage)
    (c : Cursor) (old last : Layer) (xs : List NodeRow) (m : Memory W)
    (journal : TraceRecovery.stagePost K ops c old (·<x.prefixBase) (natural m) S T (fun _=>False) xs last)
    (published : MountedAt (natural m) K ops c) (past : c.header+64*ops.length≤x.prefixBase)
    (top : x.prefixBase≤H) :
    let after:=TerminalWireArchive.image x m
    TraceRecovery.stagePost K ops c old (·<H) (natural after) S T (fun _=>False) xs last ∧
    MountedAt (natural after) K ops c := by
  intro after
  have before (z : ℕ) (lt : z<x.prefixBase) : after z=m z := by
    simp [after,TerminalWireArchive.image,fillSegment,Nat.not_le_of_lt lt]
  exact ⟨journal.transfer (fun z hz=>congrArg Fin.val (before _ hz)) (fun z hz=>hz.trans_le top),
    published.congr ops c (fun z _ lt=>congrArg Fin.val (before z (lt.trans_le past)))⟩

def registerNodes (W nodeCtrl H dp dir stages dst : ℕ) (a : NodeArchive) (s : Layer) (p : Parameters ℕ) :
    Procedure W :=
  (mount W nodeCtrl (nodeWords nodeCtrl a stages dir s)).seq
    ((compactPublish W nodeCtrl a (stages+1)).seq (register W H dp dir stages dst p))

/-- All authenticated charge/row assumptions of the registration phase come from the
actual first native pass. Both programs take only public addresses and stage counts. -/
theorem registerNodes_selected (r : Run F A) (h : r.plan.History) (C : r.Charges)
    (O : A.ArchiveSites) (path : r.ArchivePath h C O) (data : LayerData O.layer)
    (num : r.FinalNumbered h C O path) (a : NodeArchive) (start pay : A.Site→ℕ)
    (K nodeCtrl budget lo H dp dst S T : ℕ) (ops : List Stage) (c : Cursor)
    (m : Memory W) (p : Parameters ℕ) (count : Fintype.card (r.plan.finish h).Site=p.roots)
    (pin : Fin p.lanes→A.Site) (seed : ∀j,(O.ord (pin j)).val=j.val)
    (seen : TraceRecovery.stagePost K ops c O.layer (·<H) (natural m) S T (fun _=>False)
      (r.archiveList h C O path data) (r.finalArchive h C O path).1)
    (sroom : ScanRoom W nodeCtrl (nodeCtrl+1) c.header a.headerBase ops.length)
    (ctl : H≤nodeCtrl)
    (mountedDirectory : MountedAt (natural m) K ops c) (live : ∀ op∈ops,0<successors op)
    (banks : BankInterval a (records (r.archiveList h C O path data)) lo dp)
    (address : lo≤2^W) (halves : S≤a.halfCap) (motifs : T≤a.motifCap)
    (arity : O.layer.childCount=0) (seeds : State.SeedRows O data a.banks start pay)
    (fit : r.ArchiveFits W a.banks.unitWork h C start pay)
    (room : RunBounds W a (records (r.archiveList h C O path data)) budget)
    (tape : TapeBounds W a (records (r.archiveList h C O path data)))
    (pRoom : Parents.Layout W H (H+1) dp p.lanes ops.length (c.header+44))
    (lRoom : TraceIntervalScanner.Layout W (dp+ops.length*p.lanes) p.heads p.links p.lanes p.roots)
    (rRoom : Room W (H+5) (H+6) p)
    (headers : H+22≤lo) (prior : c.header+64*ops.length≤H)
    (chargeBase : p.charges=a.banks.charges) (firstNumber : p.firstFinal=(TraceRecovery.lastLayer K ops c O.layer).first)
    (chargeEnd : p.charges+2*(p.firstFinal+p.roots)≤dp)
    (target : dst+resourceLength p≤dp)
    (cap : p.cap≤p.lanes*(2*p.pairSpan)) (bands : p.directions*p.band≤p.lanes*p.pairSpan) :
    let idx:=indexEquiv r h count
    let dest:=fun j=>idx (r.plan.destination h (pin j))
    let work:=fun v=>a.banks.unitWork*r.chargeAt h C start (idx.symm v)
    (registerNodes W nodeCtrl H dp c.header ops.length dst a O.layer p).Spec (·=m)
      (fun _ out=>Registered (dp+ops.length*p.lanes) dst p dest work out ∧
        (∀ z, z<H → (z<dst ∨ dst+resourceLength p≤z) → out z=m z) ∧
        ∃ archiveMem : Memory W,
          archiveMem=state a (program (r.archiveList h C O path data))
            (mounted nodeCtrl (nodeWords nodeCtrl a ops.length c.header O.layer) m) (ops.length+1) ∧
          O.Charged a.banks (natural archiveMem) start pay ∧ r.ArchiveRowsStored a.banks (natural archiveMem) h C O path ∧
          ∀ z, p.charges≤z → z<dp → (z<dst ∨ dst+resourceLength p≤z) → out z=archiveMem z)
      (43+(compactTicks nodeCtrl (ops.length+1) budget+registrationTicks H (H+5) ops.length p)) := by
  intro idx dest work
  let rows:=records (r.archiveList h C O path data)
  have size : rows.length=ops.length+1 := by
    change (TraceRecovery.records (r.archiveList h C O path data)).length = ops.length+1
    rw [seen.1,nodeLayers_length]
  let fields:=nodeWords nodeCtrl a ops.length c.header O.layer
  let m₀:=mounted nodeCtrl fields m
  have fitHeader : nodeCtrl+fields.length≤2^W := by
    have hh:=sroom.head;have top:=sroom.targetFits
    simp only [fields,nodeWords,List.length_cons,List.length_ofFn];omega
  have preNode (z : ℕ) (hz : z<H) : m₀ z=m z := mounted_frame _ _ _ fitHeader (.inl (by omega))
  have fieldFit (j : Fin 13) := compactWords_fit a ops c O.layer seen.1 sroom room tape j
  have pointer : (m₀ nodeCtrl).val=nodeCtrl+1 := by
    have head:=mounted_at nodeCtrl fields m (⟨0,by simp [fields,nodeWords]⟩ : Fin fields.length) fitHeader
    have ht : nodeCtrl+1<2^W := by have:=sroom.head;have:=sroom.targetFits;omega
    have head' : m₀ nodeCtrl=((nodeCtrl+1:ℕ):Word W) := head
    rw [head',Fin.val_cast_of_lt ht]
  have params (j : ℕ) (hj : j<13) :
      (m₀ (nodeCtrl+1+j)).val=scanFields a.banks ops.length c.header a.headerBase O.layer j := by
    let slot : Fin fields.length :=
      ⟨j+1,by simp only [fields,nodeWords,List.length_cons,List.length_ofFn];omega⟩
    have word : fields[slot.val] = scanFields a.banks ops.length c.header a.headerBase O.layer j := by
      simp only [fields,nodeWords,slot,List.getElem_cons_succ,List.getElem_ofFn]
    have site : nodeCtrl+1+j = nodeCtrl+slot.val := by change _=nodeCtrl+(j+1);omega
    have cell' : m₀ (nodeCtrl+1+j)=(scanFields a.banks ops.length c.header a.headerBase O.layer j : Word W) := by
      rw [site,←word]
      exact mounted_at nodeCtrl fields m slot fitHeader
    rw [cell',Fin.val_cast_of_lt (fieldFit ⟨j,hj⟩)]
  have newDir:=mountedDirectory.congr ops c (new:=natural m₀)
    (fun x _ high=>congrArg Fin.val (preNode _ (high.trans_le prior)))
  have wide:=seen.transfer (protected':=(·<lo)) (mem':=natural m₀)
    (fun z hz=>congrArg Fin.val (preNode _ hz)) (fun _ hz=>by omega)
  let xs := r.archiveList h C O path data
  have node : (compactPublish W nodeCtrl a rows.length).Spec (·=m₀) (fun _ out =>
      out=state a (program xs) m₀ rows.length ∧
      (∀ z, z<lo ∨ dp≤z → out z=m₀ z) ∧
      O.Charged a.banks (natural out) start pay ∧ r.ArchiveRowsStored a.banks (natural out) h C O path ∧
      ∀ v : (r.plan.finish h).Site,
        let terminal:=r.finalArchive h C O path
        let id:=terminal.1.first+(terminal.2 ((r.finalSite h).symm v)).val
        (out (a.banks.charges+2*id)).val=a.banks.unitWork*r.chargeAt h C start v)
      (compactTicks nodeCtrl rows.length budget) :=
    NodePublication.publish_selected (K:=K) (ctrl:=nodeCtrl) (head:=nodeCtrl+1) (lo:=lo) (hi:=dp)
      (H:=S) (M:=T) r h C O path data a m₀ ops c (r.finalArchive h C O path).1
      sroom pointer params newDir live wide banks address halves motifs arity room tape start pay seeds fit
  rw [size] at node
  let snapshot:=state a (program (r.archiveList h C O path data)) m₀ (ops.length+1)
  let ready (changed : Memory W) := changed=snapshot ∧ (∀ z, z<H → changed z=m z) ∧
    O.Charged a.banks (natural changed) start pay ∧ r.ArchiveRowsStored a.banks (natural changed) h C O path
  have reached : (compactPublish W nodeCtrl a (ops.length+1)).Spec (·=m₀)
      (fun _ out=>ready out) (compactTicks nodeCtrl (ops.length+1) budget) := by
    intro labels regs slots M
    exact Procedure.Spec.mono (A := compactPublish W nodeCtrl a (ops.length+1))
      node (fun _ x => x) (fun _ _ x =>
        ⟨x.1,fun z hz=>(x.2.1 z (.inl (by omega))).trans (preNode z hz),x.2.2.1,x.2.2.2.1⟩)
      le_rfl M
  let post (out : Memory W) := Registered (dp+ops.length*p.lanes) dst p dest work out ∧
    (∀ z, z<H → (z<dst ∨ dst+resourceLength p≤z) → out z=m z) ∧
    ∃ old : Memory W, old=snapshot ∧ O.Charged a.banks (natural old) start pay ∧
      r.ArchiveRowsStored a.banks (natural old) h C O path ∧
      ∀ z, p.charges≤z → z<dp → (z<dst ∨ dst+resourceLength p≤z) → out z=old z
  have next : (register W H dp c.header ops.length dst p).Spec ready (fun _ out=>post out)
      (registrationTicks H (H+5) ops.length p) := by
    intro P R B M pc reg pub exit installed given cfg changed entry readyNow
    obtain ⟨snap,previous,charged,stored⟩:=readyNow
    have selected := seen.transfer (protected':=(·<H)) (mem':=fun z=>(changed z).val)
      (fun z hz=>congrArg Fin.val (previous z hz)) (fun _ z=>z)
    have phys (pre : List Stage) (op : Stage) (tail : List Stage) (eqn : ops=pre++op::tail) :
        (changed (c.header+(64*pre.length+44))).val=(allocate K (finish K pre c) op).words 44 := by
      have len:=congrArg List.length eqn
      simp only [List.length_append,List.length_cons] at len
      rw [previous _ (by omega)]
      have hf:=stage44 K pre op tail c (eqn ▸ mountedDirectory)
      simpa only [natural,header_finish,Nat.add_assoc] using hf
    have above : H+22≤p.charges := by rw [chargeBase];exact headers.trans banks.charges
    have second : (register W H dp c.header ops.length dst p).Spec _ _ _ := register_selected r h C O path data num a.banks start pay K H dp dst S T ops c
      changed p count pin seed stored charged selected phys pRoom lRoom rRoom (by omega) prior chargeBase
      (firstNumber.trans (congrArg Layer.first seen.2.1).symm) above chargeEnd target cap bands
    exact Procedure.Spec.mono (A := register W H dp c.header ops.length dst p) second
      (fun _ (e : _ = changed) => e) (fun _ out data =>
        (show post out from ⟨data.1,fun z hz outside=>(data.2.1 z hz outside).trans (previous z hz),
          changed,snap,charged,stored,data.2.2⟩))
      le_rfl M pc reg pub exit installed given cfg changed entry rfl
  have loaded : (mount W nodeCtrl fields).Spec (·=m) (fun _ out=>out=m₀) (3*fields.length+1) :=
    Procedure.Spec.atMemory (mount_spec (W:=W) nodeCtrl fields) m trivial
  intro labels regs slots
  refine Procedure.Spec.mono (A:=registerNodes W nodeCtrl H dp c.header ops.length dst a O.layer p)
    (Procedure.Spec.seq (A:=mount W nodeCtrl fields)
      (B:=(compactPublish W nodeCtrl a (ops.length+1)).seq (register W H dp c.header ops.length dst p))
      loaded (Procedure.Spec.seq (A:=compactPublish W nodeCtrl a (ops.length+1))
        (B:=register W H dp c.header ops.length dst p) reached next (fun _ _ x=>x)) (fun _ _ e=>e))
    (fun _ e=>e) ?_ (by simp only [fields,nodeWords,List.length_cons,List.length_ofFn];omega)
  rintro _ out ⟨_,_,_,_,registered⟩
  exact registered

end Hierarchy.TraceAdmission.Resources

end OAI
