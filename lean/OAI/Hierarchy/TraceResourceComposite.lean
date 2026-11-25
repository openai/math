import OAI.Hierarchy.TraceRegisteredRows
import OAI.Hierarchy.TraceResourceRegistration
import OAI.Hierarchy.TraceResourceHeaders
import OAI.Hierarchy.TraceResourceClock

namespace OAI
/-! # Registering the selected archive with all original input and direction counts -/
namespace Hierarchy.TraceAdmission.Resources
open ThreeFlat Diagonal PhysicalStage NavigationPass NavigationDirectory
open RAM RAM.NavigationNodeRows RAM.PhysicalProcedure Computability.VPVNP.BurstRAM
open TraceReceiverArchive
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {W d l : ℕ} {A : State d l}

def register (W H dp dir stages dst : ℕ) (p : Parameters ℕ) : Procedure W :=
  (mount W H (headerWords H dp dir stages p)).seq
    (registration W H (H+5) dp stages dst p)

private theorem public_at_low {ctrl head : ℕ} (dst : ℕ) (p : Parameters ℕ) (r : Room W ctrl head p)
    (m : Memory W) {a : ℕ} (low : a<p.scratch) (away : a<dst ∨ dst+resourceLength p≤a) :
    publicRows dst p m a=m a := by
  rw [public_frame _ _ _ _ away]
  have res : a<p.resources := by have:=r.scratch;omega
  simp [completed,intermediate,fillSegment,Nat.not_le_of_lt res,Nat.not_le_of_lt low]

/-- Every common ROM word for the two mounts is represented exactly. -/
theorem headerWords_fit (H dp dir n : ℕ) (p : Parameters ℕ)
    (r : Room W (H+5) (H+6) p) (parents : Parents.Layout W H (H+1) dp p.lanes n (dir+44))
    (space : H+22≤dp) (v : ℕ) (hv : v∈headerWords H dp dir n p) : v<2^W := by
  have pw:=parents.room
  have src:=parents.tables
  have sc:=r.scratch
  have last:=r.space
  have heads:=r.heads
  have links:=r.links
  have charges:=r.costs
  have columns:=r.dimensions
  have bits:=r.bits
  have bands:=r.bands
  have cap:=r.cap
  have roots : p.roots≤p.roots*(p.directions+2) := Nat.le_mul_of_pos_right _ (by omega)
  have lanes : p.lanes≤(n+1)*p.lanes := Nat.le_mul_of_pos_left _ (by omega)
  have band : p.band≤(p.directions+1)*p.band := Nat.le_mul_of_pos_left _ (by omega)
  have span : p.pairSpan≤(p.lanes+1)*p.pairSpan := Nat.le_mul_of_pos_left _ (by omega)
  simp only [headerWords,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> omega

/-- Starting at the genuine published charge state, install both public scanner headers,
follow every actual archived owner, count the original fiber and export all resource rows. -/
theorem register_selected (r : Run F A) (h : r.plan.History) (C : r.Charges)
    (O : A.ArchiveSites) (path : r.ArchivePath h C O) (data : LayerData O.layer)
    (num : r.FinalNumbered h C O path) (bank : Banks) (start pay : A.Site→ℕ)
    (K H dp dst S T : ℕ) (ops : List Stage) (c : Cursor) (m : Memory W)
    (p : Parameters ℕ) (count : Fintype.card (r.plan.finish h).Site=p.roots)
    (pin : Fin p.lanes→A.Site) (seed : ∀j,(O.ord (pin j)).val=j.val)
    (stores : r.ArchiveRowsStored bank (fun a=>(m a).val) h C O path)
    (funds : O.Charged bank (fun a=>(m a).val) start pay)
    (seen : TraceRecovery.stagePost K ops c O.layer (·<H) (fun a=>(m a).val) S T (fun _=>False)
      (r.archiveList h C O path data) (r.finalArchive h C O path).1)
    (physical : ∀ pre op post,ops=pre++op::post →
      (m (c.header+(64*pre.length+44))).val=(allocate K (finish K pre c) op).words 44)
    (pRoom : Parents.Layout W H (H+1) dp p.lanes ops.length (c.header+44))
    (lRoom : TraceIntervalScanner.Layout W (dp+ops.length*p.lanes) p.heads p.links p.lanes p.roots)
    (rRoom : Room W (H+5) (H+6) p)
    (headers : H+22≤dp) (prior : c.header+64*ops.length≤H)
    (chargeBase : p.charges=bank.charges) (firstNumber : p.firstFinal=(r.finalArchive h C O path).1.first)
    (above : H+22≤p.charges) (chargeEnd : p.charges+2*(p.firstFinal+p.roots)≤dp)
    (target : dst+resourceLength p≤dp)
    (cap : p.cap≤p.lanes*(2*p.pairSpan)) (bands : p.directions*p.band≤p.lanes*p.pairSpan) :
    let idx:=indexEquiv r h count
    let dest:=fun j=>idx (r.plan.destination h (pin j))
    let work:=fun v=>bank.unitWork*r.chargeAt h C start (idx.symm v)
    (register W H dp c.header ops.length dst p).Spec (·=m)
      (fun _ out=>Registered (dp+ops.length*p.lanes) dst p dest work out ∧
        (∀ a, a<H → (a<dst ∨ dst+resourceLength p≤a) → out a=m a) ∧
        ∀ a, p.charges≤a → a<dp → (a<dst ∨ dst+resourceLength p≤a) → out a=m a)
      (registrationTicks H (H+5) ops.length p) := by
  intro idx dest work
  let xs:=headerWords H dp c.header ops.length p
  let m₁:=mounted H xs m
  have space : H+xs.length≤2^W := by have:=pRoom.room;change H+22≤2^W;omega
  have pre (a : ℕ) (lo : a<H) : m₁ a=m a := mounted_frame _ _ _ space (.inl lo)
  have hi (a : ℕ) (ha : p.charges≤a) : m₁ a=m a :=
    mounted_frame _ _ _ space (.inr (by change H+22≤a;omega))
  obtain ⟨pointer,base,sizes,dir,lanes,header⟩:=header_ready H dp c.header ops.length p m space
    (headerWords_fit H dp c.header ops.length p rRoom pRoom headers)
  have traced := seen.transfer (protected':=(·<dp)) (mem':=fun a=>(m₁ a).val)
    (fun i lo=>congrArg Fin.val (pre i lo)) (fun i lo=>by omega)
  have actual (preops : List Stage) (op : Stage) (post : List Stage) (eqn : ops=preops++op::post) :
      (m₁ (c.header+(64*preops.length+44))).val=(allocate K (finish K preops c) op).words 44 := by
    have len:=congrArg List.length eqn
    simp only [List.length_append,List.length_cons] at len
    rw [pre _ (by omega),physical preops op post eqn]
  have first : (mount W H xs).Spec _ _ _ := header_spec (W:=W) H dp c.header ops.length p
  have target' : dst≤p.resources := by have:=pRoom.room;have:=lRoom.beforeHeads;have:=rRoom.heads;have:=rRoom.scratch;omega
  have second : (registration W H (H+5) dp ops.length dst p).Spec _ _ _ := register_recovered r h C O path data K dp c.header S T ops c m₁ (fun _=>False)
    num traced actual p pin seed count H (H+1) (H+5) (H+6) dst pRoom lRoom rRoom header
    (by omega) (by omega) target' pointer base (by simpa only [Nat.add_assoc] using sizes)
    (by simpa only [Nat.add_assoc] using dir) (by simpa only [Nat.add_assoc] using lanes)
  have mountedAt : (mount W H xs).Spec (·=m) (fun _ out => out=m₁) 67 :=
    Procedure.Spec.atMemory first m trivial
  intro labels regs slots
  refine Procedure.Spec.mono (A := register W H dp c.header ops.length dst p)
    (Procedure.Spec.seq (A := mount W H xs) (B := registration W H (H+5) dp ops.length dst p)
      mountedAt second (fun _ _ eqn => eqn)) (fun _ e => e) ?_ le_rfl
  intro _ out ⟨_,rfl,linked,loaded,lists,done⟩
  let bs:=ownerBases r h C O path
  let f:=fillSegment dp ((bs.length+1)*p.lanes)
    (Parents.file dp p.lanes (Parents.walkPrefix (fun a=>(m₁ a).val) bs)) m₁
  have lowFirst (a : ℕ) (lt : a<dp) : f a=m₁ a := by simp [f,fillSegment,Nat.not_le_of_lt lt]
  have index_eq (v : (r.plan.finish h).Site) :
      idx v = Fin.cast count (r.terminalOrderEquiv h v) := by
    apply Fin.ext
    rfl
  have dest_eq : dest = fun j => Fin.cast count (r.terminalOrderEquiv h (r.plan.destination h (pin j))) :=
    funext fun j => index_eq (r.plan.destination h (pin j))
  have bound (v : (r.plan.finish h).Site) :
      (out (dst+(idx v).val*(p.directions+2))).val = bank.unitWork*r.chargeAt h C start v ∧
      out (dst+(idx v).val*(p.directions+2)+1) = (inputCount dest (idx v) p.cap p.pairSpan : Word W) ∧
      ∀ i : Fin p.directions, out (dst+(idx v).val*(p.directions+2)+(2+i.val)) =
        (directionCount dest (idx v) p.band p.pairSpan i.val : Word W) := by
    rw [dest_eq, index_eq]
    exact registered_resource_rows r h C O path num p bank chargeBase firstNumber count pin
      start pay m f linked out (H+5) (H+6) dp dst rRoom stores funds chargeEnd
      (by have:=lRoom.beforeHeads;omega) (by have:=lRoom.beforeHeads;have:=lRoom.beforeLinks;omega)
      (fun a lower upper=>(lowFirst a upper).trans (hi a lower)) lists done v
  have read (a : ℕ) (lt : a<p.heads) (outside : a<dst ∨ dst+resourceLength p≤a) : out a=f a := by
    rw [done,public_at_low dst p rRoom linked (by have:=rRoom.heads;omega) outside]
    exact lists.1 _ (.inl lt) (.inl (by have:=lRoom.beforeLinks;omega))
  constructor
  · constructor
    · intro j
      have hj:=j.isLt
      rw [read _ (by have:=lRoom.beforeHeads;omega) (.inr (by omega))]
      exact loaded j
    · intro v
      obtain ⟨u,rfl⟩:=idx.surjective v
      simpa only [work,Equiv.symm_apply_apply] using (bound u).1
    · intro v
      obtain ⟨u,rfl⟩:=idx.surjective v
      have cell : inputCount dest (idx u) p.cap p.pairSpan≤p.cap := by
        conv_rhs => rw [←total_inputCount dest p.cap p.pairSpan cap]
        exact Finset.single_le_sum (s := Finset.univ) (f := fun v => inputCount dest v p.cap p.pairSpan)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ (idx u))
      rw [(bound u).2.1,Fin.val_cast_of_lt (cell.trans_lt rRoom.cap)]
    · intro v i
      obtain ⟨u,rfl⟩:=idx.surjective v
      have cover := (Nat.mul_le_mul_right p.band (Nat.succ_le_of_lt i.isLt)).trans bands
      have cell : directionCount dest (idx u) p.band p.pairSpan i.val≤p.band := by
        conv_rhs => rw [←total_directionCount dest p.band p.pairSpan i.val cover]
        exact Finset.single_le_sum (s := Finset.univ)
          (f := fun v => directionCount dest v p.band p.pairSpan i.val)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ (idx u))
      have incl : p.band≤(p.directions+1)*p.band := Nat.le_mul_of_pos_left _ (by omega)
      rw [(bound u).2.2 i,Fin.val_cast_of_lt (cell.trans_lt (incl.trans_lt rRoom.bands))]
  · constructor
    · intro a la away
      exact (read a (by have:=lRoom.beforeHeads;omega) away).trans ((lowFirst _ (by omega)).trans (pre _ la))
    · intro a lower upper away
      exact (read a (by have:=lRoom.beforeHeads;omega) away).trans ((lowFirst _ upper).trans (hi a lower))

end Hierarchy.TraceAdmission.Resources

end OAI
