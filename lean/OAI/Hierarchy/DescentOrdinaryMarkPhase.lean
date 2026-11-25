import OAI.Hierarchy.DescentOrdinaryMarkProject

namespace OAI
/-! # One shared paid mark scan and regrouping for all ordinary parent candidates -/
namespace Hierarchy.DescentOrdinaryMarkProject
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentSharedCableNames
open DescentPacking.PackedMatch.Local
open DescentOrdinarySignedMeta
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {P O N H G X D cap M A w : ℕ}
local notation "GatherROM" => DescentOrdinaryAtomFieldRAM.ROM.mount
local notation "Projection" => DescentResetStemProjectExpr.program

def pick (ports : Ports P) (prior : Fin O→Bank) (fresh : Fin O→Bool) (base D cap N A : ℕ) (j : Fin (P*O)) : Expr :=
  let q:=finProdFinEquiv.symm j
  (MarkGather.lut base D cap A (fresh q.2)).read (peerExpr ports (prior q.2) N q.1) (.lit 0)

def region (base P O N G X D cap A M : ℕ) :=
  DescentResetStemProject.endAddress (MarkGather.stop base D cap A) (P*O) N G X 1 A M
def markExpr (base P O N H G X D cap A M : ℕ) (x : Fin X) (j : Fin (P*O)) : Expr :=
  mask (DescentResetStemProject.bank (MarkGather.stop base D cap A) (P*O) N G X 1 A M j x)
    (region base P O N G X D cap A M) N H G M
def endpoint (base P O N H G X D cap A M : ℕ) :=stop (region base P O N G X D cap A M) H G M

def program (ports : Ports P) (prior : Fin O→Bank) (fresh : Fin O→Bool) (base N H G X D cap A M pitch w : ℕ) :=
  (GatherROM (MarkGather.pages D cap A) (MarkGather.width D cap A) w base).seq
    ((Projection (MarkGather.stop base D cap A) N G X 1 A M (pick ports prior fresh base D cap N A) w).seq
      (DescentStaticWordColumn.program w (region base P O N G X D cap A M) (words N H G M pitch) (rows H G M)))

def ticks (ports : Ports P) (prior : Fin O→Bank) (fresh : Fin O→Bool) (base N H G X D cap A M : ℕ) :=
  (4+10*(4*2^MarkGather.width D cap A))+
    (DescentResetStemProjectExpr.ticks (MarkGather.stop base D cap A) N G X 1 A M (pick ports prior fresh base D cap N A)+
      (4+10*rows H G M))

def bits (R : Fin N→Fin P→Option (Fin N)) (panel : Fin O→Fin N→Fin (G*X)→Option (Stage.Live D cap))
    (fresh : Fin O→Bool) (pitch : ℕ) (x : Fin X) (j : Fin (P*O)) (h : Fin H) (g : Fin G) : Cell 1 :=
  let q:=finProdFinEquiv.symm j
  (DescentOrdinaryCompactPeer.ROM.rack N pitch h).elim 0 (fun v=>MarkGather.flag (fresh q.2)
    ((R v q.1).bind (fun donor=>panel q.2 donor (finProdFinEquiv (g,x)))))

def memory (ports : Ports P) (prior : Fin O→Bank) (fresh : Fin O→Bool) (base N H G X D cap A M pitch : ℕ) (m : Memory w) :=
  let prep:=DescentOrdinaryAtomFieldRAM.ROM.after (MarkGather.pages D cap A) (MarkGather.width D cap A) base m
  let shaped:=DescentResetStemProjectExpr.image (MarkGather.stop base D cap A) N G X 1 A M
    (pick ports prior fresh base D cap N A) prep
  DescentStaticWordColumn.image (region base P O N G X D cap A M) (words N H G M pitch) shaped (rows H G M)

theorem run_fixed (ports : Ports P) (prior : Fin O→Bank) (fresh : Fin O→Bool) (base pitch : ℕ)
    (R : Fin N→Fin P→Option (Fin N)) (panel : Fin O→Fin N→Fin (G*X)→Option (Stage.Live D cap))
    (m : Memory w) (ha : 0<A) (hm : 0<M) (hx : 0<X)
    (access : ∀o,Accessible ports (prior o) N (G*X) A w base) (routing : Mounted ports R m (G*X) A)
    (stored : ∀o,Reads (prior o) (fun v g=>DescentSignedCableCodec.encode (panel o v g)) A m)
    (narrow : rows N G M<2^w) (room : endpoint base P O N H G X D cap A M<2^w) :
    let dst:=memory ports prior fresh base N H G X D cap A M pitch m
    (program ports prior fresh base N H G X D cap A M pitch w).Exec m dst (ticks ports prior fresh base N H G X D cap A M) ∧
      (∀x j,(markExpr base P O N H G X D cap A M x j).Fits w (endpoint base P O N H G X D cap A M)) ∧
      (∀x j,Source (markExpr base P O N H G X D cap A M x j) (bits (H:=H) R panel fresh pitch x j) M dst) ∧
      ∀u,u<base ∨ endpoint base P O N H G X D cap A M≤u→dst u=m u := by
  intro dst
  let pg:=MarkGather.pages D cap A
  let aw:=MarkGather.width D cap A
  let start:=MarkGather.stop base D cap A
  let mid:=region base P O N G X D cap A M
  let roof:=endpoint base P O N H G X D cap A M
  let t₀:=DescentOrdinaryAtomFieldRAM.ROM.after pg aw base m
  let src:=pick ports prior fresh base D cap N A
  let Y : Fin (P*O) → Fin N → Fin (G*X) → Cell 1 := fun j v g=>MarkGather.flag (fresh (finProdFinEquiv.symm j).2)
    ((R v (finProdFinEquiv.symm j).1).bind (fun donor=>panel (finProdFinEquiv.symm j).2 donor g))
  have ordered : start ≤ mid := by
    change start ≤ DescentResetStemProject.endAddress start (P*O) N G X 1 A M
    rw [DescentResetStemProject.extent start (P*O) N G X 1 A M]
    exact Nat.le_add_right ..
  have post : mid≤roof :=Nat.le_add_right ..
  have sr : start<2^w :=(ordered.trans post).trans_lt room
  have first : (GatherROM pg aw w base).Exec m t₀ (4+10*(4*2^aw)) := by
    intro labels regs slots machine
    exact DescentStaticWordColumn.mount base (4*2^aw) _ m sr machine
  have source (j : Fin (P*O)) : (src j).Fits w start ∧ Source (src j) (Y j) A t₀ :=
    (MarkGather.issued_on base ports (prior (finProdFinEquiv.symm j).2) R (finProdFinEquiv.symm j).1
      (fresh (finProdFinEquiv.symm j).2) (panel (finProdFinEquiv.symm j).2) m sr
      (access _) routing (stored _)).2
  have moved:=DescentResetStemProjectExpr.run start N G X 1 A M src t₀ Y ha hm hx
    (fun j=>(source j).1) (fun j=>(source j).2) (post.trans_lt room)
  let t₁:=DescentResetStemProjectExpr.image start N G X 1 A M src t₀
  let final:=DescentStaticWordColumn.image mid (words N H G M pitch) t₁ (rows H G M)
  have span : mid+rows H G M≤roof :=
    Nat.add_le_add_left (Nat.le_pow_clog (by decide : 1<2) (rows H G M)) mid
  have emit : (DescentStaticWordColumn.program w mid (words N H G M pitch) (rows H G M)).Exec
      t₁ final (4+10*rows H G M) := by
    intro labels regs slots machine
    exact DescentStaticWordColumn.mount mid (rows H G M) (words N H G M pitch) t₁
      (span.trans_lt room) machine
  have fields (x : Fin X) (j : Fin (P*O)) :=
    projection (N:=N) (H:=H) (G:=G) (M:=M) (a:=1)
      mid pitch t₁ (DescentResetStemProject.bank start (P*O) N G X 1 A M j x)
      (moved.2.2.1 j x) narrow room (fun h g=>Y j h (finProdFinEquiv (g,x))) (moved.2.1 j x)
  refine ⟨?_,fun x j=>(fields x j).1,fun x j=>(fields x j).2,?_⟩
  · intro labels regs slots machine
    exact Procedure.Exec.then (@first) (Procedure.Exec.then moved.1 (@emit)) machine
  intro u away
  change final u = m u
  have begin_ : base≤ start := Nat.le_add_right ..
  rcases away with lt|gt
  · exact (DescentStaticWordColumn.frame mid (rows H G M) (words N H G M pitch) t₁ u (.inl (lt.trans_le (begin_.trans ordered)))).trans
      ((moved.2.2.2.1 u (.inl (lt.trans_le begin_))).trans (DescentOrdinaryAtomFieldRAM.ROM.frame pg aw base m u (.inl lt)))
  · exact (DescentStaticWordColumn.frame mid (rows H G M) (words N H G M pitch) t₁ u (.inr (span.trans gt))).trans
      ((moved.2.2.2.1 u (.inr (post.trans gt))).trans (DescentOrdinaryAtomFieldRAM.ROM.frame pg aw base m u (.inr ((ordered.trans post).trans gt))))

theorem run (ports : Ports P) (prior : Fin O→Bank) (fresh : Fin O→Bool) (base pitch : ℕ)
    (R : Fin N→Fin P→Option (Fin N)) (panel : Fin O→Fin N→Fin (G*X)→Option (Stage.Live D cap))
    (m : Memory w) (ha : 0<A) (hm : 0<M) (hx : 0<X)
    (access : ∀o,Accessible ports (prior o) N (G*X) A w base) (routing : Mounted ports R m (G*X) A)
    (stored : ∀o,Reads (prior o) (fun v g=>DescentSignedCableCodec.encode (panel o v g)) A m)
    (narrow : rows N G M<2^w) (room : endpoint base P O N H G X D cap A M<2^w) :
    ∃dst : Memory w,
      (program ports prior fresh base N H G X D cap A M pitch w).Exec m dst (ticks ports prior fresh base N H G X D cap A M) ∧
      (∀x j,(markExpr base P O N H G X D cap A M x j).Fits w (endpoint base P O N H G X D cap A M)) ∧
      (∀x j,Source (markExpr base P O N H G X D cap A M x j) (bits (H:=H) R panel fresh pitch x j) M dst) ∧
      ∀u,u<base ∨ endpoint base P O N H G X D cap A M≤u→dst u=m u :=
  ⟨memory ports prior fresh base N H G X D cap A M pitch m,
    run_fixed ports prior fresh base pitch R panel m ha hm hx access routing stored narrow room⟩

theorem work_mark (base P O N H G X D cap A M : ℕ) (x : Fin X) (j : Fin (P*O)) :
    (markExpr base P O N H G X D cap A M x j).work=22 :=rfl

end
end Hierarchy.DescentOrdinaryMarkProject

end OAI
