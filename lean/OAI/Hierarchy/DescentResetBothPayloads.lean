import OAI.Hierarchy.DescentResetReturningTarget

namespace OAI
/-! # Both directed short fields at either actual end, on physical old-roster reads -/
namespace Hierarchy.DescentResetOppositePayload
open DescentSIMDLookup DescentPacking.PackedMatch.Local.Gather DescentPackedFallbackTree.Image
open DescentIssuedGoodHeaders DescentPackedZip DescentPackedColony DescentSharedCableNames DescentResetReciprocalPeer
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

abbrev Form (D cap : ℕ) := Fin 1 ⊕ (Slot D cap×Fin 2) ⊕ (Fin D×Fin D)
def span (D cap : ℕ) := 1+((D*(2*cap))*2+D*D)
def fieldIndex (D cap : ℕ) : Form D cap ≃ Fin (span D cap) :=
  ((Equiv.refl _).sumCongr ((((finProdFinEquiv.prodCongr (Equiv.refl _)).trans finProdFinEquiv).sumCongr finProdFinEquiv).trans finSumFinEquiv)).trans finSumFinEquiv

def project {D cap : ℕ} {T : Type} (q : T) (cable pay : Slot D cap→T) (gates : Fin D→Fin D→T) (i : Fin (span D cap)) : T :=
  match (fieldIndex D cap).symm i with
  | .inl _=>q
  | .inr (.inl (j,s))=>if s.val=0 then cable j else pay j
  | .inr (.inr (v,t))=>gates v t

def both (D cap b : ℕ) (wanted : Bool) (x : Fin (span D cap)→Cell b) : Cell b :=
  let slotAt:=fieldIndex D cap
  let q:=chip D cap (x (slotAt (.inl 0)))
  let signed:=fun j=>chip D cap (x (slotAt (.inr (.inl (j,0)))))
  let cargo:=fun j=>x (slotAt (.inr (.inl (j,1))))
  let gates:=fun v t=>decide ((x (slotAt (.inr (.inr (v,t))))).val≠0)
  if wanted then reverse gates q signed cargo else select q signed cargo

theorem both_at {D cap b : ℕ} (wanted : Bool) (q : Cell b) (cable pay : Slot D cap→Cell b) (gate : Fin D→Fin D→Cell b) :
    both D cap b wanted (project q cable pay gate)=
      if wanted then reverse (fun v t=>decide ((gate v t).val≠0)) (chip D cap q) (fun j=>chip D cap (cable j)) pay
      else select (chip D cap q) (fun j=>chip D cap (cable j)) pay:=by simp [both,project]

variable {D cap H G M w b : ℕ}
def «fields» (P : Ports D) (cable cargo : Fin (2*cap)→Bank) (H : ℕ) (query own ones : Expr) : Fin (span D cap)→Expr:=
  project query (fun j=>peerExpr P (cable j.2) H j.1) (fun j=>peerExpr P (cargo j.2) H j.1)
    (fun v t=>back P H own ones v t)

def digits (adj : Adj H D) (query : Fin H→Fin G→Cell b) (signed cargo : Fin (2*cap)→Fin H→Fin G→Cell b)
    (h : Fin H) (g : Fin G) : Fin (span D cap)→Cell b:=
  project (query h g) (fun j=>(adj h j.1).elim 0 (fun u=>signed j.2 u g)) (fun j=>(adj h j.1).elim 0 (fun u=>cargo j.2 u g))
    (fun v t=>if reaches adj h v t then 1 else 0)

theorem operands (P : Ports D) (old : Bank) (cable cargo : Fin (2*cap)→Bank) (roof : ℕ) (m : Memory w)
    (adj : Adj H D) (real : Mounted P adj m G M) (access : Accessible P old H G M w roof)
    (wide : ∀j,Accessible P (cable j) H G M w roof ∧ Accessible P (cargo j) H G M w roof)
    (query own ones : Expr) (q : Fin H→Fin G→Cell b) (signed pay : Fin (2*cap)→Fin H→Fin G→Cell b)
    (prev : ∀j,Reads (cable j) (signed j) M m ∧ Reads (cargo j) (pay j) M m)
    (qr : Source query q M m) (hr : ∀p : Row H G M,own.eval m ((row H G M p).val:Word w)=(p.1.val:Word w))
    (one : Source ones (fun (_ : Fin H) (_ : Fin G)=>(1:Cell b)) M m)
    (j : Fin (span D cap)) :
    Source («fields» P cable cargo H query own ones j) (fun h g=>digits adj q signed pay h g j) M m:=by
  obtain ⟨u,rfl⟩:=(fieldIndex D cap).surjective j
  rcases u with x|⟨⟨v,t⟩,flag⟩|⟨v,t⟩
  · simpa [«fields»,project,digits] using qr
  · fin_cases flag
    · simpa [«fields»,project,digits] using peerSource P (cable t) roof (wide t).1 adj m real (signed t) (prev t).1 v
    · simpa [«fields»,project,digits] using peerSource P (cargo t) roof (wide t).2 adj m real (pay t) (prev t).2 v
  · simpa [«fields»,project,digits] using back_source P old roof access adj m real own ones hr (fun (_ : Fin H) (_ : Fin G)=>(1:Cell b)) one v t

theorem fits_fields (P : Ports D) (old : Bank) (cable cargo : Fin (2*cap)→Bank) (roof : ℕ) (access : Accessible P old H G M w roof)
    (wide : ∀j,Accessible P (cable j) H G M w roof ∧ Accessible P (cargo j) H G M w roof) (q own ones : Expr)
    (qfits : q.Fits w roof) (o : own.Fits w roof) (c : ones.Fits w roof) (j : Fin (span D cap)) :
    («fields» P cable cargo H q own ones j).Fits w roof:=by
  obtain ⟨u,rfl⟩:=(fieldIndex D cap).surjective j
  rcases u with x|⟨⟨v,t⟩,flag⟩|⟨v,t⟩
  · simpa [«fields»,project] using qfits
  · fin_cases flag
    · simpa [«fields»,project] using peer_fits P (cable t) roof (wide t).1 v
    · simpa [«fields»,project] using peer_fits P (cargo t) roof (wide t).2 v
  · simpa [«fields»,project] using back_fits P old roof access own ones o c v t

/-- The kernel runs once for each direction and field chosen by the outer
public calendar. The guard expressions follow two real host-roster pointers. -/
theorem issued (P : Ports D) (old : Bank) (cable cargo : Fin (2*cap)→Bank) (roof : ℕ)
    (adj : Adj H D) (wanted : Bool) (query own ones : Expr) (q : Fin H→Fin G→Cell b) (signed pay : Fin (2*cap)→Fin H→Fin G→Cell b)
    (tables : Fin (span D cap)→Tables) (menu : DescentSIMDLookup.Banks) (out : Bank) (positive : 0<M) (m : Memory w)
    (real : Mounted P adj m G M) (access : Accessible P old H G M w roof)
    (wide : ∀j,Accessible P (cable j) H G M w roof ∧ Accessible P (cargo j) H G M w roof)
    (prev : ∀j,Reads (cable j) (signed j) M m ∧ Reads (cargo j) (pay j) M m)
    (qr : Source query q M m) (hr : ∀p : Row H G M,own.eval m ((row H G M p).val:Word w)=(p.1.val:Word w))
    (one : Source ones (fun (_ : Fin H) (_ : Fin G)=>(1:Cell b)) M m)
    (qfits : query.Fits w roof) (o : own.Fits w roof) (c : ones.Fits w roof)
    (statics : ∀j,Static (tables j) (setField (d:=b) j) M m)
    (safe : ∀j,(tables j).shift.Fits w roof ∧ (tables j).apply.Fits w roof ∧ (tables j).shift.bits=b*span D cap*M ∧ (tables j).apply.bits=(b*span D cap+b)*M)
    (room : roof+H*chunks G M<2^w) (fit : DescentSIMDLookup.Fits menu (b*span D cap) b M H G w out.base)
    (rom : resident (both D cap b wanted ∘ (encode b (span D cap)).symm) menu H G M m)
    (dictLow : menu.dictionary.base+2^(b*span D cap*M)≤roof) (maskLow : menu.mask.base+H*chunks G M≤roof)
    (wire : menu.source.base=roof) (ceiling : ℕ) (available : out.Fits w ceiling) (extent : H*chunks G M≤out.size) :
    let act:=assembly tables («fields» P cable cargo H query own ones)
    let N:=H*chunks G M
    let dst:=imageBank H G M out.base menu (image roof N act m)
    ((scan w roof N act).seq (DescentSIMDLookup.program menu out.base H G M w)).Exec m dst ((4+N*(2*act.work+4))+(4+44*N)) ∧
      Source (.lookup out .row) (fun h g=>both D cap b wanted (digits adj q signed pay h g)) M dst ∧
      ∀a,(a<roof∨roof+N≤a)→(a<out.base∨out.base+N≤a)→dst a=m a:=by
  have bounds : Bounds (w:=w) (d:=b) (M:=M) tables («fields» P cable cargo H query own ones) roof:=
    fun j=>⟨fits_fields P old cable cargo roof access wide query own ones qfits o c j,safe j⟩
  have sources:=operands P old cable cargo roof m adj real access wide query own ones q signed pay prev qr hr one
  obtain ⟨run,whole,_,frame⟩:=gathered_words (both D cap b wanted) tables _ menu roof out.base (digits adj q signed pay) positive m bounds statics sources room fit rom dictLow maskLow wire
  exact ⟨run,source_column out ceiling available _ _ extent whole,frame⟩

end
end Hierarchy.DescentResetOppositePayload

end OAI
