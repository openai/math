import OAI.Hierarchy.DescentResetStemKey
import OAI.Hierarchy.DescentResetStemKeyRAM
import OAI.Hierarchy.DescentFallbackPacket
import OAI.Hierarchy.DescentPackedPorts

namespace OAI
/-! # Reset keys from authentic local shape, original signed slot and physical peer receiver columns -/
namespace Hierarchy.DescentResetStemKey
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentFallbackPeriod
open DescentSharedCableNames.Stage
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {D cap L field t n r H G M w : ℕ}

/-- The peer address is looked up in the previous host's physically mounted directory.
All operands use the fixed stage and original low/slot ordinal. -/
def readers (ports : Ports D) (bank : Projected.Column L cap→Bank) (H : ℕ)
    (lo : Fin L) (slot : Fin (2*cap)) : Fin (D+2)→Expr :=
  fields (.lookup (bank (.inl (0,lo))) .row) (.lookup (bank (.inr (slot,lo))) .row)
    (fun j=>peerExpr ports (bank (.inl (1,lo))) H j)

theorem readers_work (ports : Ports D) (bank : Projected.Column L cap→Bank) (H : ℕ)
    (lo : Fin L) (slot : Fin (2*cap)) (i : Fin (D+2)) :
    (readers ports bank H lo slot i).work≤45 := by
  refine Fin.cases ?_ (fun j=>Fin.cases ?_ (fun k=>?_) j) i
  · change 7≤45
    decide
  · change 7≤45
    decide
  · change (peerExpr ports (bank (.inl (1,lo))) H k).work≤45
    simp [peerExpr,neighborID,Expr.work]

theorem readers_fit (ports : Ports D) (bank : Projected.Column L cap→Bank) (base : ℕ)
    (banks : ∀a,(bank a).Fits w base)
    (peer : ∀lo,Accessible ports (bank (.inl (1,lo))) H G M w base)
    (lo : Fin L) (slot : Fin (2*cap)) (i : Fin (D+2)) :
    (readers ports bank H lo slot i).Fits w base := by
  refine Fin.cases ?_ (fun j=>Fin.cases ?_ (fun k=>?_) j) i
  · exact ⟨banks _,trivial⟩
  · exact ⟨banks _,trivial⟩
  · exact peer_fits ports _ base (peer lo) k

theorem operand_sources (ports : Ports D) (bank : Projected.Column L cap→Bank) (base : ℕ)
    (values : Fin H→Fin G→Fin L→Cell t)
    (roster : Fin H→Fin D→Option (Fin H)) (chips : Fin H→Fin G→Fin L→Fin (2*cap)→Option (Live D cap))
    (rank : Fin H→Fin (DescentSharedBookScan.width r (2^n) D)→ℕ) (m : Memory w)
    (banks : ∀a,(bank a).Fits w base) (span : ∀a,H*chunks G M≤(bank a).size)
    (peer : ∀lo,Accessible ports (bank (.inl (1,lo))) H G M w base)
    (neighbors : Mounted ports roster m G M)
    (old : ∀lo,Reads (bank (.inl (0,lo))) (fun v g=>((values v g lo).val:Cell field)) M m)
    (tag : ∀lo,Reads (bank (.inl (1,lo))) (fun v g=>((values v g lo).val+1:Cell field)) M m)
    (signed : ∀slot lo,Reads (bank (.inr (slot,lo)))
      (fun v g=>((DescentSignedCableCodec.encode (chips v g lo slot)).val:Cell field)) M m)
    (lo : Fin L) (slot : Fin (2*cap)) :
    let live:=fun v g=>inputs (field:=field) (fun h j i=>(values h j i).val) roster chips rank v g
    ∀i,Source (readers ports bank H lo slot i) (fun v g=>panel (live v g) lo slot i) M m := by
  let live:=fun v g=>inputs (field:=field) (fun h j i=>(values h j i).val) roster chips rank v g
  change ∀i,Source (readers ports bank H lo slot i) (fun v g=>panel (live v g) lo slot i) M m
  intro i
  refine Fin.cases ?_ (fun j=>Fin.cases ?_ (fun k=>?_) j) i
  · exact source_column _ base (banks _) m _ (span _) (old lo)
  · exact source_column _ base (banks _) m _ (span _) (signed slot lo)
  · have remoteRead:=peerSource ports (bank (.inl (1,lo))) base (peer lo) roster m neighbors
        (fun h g=>((values h g lo).val+1:Cell field)) (tag lo) k
    have same (h : Fin H) (g : Fin G) :
        (roster h k).elim (0:Cell field) (fun a=>((values a g lo).val+1:Cell field)) =
          panel (live h g) lo slot k.succ.succ := by
      cases choice : roster h k <;> simp [panel,fields,live,inputs,choice]
    simpa only [readers,fields,Fin.cases_succ,same] using remoteRead

theorem window_source (ports : Ports D) (bank : Projected.Column L cap→Bank) (base : ℕ)
    (values : Fin H→Fin G→Fin L→Cell t)
    (roster : Fin H→Fin D→Option (Fin H)) (chips : Fin H→Fin G→Fin L→Fin (2*cap)→Option (Live D cap))
    (rank : Fin H→Fin (DescentSharedBookScan.width r (2^n) D)→ℕ) (m : Memory w)
    (banks : ∀a,(bank a).Fits w base) (span : ∀a,H*chunks G M≤(bank a).size)
    (peer : ∀lo,Accessible ports (bank (.inl (1,lo))) H G M w base)
    (neighbors : Mounted ports roster m G M)
    (old : ∀lo,Reads (bank (.inl (0,lo))) (fun v g=>((values v g lo).val:Cell field)) M m)
    (tag : ∀lo,Reads (bank (.inl (1,lo))) (fun v g=>((values v g lo).val+1:Cell field)) M m)
    (signed : ∀slot lo,Reads (bank (.inr (slot,lo)))
      (fun v g=>((DescentSignedCableCodec.encode (chips v g lo slot)).val:Cell field)) M m)
    (space : base+words D field M<2^w)
    (s : Bool) (lo : Fin L) (slot : Fin (2*cap)) :
    let x:=readers ports bank H lo slot
    let live:=fun v g=>inputs (field:=field) (fun h j i=>(values h j i).val) roster chips rank v g
    let mid:=memory (parse D cap field) M base m
    (expr (parse D cap field) M base s x).Fits w (base+words D field M) ∧
      Source (expr (parse D cap field) M base s x)
        (fun v g=>word (parse D cap field) s (panel (live v g) lo slot)) M mid := by
  let live :=fun v g=>inputs (field:=field) (fun h j i=>(values h j i).val) roster chips rank v g
  apply issued (parse D cap field) (parse_zero D cap field) s base _ m
    (fun v g=>panel (live v g) lo slot) (readers_fit ports bank base banks peer lo slot) _ space
  exact operand_sources ports bank base values roster chips rank m banks span peer neighbors old tag signed lo slot

end
end Hierarchy.DescentResetStemKey

end OAI
