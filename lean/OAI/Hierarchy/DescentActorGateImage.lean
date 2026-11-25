import OAI.Hierarchy.DescentResetActorCPU
import OAI.Hierarchy.DescentZipBook

namespace OAI
/-! # Mounting all public occupancy gates against physical predecessor sources -/
namespace Hierarchy.DescentActorRaster.CPU
open DescentSIMDLookup DescentPackedZip Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {Q r t a H G M w : ℕ}
def menu (r t a : ℕ) (qs : Fin Q→Query) (i : Fin Q) : Book.Gate :=
  ⟨t*2^r,a,1,gate r t a (qs i)⟩
local notation "area" => t*2^r+a

theorem installed (qs : Fin Q→Query) (st : Expr) (heads : Fin Q→Expr) (base out : ℕ) (m : Memory w)
    (words : Fin H→Fin G→Cell (t*2^r)) (header : Fin Q→Fin H→Fin G→Cell a)
    (stFit : st.Fits w base) (headFit : ∀i,(heads i).Fits w base)
    (earlier : Source st words M m) (previous : ∀i,Source (heads i) (header i) M m)
    (apart : base+Q*(2*2^(area*M))≤out) (room : out+Q*(H*chunks G M)<2^w) :
    let table:=menu r t a qs
    let boot:=Book.install table area M w base
    let tabs:=Book.tables table area M base
    let pass:=passes tabs st heads out H G M
    let state:=ProtocolRAM.result pass (Book.image table area M base m)
    (boot.seq (program w pass)).Exec m state ((4+10*(Q*(2*2^(area*M))))+clock pass) ∧
    (∀j(p:Row H G M),state (out+j.val*(H*chunks G M)+(row H G M p).val)=
      ((data (fun h g=>gate r t a (qs j) (words h g) (header j h g)) p).val:Word w)) ∧
    (∀x,x<base ∨ out+Q*(H*chunks G M)≤x→state x=m x) ∧ CheapCode (boot.seq (program w pass)) := by
  intro table boot tabs pass state
  have low:base≤out:=(Nat.le_add_right ..).trans apart
  have fit:out<2^w:=(Nat.le_add_right ..).trans_lt room
  obtain ⟨mounted,maps,frame,cheap⟩:=Book.mount table area M base m (fun _=>le_rfl) (apart.trans_lt fit)
  have access (i:Fin Q):Fits (tabs i) st (heads i) (t*2^r) a M out w:=by
    have hw:=Book.geometry table area M base i apart fit le_rfl
    exact ⟨ProtocolRAMGeneratedWrite.fits_mono _ low stFit,ProtocolRAMGeneratedWrite.fits_mono _ low (headFit i),hw.1,hw.2,rfl,rfl⟩
  have keep {d:ℕ} (expr:Expr) (f:Fin H→Fin G→Cell d) (before:expr.Fits w base) (rd:Source expr f M m) :
      Source expr f M (Book.image table area M base m):=by
    intro p
    exact (eval_below expr _ m _ before (fun z hz=>frame z (Or.inl hz))).trans (rd p)
  obtain ⟨ran,correct,both,light⟩:=run tabs st heads out (Book.image table area M base m) qs words header
    access room maps (keep _ _ stFit earlier) (fun j=>keep _ _ (headFit j) (previous j))
  exact ⟨mounted.then ran,correct,fun x hx=>(both x (by omega)).trans (frame x (by omega)),cheap_seq cheap light⟩

end
end Hierarchy.DescentActorRaster.CPU

end OAI
