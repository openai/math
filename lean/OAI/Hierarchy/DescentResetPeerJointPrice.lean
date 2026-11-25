import OAI.Hierarchy.DescentResetPeerJointRAM

namespace OAI
/-! Exact linear old-degree tariff of the current four shared physical coordinates. -/
namespace Hierarchy.DescentResetPeerJointRAM
open DescentDyadicSpan DescentSixParty.Chronology DescentStaticWordColumn DescentClosedHaloChip DescentFallbackRankRAM
open ThreeFlat.RAM PhysicalProcedure
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical
noncomputable section

private theorem bound {D : ℕ} (s : Fin D→Expr) (v z sh : Expr) (old : ∀i,(s i).work≤18)
    (x : v.work≤11) (y : z.work≤39) (u : sh.work≤39) :
    (chip s v z sh).work≤170+160*D := by
  have bitCost (i : Fin D) : (bit s v z i).work≤91:=by
    have b:=old i
    simp only [bit,less,Expr.work]
    omega
  have search (l : List (Fin D)) : (existsWord s z l).work≤1+59*l.length:=by
    induction l with
    | nil=>exact le_rfl
    | cons i l ih=>
      have b:=old i
      simp only [existsWord,Expr.work,List.length_cons]
      omega
  have sumCost (l : List (Fin D)) : (foldSum (l.map (bit s v z))).work≤1+92*l.length:=by
    induction l with
    | nil=>exact le_rfl
    | cons i l ih=>
      have b:=bitCost i
      change (bit s v z i).work + (foldSum (l.map (bit s v z))).work + 1 ≤ 1+92*(l.length+1)
      omega
  have hh:=search (List.finRange D)
  have tt:=sumCost ((Finset.univ : Finset (Fin D)).toList)
  simp only [List.length_finRange] at hh
  simp only [Finset.length_toList,Finset.card_univ,Fintype.card_fin] at tt
  simp only [chip,total,less,Expr.work]
  omega

private theorem guarded_work (v P O D : ℕ) (num dst left right core : Expr)
    (hn : num.work≤6) (hd : dst.work≤34) (hl : left.work≤11) (hr : right.work≤39)
    (hc : core.work≤170+160*D) :
    (Expr.branch .lt (.lit v) num (.branch .lt dst (.lit P) (.branch .lt left (.lit O)
      (.branch .lt right (.lit O) core (.lit 0)) (.lit 0)) (.lit 0)) (.lit 0)).work ≤ 300*(D+1) := by
  simp only [Expr.work]
  omega

theorem term_work (A : Sources) (base P O D v j : ℕ) : (term A base P O D v j).work≤300*(D+1) := by
  let here:=Expr.lookup A.inverse (.lit v)
  let twice:=Expr.op .add here here
  let dst:=Expr.lookup A.current (.op .add (.op .add twice twice) (.lit j))
  let left:=Expr.lookup (table base P 0) here
  let right:=Expr.lookup (table base P 0) dst
  let sh:=Expr.lookup (table base P 1) dst
  let start:=Expr.lookup (table base P 2) here
  let src (i : Fin D) := Expr.lookup A.prior (.op .add start (.lit i.val))
  have small (i : Fin D) : (src i).work≤18 := by change 18≤18; exact le_rfl
  have hl : left.work≤11 := by change 11≤11; exact le_rfl
  have hr : right.work≤39 := by change 39≤39; exact le_rfl
  have hs : sh.work≤39 := by change 39≤39; exact le_rfl
  exact guarded_work v P O D (.lookup A.count (.lit 0)) dst left right (chip src left right sh)
    (by change 6≤6; exact le_rfl) (by change 34≤34; exact le_rfl) hl hr
    (bound src left right sh small hl hr hs)

theorem price (w base H P O width D : ℕ) (A : Sources) :
    let a:=phase w base H P O width D A
    a.ticks+names a.program ≤ 9000*(H+1)*(D+1)+150*(P+1) := by
  intro a
  let d:=deck w base P width D
  let x:=writer w base H P O D A
  have dynamic:=DescentFixedRowProgram.bill w (outputBase base P) (4*H) (row A base H P O D) (300*(D+1))
    (fun i _=>term_work A base P O D (i%H) (i/H))
  have dy : x.ticks+names x.program≤19+4*H*(19+6*(300*(D+1))):=dynamic
  have static_ : d.ticks+names d.program≤150*P+94:=by
    change (4+10*(3*span P))+names (DescentStaticWordColumn.program _ _ _ (3*span P))≤_
    rw [names_mount]
    have sp:=span_le P
    omega
  change (d.ticks+x.ticks)+names (d.program.seq x.program)≤_
  rw [names_seq]
  ring_nf at dy ⊢
  omega


end
end Hierarchy.DescentResetPeerJointRAM

end OAI
