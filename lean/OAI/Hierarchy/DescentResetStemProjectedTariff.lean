import OAI.Hierarchy.DescentResetStemProjected
import OAI.Hierarchy.DescentResetStemProjectExprTariff

namespace OAI
/-! # Time and program size of the dated reset-stem issue -/
namespace Hierarchy.DescentResetStemPackedIssue.Mixed
open DescentSIMDLookup DescentPackedZip DescentStaticWordColumn DescentDyadicSpan
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable {D f Q K : ℕ}

def keyNames (D f M Q T : ℕ) := 15*(DescentResetStemKey.words D f M+1)+(15+Q*(11+4*(14+(D+2)*(T+11))))

private theorem printed_keys (parse : DescentResetStemKey.Decoder D f) (side : Fin Q→Bool)
    (src : Fin Q→Fin (D+2)→Expr) (base M H G w T : ℕ) (cost : ∀q i,(src q i).work≤T) :
    names (DescentResetStemKey.Columns.code parse side src base M H G w)≤keyNames D f M Q T := by
  rw [DescentResetStemKey.Columns.code,names_seq]
  have rom : names (DescentResetStemKey.program parse M w base)=15*(DescentResetStemKey.words D f M+1) :=
    DescentPackedZip.Book.names (DescentResetStemKey.gates parse) (DescentResetStemKey.unit D f) M w base
  rw [rom]
  apply Nat.add_le_add_left
  apply (ProbeStage.Native.columns_text _ _ _ (14+(D+2)*(T+11)) _ ?_).trans
  · simp only [DescentResetStemKey.Columns.terms,List.length_ofFn,le_refl]
  · intro e has
    obtain ⟨q,rfl⟩:=List.mem_ofFn.mp has
    exact DescentResetStemKey.expr_work parse M base (side q) (src q) T (cost q)

def codeTariff (D f b K M P H G Q T : ℕ) :=
  let n:=H*chunks G M
  keyNames D f M Q T + 15*(DescentResetStemKeyReindex.size P H G M+1) +
    (15*(DescentResetStemHeaders.romSize b n+1)+(15+(2*K)*(11+4*25)))+
    (15*(DescentResetStemMux.words K (f+2) b M+1)+(15+Q*(11+4*(1+K*(30+7+22)))))

theorem Layout.names_bound (A : Layout) (parse : DescentResetStemKey.Decoder D f)
    (side : Fin Q→Bool) (src : Fin Q→Fin (D+2)→Expr) (b K M P H G w T : ℕ) (cost : ∀q i,(src q i).work≤T) :
    names (A.code parse side src b K M P H G w)≤codeTariff D f b K M P H G Q T := by
  unfold Layout.code
  simp only [names_seq,DescentResetStemKeyReindex.names]
  apply Nat.add_le_add
  · apply Nat.add_le_add
    · exact Nat.add_le_add_right (printed_keys parse side src A.base M P G w T cost) _
    · exact DescentResetStemHeaders.names_le w (2*K) H G M b A.raw (A.hdr D f M P H G Q)
  · exact DescentResetStemIssuer.names_bound (A.mux D f b K M P H G Q)
      (A.key D f M P H G) (A.heads D f b M P H G side (K:=K))
      (f+2) b M H G w (A.out D f b K M P H G Q) 30 7 (fun _=>le_rfl) (fun _ _=>le_rfl)

namespace Projected

def bill (D f b K P H G X M₀ M Q T U : ℕ) :=
  let N:=Q*(D+2)
  let q:=X*Q
  let n:=H*chunks G M
  let prev:=P*chunks G M
  let scalar:=DescentResetStemDescriptorRAM.workLimit (6*U+7)
  let project:=4096*DescentResetStemProject.volume N P G X f M₀ M+
    (4+N*(4+P*chunks (G*X) M₀*(2*T+4)))+7*(15+N*(11+4*T))
  let print:=(4+10*56)+(4+(2*K)*(4+H*(2*scalar+4)))
  let printNames:=15*(56+1)+(15+(2*K)*(11+4*scalar))
  let temps:=((4+10*DescentResetStemKey.words D f M)+(4+q*(4+prev*(2*(14+(D+2)*(7+11))+4))))+
    (4+10*(span P+2*span n))+(4+10*DescentResetStemHeaders.romSize (b*7) n+(4+(2*K)*(4+54*n)))+
    ((4+10*DescentResetStemMux.words K (f+2) (b*7) M)+(4+q*(4+n*(2*(1+K*(30+7+22))+4))))
  project+(print+temps)+7*(printNames+codeTariff D f (b*7) K M P H G q 7)

/-- One literal program metered at the previous width, current width, padding,
and all block and slot multiplicities, including initialization of every table. -/
theorem tariff (base ptr b P H G X M₀ M w : ℕ) (parse : DescentResetStemKey.Decoder D f)
    (side : Fin Q→Bool) (src : Fin Q→Fin (D+2)→Expr) (ports : DescentResetStemIncidence.Ports (2*K))
    (T U : ℕ) (cost : ∀q i,(src q i).work≤T) (chart : ports.All (fun e=>e.work≤U))
    (old : 0<M₀) (block : 0<X) (lanes : 0<M) :
    ticks base ptr b P H G X M₀ M parse side src ports w+
      7*names (program base ptr b P H G X M₀ M parse side src ports w)≤
      bill D f b K P H G X M₀ M Q T U := by
  let A:=plan (splitAt base Q D P G X f M₀ M) ptr K H
  let ops:=operand base Q D P G X f M₀ M
  let cut:=splitAt base Q D P G X f M₀ M
  have cheap : ∀q i,(ops q i).work≤7:=fun _ _=>le_rfl
  have p:=DescentResetStemProjectExpr.tariff base P G X f M₀ M w (flat src) T (fun j=>cost _ _) old block lanes
  have ct:=ports.clock_bound (polarity K) U H cut A.raw chart
  have cs:=ports.names_bound (polarity K) b w U H cut A.raw chart
  have t:=A.clock_bound parse (direction X side) ops (b*7) K M P H G w 7 cheap
  have s:=A.names_bound parse (direction X side) ops (b*7) K M P H G w 7 cheap
  dsimp only [bill]
  unfold ticks program Layout.budget Layout.native
  rw [names_seq,names_seq]
  dsimp only at t
  dsimp only [A,ops,cut] at ct cs t s
  omega

end Projected
end
end Hierarchy.DescentResetStemPackedIssue.Mixed

end OAI
