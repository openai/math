import OAI.Computability.BorderVNP.CubeTeamDeclarationReturn
import OAI.Computability.BorderVNP.CubeTeamOwnedSelectorRows
import OAI.Computability.BorderVNP.CubeISAOwnedStrictSideInverse
import OAI.Computability.BorderVNP.CubeTeamOwnedVertexCount

/-! # Constructing declaration-check evidence from the actual stage returns -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.TeamRows

open RoutingISA RoutingISA.OwnedStages RoutingISA.CellDispatch Physical Physical.Owned Cube.Tally Cube.Scatter VPVNP.BurstRAM

variable {w n d blocks b h K s : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}

/-- The raw group program itself supplies its chronological history of ordered visits.
The initial vertex-pointer load and the outer cursor setup both preserve memory. -/
theorem ownedGroups_history {l : TeamRowPrepare.Layout} {resident : Memory w → Prop}
    (F : ScanFrame l (strictRole n b h K s) (diagonalRole n b h K s) resident pub mac)
    (fit : l.Fits w) (frame : readings pub 0 = l.frame)
    {r : Bank w} {m : Memory w} {es t mt} (initial : resident m)
    (run : Runs pub mac (ownedGroups n b h K s) r m es t mt) :
    ∃ a rows gs u mu, ReturnedRows pub mac l (strictRole n b h K s) (diagonalRole n b h K s)
      0 a m rows gs u mu := by
  obtain ⟨_,v,mv,_,_,start,tail⟩ := seq_split run
  obtain ⟨_,u,mu,_,_,scanRun,_⟩ := seq_split tail
  have room : l.frame+78 < 2^w := by have h := fit.frameFit; omega
  obtain ⟨_,_,_,same⟩ := startVertices_return frame room rfl start
  subst mv
  obtain ⟨_,a,rows,gs,_,_,hist,_,_,_⟩ := scan_decode F fit frame initial scanRun
  exact ⟨a,rows,gs,u,mu,hist⟩

/-- Inverting a strict scatter supplies the checker's addressed metadata, sorted endpoint
registers and the very selector prefixes that it subsequently validates. This argument
uses the return on its actual private tape and accepts arbitrary values of the public claim. -/
theorem strict_check_words (D : PacketRowData n d blocks b h K s) (A : SideData n d blocks b h)
    (actual claimed : ℕ) (rows : Sym2 (Fin d) → Fin (n+1) → ℕ)
    {src : Set ℕ} {r m es u mu} (ready : SideReady D A pub src r m)
    (input : CheckImage (layout D A.power A.header) src n actual claimed rows m)
    (space : LocalRow.Space (layout D A.power A.header) w n b h K s (readings pub 0) actual claimed)
    (directorySep : ∀ x ∈ src, x < A.out ∨ A.out+(2*blocks*(d.choose 2)^n)*(3*2^n) ≤ x)
    (scatter : Runs pub mac (strictSide n b h K s) r m es u mu) :
    ∃ v : CheckAddresses, CheckWords blocks b h K s v pub (D.axis,rows) D.pair.val.1 D.pair.val.2 u mu ∧
      ∀ p : {p : Packet n d blocks // p.1.1 D.axis = D.pair}, SelectorRead.Stored (readings mu)
        (v.bank+packetIndex p.val*bankWidth n b h K s) (D.select p.val) := by
  obtain ⟨x,z,exterior,_,_,_,result⟩ := strictSide_recover D A pub mac src r m ready scatter
  let E := D.withWords x z
  have streams := crossing_exterior D A x z exterior
  have entry : SideReady E A pub src r m := {ready with crosses := streams ▸ ready.crosses}
  have keep (a : ℕ) (ha : a ∈ src) : mu a = m a := by
    rcases directorySep a ha with low | high
    · exact result.source a ha low
    · exact result.above a ha high
  have im := input.transfer keep
  let v : CheckAddresses := ⟨A.power,A.header,D.base,actual,claimed⟩
  have retain (j : Reg) (hj : Control j) (h7 : j ≠ 7) : readings u j = readings r j :=
    congrArg Fin.val (result.keep j hj h7)
  refine ⟨v,⟨ready.protect.loaded ready.loaded keep,im.actualAt,im.claimedAt,im.table,space,?_⟩,?_⟩
  · exact ⟨(retain _ (by decide) (by decide)).trans ready.entry.zero,
      (retain _ (by decide) (by decide)).trans ready.entry.one,(retain _ (by decide) (by decide)).trans ready.entry.axis,
      (retain _ (by decide) (by decide)).trans ready.entry.left,(retain _ (by decide) (by decide)).trans ready.entry.right⟩
  · intro p
    simpa only [v,E,PacketRowData.withWords,OwnedVertex.bankAt,ready.stride] using
      stored_after_strictSide entry result p.val p.property

/-- Inverting the scalar scatter retains the advertised diagonal row independently of the
private singleton bits. The local declaration checker thus receives the actual table. -/
theorem diagonal_check_words (v : CheckAddresses) (decl : LengthDeclaration n d) (x : Fin d)
    (D : SingleRowData n d (blocks*(h*b))) (axis : D.axis = decl.1) (left : D.left = x) (right : D.right = x)
    {src : Set ℕ} {r m es u mu} (en : Entry D.axis D.left D.right r)
    (sel : r 36 = DiagonalResidueRAM.word w D.selector) (cross : r 37 = DiagonalResidueRAM.word w D.crossing)
    (loaded : (v.layout d blocks b h).Loaded n (readings pub) (readings m))
    (protection : Protected (v.layout d blocks b h) n (pub 0).val src)
    (space : LocalRow.Space (v.layout d blocks b h) w n b h K s (readings pub 0) v.actual v.claimed)
    (input : CheckImage (v.layout d blocks b h) src n v.actual v.claimed decl.2 m)
    (prepared : D.PreparedRow src m) (fZ : (pub 0).val+56 ∈ src) (fB : (pub 0).val+88 ∈ src)
    (zAt : readings m ((pub 0).val+56) = d^(n+1)) (bankAt : readings m ((pub 0).val+88) = D.bank)
    (room : SingleRoom w n d (blocks*(h*b)) (pub 0).val D.bank)
    (scatter : Runs pub mac (diagonalSide n) r m es u mu) : CheckWords blocks b h K s v pub decl x x u mu := by
  let E := D.withTape (ChoiceTape.extend (es.flatMap TeamRAM.Event.choices))
  obtain ⟨_,_,kept,_,_,out⟩ := singleStage_recover pub mac (v.layout d blocks b h) D src r m en sel cross
    loaded space.frameFit prepared fZ fB zAt bankAt room.frameFit room.keys room.allocation scatter
  have eprep : E.PreparedRow src m := D.prepared_withTape _ m prepared
  have keep (j : ℕ) (hj : j ∈ src) : mu j = m j := (congrFun out j).trans (E.before_source m eprep _ j hj)
  have im := input.transfer keep
  refine ⟨protection.loaded loaded keep,im.actualAt,im.claimedAt,im.table,space,?_⟩
  simpa only [axis,left,right] using en.keep kept

end Cube.TeamRows

end BorderVNP
end Computability
end OAI
