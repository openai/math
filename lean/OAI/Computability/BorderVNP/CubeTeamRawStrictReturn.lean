import OAI.Computability.BorderVNP.CubeTeamRawSideSpace
import OAI.Computability.BorderVNP.CubeISAOwnedRawPacketStage

/-! # Reading a canonical declaration row from its real strict-side execution -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.TeamRows

open RoutingISA RoutingISA.CellDispatch RoutingISA.OwnedStages RoutingISA.OwnedVertex
open Physical Physical.Owned Tally Scatter VPVNP.BurstRAM DiagonalResidueRAM

/-- Every real strict-side return observes its own selector words in the incoming prefix.
Both singleton passes and the vertex writer leave precisely those selector fields available
to the subsequent checker, regardless of the incoming crossing words. -/
theorem rawStrict_return {w n d blocks b h K s : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    (v : CheckAddresses) (decl : LengthDeclaration n d) (pair : Symbols d) (high : Bool)
    (single sel out : ℕ) (src : Set ℕ) (raw : List Bool) {r : Bank w} {m : Memory w} {es t mt}
    (entry : Entry decl.1 pair.val.1 pair.val.2 r) (group : readings r 3 = (if high then pair.val.2 else pair.val.1).val)
    (selAt : r 36 = word w sel) (outAt : readings r 7 = out)
    (loaded : (v.layout d blocks b h).Loaded n (readings pub) (readings m))
    (image : CheckImage (v.layout d blocks b h) src n v.actual v.claimed decl.2 m)
    (zAt : readings m ((pub 0).val+56) = d^(n+1)) (singleAt : readings m ((pub 0).val+88) = single)
    (space : RawSideSpace blocks b h K s v single out decl.1 pair pub src)
    (len : raw.length = 2*blocks*(d.choose 2)^n*selectorWidth n K h) (bits : Resident src m sel raw)
    (run : Runs pub mac (strictSide n b h K s) r m es t mt) :
    CheckWords blocks b h K s v pub decl pair.val.1 pair.val.2 t mt ∧
      (∀ x ∈ src, mt x = m x) ∧ (∀ j, Control j → j ≠ 7 → t j = r j) ∧
      t 36 = word w (sel+raw.length) ∧ readings t 7 = out+(2*blocks*(d.choose 2)^n)*(3*2^n) ∧
      ∃ S : Packet n d blocks → Selector n K h, raw = commonSelectors S decl.1 pair ∧
        ∀ p : {p : Packet n d blocks // p.1.1 decl.1 = pair}, SelectorRead.Stored (readings mt)
          (v.bank+packetIndex p.val*bankWidth n b h K s) (S p.val) := by
  obtain ⟨_,y,my,_,_,scatter,vertices⟩ := seq_split run
  obtain ⟨_,u,mu,_,_,pack,doubled⟩ := seq_split scatter
  let L := v.layout d blocks b h
  obtain ⟨control1,sel1,source1,S,observed,stored⟩ := rawPacketStage_return pub mac L src decl.1 pair high
    sel raw r m entry group selAt loaded space.packet space.packetSource len bits pack
  -- Only geometry and the recovered selectors are used by the singleton/vertex suffix.
  let D : PacketRowData n d blocks b h K s := ⟨decl.1,pair,high,v.bank,bankWidth n b h K s,sel,0,S,
    fun _ _ _ => false,fun _ _ _ => false⟩
  let A : SideData n d blocks b h := ⟨v.powers,v.header,single,out,fun _ _ => false⟩
  have room : RawTailRoom D A pub src := ⟨rfl,space.packet,space.singleton,space.frame,space.fields,
    space.singleSource,space.beforeSingle,space.beforeVertex,space.directory,space.source⟩
  have z := (congrArg Fin.val (source1 _ space.fields.1)).trans zAt
  have bank := (congrArg Fin.val (source1 _ space.fields.2)).trans singleAt
  obtain ⟨control2,sel2,cursor,source2,final⟩ := rawTail_return D A src (entry.keep control1)
    ((congrArg Fin.val (control1 _ (by decide))).trans group) ((congrArg Fin.val (control1 _ (by decide))).trans outAt)
    (space.frame.loaded loaded source1) z bank room stored doubled vertices
  have keep (j : Reg) (hj : Control j) (h7 : j ≠ 7) := (control2 j hj h7).trans (control1 j hj)
  have old (x : ℕ) (hx : x ∈ src) := (source2 x hx).trans (source1 x hx)
  have im := image.transfer old
  have k (j : Reg) (hj : Control j) (h7 : j ≠ 7) := congrArg Fin.val (keep j hj h7)
  refine ⟨⟨space.frame.loaded loaded old,im.actualAt,im.claimedAt,im.table,space.checker,?_⟩,old,keep,
    sel2.trans sel1,cursor,S,observed,fun p => final p.val p.property⟩
  exact ⟨(k _ (by decide) (by decide)).trans entry.zero,(k _ (by decide) (by decide)).trans entry.one,
    (k _ (by decide) (by decide)).trans entry.axis,(k _ (by decide) (by decide)).trans entry.left,
    (k _ (by decide) (by decide)).trans entry.right⟩

end Cube.TeamRows

end BorderVNP
end Computability
end OAI
