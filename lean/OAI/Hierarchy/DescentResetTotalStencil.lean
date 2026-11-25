import OAI.Hierarchy.DescentResetMeasuredReturn

namespace OAI
/-! # Exact terminal lookup clock on arbitrary earlier RAM contents -/
namespace Hierarchy.DescentSixParty.PackedFlow.Padded
open DescentGLPacked.BankImage DescentPlainTerminal.Suffix DescentColonies DescentPackedColony DescentSIMDLookup
open DescentPackedZip DescentIssuedFallbackPanel DescentPacking.PackedMatch.Local
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable {w : ℕ} (S : StencilBook)

theorem repack_any_framed (chip : Bank) (first ratio : ℕ) {K₀ : ℕ} (factor : 2^S.c=K₀*(ratio*S.M))
    (ratioPos : 0<ratio) (pos : 0<S.M) (mem : Memory w) (early : chip.Fits w first)
    (room : ((1+S.maxPorts)+S.m)*S.hosts*chunks (2^S.c) (ratio*S.M)≤chip.size)
    (safe : Subwords.finish first (S.b*2^S.r) (((1+S.maxPorts)+S.m)*S.hosts) (2^S.c) ratio S.M<2^w) :
    ∃dst,(repackProgram S chip first ratio factor ratioPos pos w).Exec mem dst
      (repackTime S chip first ratio factor ratioPos pos) ∧ CheapCode (repackProgram S chip first ratio factor ratioPos pos w) ∧
      ∀z,z<first ∨ Subwords.finish first (S.b*2^S.r) (((1+S.maxPorts)+S.m)*S.hosts) (2^S.c) ratio S.M≤z→dst z=mem z := by
  let H:=((1+S.maxPorts)+S.m)*S.hosts
  let G:=2^S.c
  let a:=S.b*2^S.r
  let N:=H*chunks G S.M
  let T:=Subwords.chart first a H G ratio S.M
  let I:=Subwords.literals (w:=w) first H a factor ratioPos pos
  let out:=Subwords.destination first a H G ratio S.M
  have built:=Subwords.geometry (a:=a) (G:=G) (R:=ratio) (M:=S.M) first chip early room safe
  have it:I.low+I.length<2^w:=by
    rw [show I.low=first from rfl,Subwords.length_eq]
    dsimp [a, H, Subwords.finish,Subwords.destination,Subwords.endAt] at safe ⊢
    omega
  have valid:(Subwords.term T chip).Fits w out:=⟨built.dictFit,⟨built.offsetFit,trivial⟩,built.dataFit,built.parentFit,trivial⟩
  obtain ⟨written,_,hold⟩:=I.issue mem it
  refine ⟨_,written.then (scan_exec out N _ _ valid built.top),cheap_seq I.hardware.1 (@scan_cheap _ _ _ _),?_⟩
  have low:first≤out:=by dsimp [out,Subwords.destination,Subwords.endAt];omega
  have high:I.stop≤out:=by
    change Subwords.endAt first a H G ratio S.M≤Subwords.destination first a H G ratio S.M
    dsimp [Subwords.endAt,Subwords.destination];omega
  intro z away
  rcases away with under|above
  · exact (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ z (.inl (under.trans_le low))).trans (hold z (.inl under))
  · have last:out+N≤z:=above
    exact (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ z (.inr last)).trans (hold z (.inr (by omega)))

theorem repack_any (chip : Bank) (first ratio : ℕ) {K₀ : ℕ} (factor : 2^S.c=K₀*(ratio*S.M))
    (ratioPos : 0<ratio) (pos : 0<S.M) (mem : Memory w) (early : chip.Fits w first)
    (room : ((1+S.maxPorts)+S.m)*S.hosts*chunks (2^S.c) (ratio*S.M)≤chip.size)
    (safe : Subwords.finish first (S.b*2^S.r) (((1+S.maxPorts)+S.m)*S.hosts) (2^S.c) ratio S.M<2^w) :
    ∃dst,(repackProgram S chip first ratio factor ratioPos pos w).Exec mem dst
      (repackTime S chip first ratio factor ratioPos pos) ∧ CheapCode (repackProgram S chip first ratio factor ratioPos pos w) := by
  obtain ⟨dst,run,cheap,_⟩:=repack_any_framed S chip first ratio factor ratioPos pos mem early room safe
  exact ⟨dst,run,cheap⟩

theorem paid_any_framed (X : StencilBook.Sources) (base out f B K g cap Y : ℕ) (mem : Memory w)
    (room : StencilBook.Geometry S X base out w) (safe : S.endAddress base<2^w)
    (short : S.M*max (S.n*Stencil.count S.r (S.degree+S.degree)) (S.t*2^S.r)≤w/2)
    (word : S.n*S.M≤w) :
    ∃dst,(paidProgram S X base out f B K g cap Y w).Exec mem dst (paidTime S X base out f B g) ∧
      CheapCode (paidProgram S X base out f B K g cap Y w) ∧
      ∀z,z<base ∨ S.endAddress base≤z→dst z=mem z := by
  let A:=S.layer base out X.roster
  let L:=S.chosen base out X.roster
  let H:=S.header base
  let C:=S.readers base
  let F:=S.last base
  let P:=S.inputs X base out g
  let D:=32*Nat.clog 2 (2*S.degree)
  let bound:=2^(f+1)*B
  let I:=splitImage A S.degree S.hosts S.c S.r S.b S.M D bound w
  let data:=fun z=>(C.inputs P).field z
  have start:base≤A.origin:=Nat.le_add_right ..
  have before:H.origin≤H.stop:=by dsimp [PortLevels.AddressBook.stop,PortLevels.AddressBook.lead,
    PortLevels.AddressBook.depth,PortLevels.AddressBook.pos];omega
  have past:H.stop≤C.origin:= ((Nat.le_add_right H.stop _).trans (Nat.le_add_right ..)).trans (Nat.le_add_right ..)
  have old:=room.old.roster
  have area:=S.layer_room base out X.roster (by simpa only [StencilBook.rows,Nat.mul_assoc] using room.small)
    ⟨old.1,old.2.1,old.2.2.trans start⟩ room.ports ((before.trans past).trans_lt room.safe)
  have early:A.origin≤A.fresh S.degree S.r:=Nat.le_add_right ..
  have fit : I.low + I.length < 2^w := by
    change A.origin + (A.fresh S.degree S.r - A.origin) < 2^w
    have bound := area.endFits
    change A.fresh S.degree S.r + (S.r+1)*A.page < 2^w at bound
    omega
  obtain ⟨stamp,_,stampFrame⟩:=I.issue mem fit
  obtain ⟨pass,cheap⟩:=DescentPackedColony.physical L (Frame.hardware A area) (I.output mem)
  obtain ⟨m₂,scalar,_,_,_,scalarFrame,hardware⟩:=S.scalar_issue base K (2^f*B) (2^S.r*cap)
    (result (passes L S.hosts (2^S.c) S.M S.r) (I.output mem)) room.safe
  let m₃:=(C.planes (w:=w)).output (C.image.output m₂)
  have input:=S.fit X base out g room
  have stop:C.origin≤C.stop:=C.before_planes.trans C.plane_le
  have ready:C.stop≤F.scratch := ((Nat.le_add_right C.stop _).trans (Nat.le_add_right ..)).trans (Nat.le_add_right ..)
  have finalWords:F.scratch≤F.endAddress:=by dsimp [Stencil.Layout.Chart.endAddress,Stencil.Layout.Chart.out];omega
  have space:F.endAddress<2^w:=safe
  obtain ⟨reader,rom,readerFrame,rh⟩:=C.issue_readers P C.stop m₂ le_rfl ((ready.trans finalWords).trans_lt space) word
    (fun d=>ProtocolRAMGeneratedWrite.fits_mono _ stop (input.planes d))
  obtain ⟨catalog,_,_,catalogFrame,ch⟩:=F.issued f B Y m₃ space
  let m₄:=(F.literals (w:=w) f B Y).output (F.gathers.output m₃)
  have arm:=Stencil.fields_fit C P input stop m₃ rom
  have bounds:=F.gather_bounds data (fun j=>ProtocolRAMGeneratedWrite.fits_mono _ ready (arm j)) space
  have asm:=(Gather.fits F.tabs (fun i=>data (Stencil.slotName S.r (S.degree+S.degree) i)) F.scratch bounds (List.finRange _))
  obtain ⟨tab,openAt,_,_⟩:=F.fit space short
  let N:=S.rows
  let m₅:=image F.scratch N (Stencil.assembly F.tabs data) m₄
  have collect:=@scan_exec w F.scratch N (Stencil.assembly F.tabs data) m₄ asm openAt
  have tables:(DescentSIMDLookup.lookup F.banks).Fits w F.out:=⟨⟨tab.dictionary,tab.source,trivial⟩,tab.mask,trivial⟩
  have lookup:=@scan_exec w F.out N (DescentSIMDLookup.lookup F.banks) m₅ tables tab.output
  refine ⟨image F.out N (DescentSIMDLookup.lookup F.banks) m₅,?_,?_,?_⟩
  · have price : 4+N*(2*(DescentSIMDLookup.lookup F.banks).work+4) = 4+44*N := by
      rw [DescentSIMDLookup.lookup_work]
      ring
    rw [price] at lookup
    have priceTotal : (4+10*I.length+clock (passes L S.hosts (2^S.c) S.M S.r)+S.scalarTime base) +
        (8+10*(C.stop-C.origin)+(8+10*(F.scratch-F.base))+
          (4+N*(2*(Stencil.assembly F.tabs data).work+4)+(4+44*N))) = paidTime S X base out f B g := by rfl
    rw [←priceTotal]
    intro ps rs ks mach pc reg pub exit mounted romWords cfg memory startCfg memoryEq
    exact Procedure.Exec.then (Procedure.Exec.then (Procedure.Exec.then @stamp @pass) @scalar)
      (Procedure.Exec.then (Procedure.Exec.then @reader @catalog) (Procedure.Exec.then @collect @lookup))
      mach pc reg pub exit mounted romWords cfg memory startCfg memoryEq
  · exact cheap_seq (cheap_seq (cheap_seq I.hardware.1 cheap) hardware)
      (cheap_seq (cheap_seq rh ch) (cheap_seq (@scan_cheap _ _ _ _) (@scan_cheap _ _ _ _)))

  · have land:=S.split_end base X.roster (S.weightBank out)
    change A.fresh S.degree S.r+(S.r+1)*A.page=H.origin at land
    have layers:A.fresh S.degree S.r+S.r*A.page≤H.origin:=by rw [←land,Nat.succ_mul];omega
    have head:C.origin=S.afterHeader base:=rfl
    have lastBase:F.base=C.stop:=rfl
    have roomN:N≤F.rowRoom:=F.rowRoom_le
    have outEq:F.out=F.scratch+F.rowRoom:=rfl
    have stopEq:S.endAddress base=F.out+N:=rfl
    have stages:A.origin≤H.origin:=by omega
    have stFrame (z) (away:z<base ∨ S.endAddress base≤z) :
        result (passes L S.hosts (2^S.c) S.M S.r) (I.output mem) z=I.output mem z := by
      apply split_frame (h:=S.m) (l:=0) A area
      rcases away with lo|hi
      · exact .inl ((lo.trans_le start).trans_le early)
      · exact .inr (by change A.fresh S.degree S.r+S.r*A.page≤z; omega)
    intro z away
    have initFrame:=stFrame z away
    rcases away with lo|hi
    · exact (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ z (.inl (by omega))).trans
        ((ProtocolRAMGeneratedWrite.frame_image _ _ _ _ z (.inl (by omega))).trans
        ((catalogFrame z (.inl (by omega))).trans ((readerFrame z (.inl (by omega))).trans
        ((scalarFrame z (.inl (lo.trans_le (start.trans stages)))).trans (initFrame.trans (stampFrame z (.inl (lo.trans_le start))))))))
    · exact (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ z (.inr (by omega))).trans
        ((ProtocolRAMGeneratedWrite.frame_image _ _ _ _ z (.inr (by omega))).trans
        ((catalogFrame z (.inr (by omega))).trans ((readerFrame z (.inr (by omega))).trans
        ((scalarFrame z (.inr (by omega))).trans (initFrame.trans (stampFrame z (.inr (by change A.fresh S.degree S.r≤z;omega))))))))

theorem paid_any (X : StencilBook.Sources) (base out f B K g cap Y : ℕ) (mem : Memory w)
    (room : StencilBook.Geometry S X base out w) (safe : S.endAddress base<2^w)
    (short : S.M*max (S.n*Stencil.count S.r (S.degree+S.degree)) (S.t*2^S.r)≤w/2)
    (word : S.n*S.M≤w) :
    ∃dst,(paidProgram S X base out f B K g cap Y w).Exec mem dst (paidTime S X base out f B g) ∧
      CheapCode (paidProgram S X base out f B K g cap Y w) := by
  obtain ⟨dst,run,cheap,_⟩:=paid_any_framed S X base out f B K g cap Y mem room safe short word
  exact ⟨dst,run,cheap⟩

end
end Hierarchy.DescentSixParty.PackedFlow.Padded

end OAI
