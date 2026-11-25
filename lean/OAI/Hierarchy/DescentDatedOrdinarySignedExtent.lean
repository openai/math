import OAI.Hierarchy.DescentSignedLayout

namespace OAI
/-! Uniform address exponent for the complete ordinary signed program. -/
namespace Hierarchy.DescentDatedAddressBook
open DescentHaloWalkRAM DescentSIMDLookup DescentDyadicSpan
open DescentParallelBase.ParentFilter
open Filter
open scoped Classical
noncomputable section

namespace SignedExtent
variable {ι:ℕ→Type*}
theorem core_rate (s:∀h,ι h→SignedExtent) (room:ScalarRoom s):Bounded (fun h i=>(s h i).coreRoof 0):=by
  have c (n:ℕ):Bounded (ι:=ι) (fun _ _=>n):=Bounded.const n
  have dirs:=((c 3).mul ((room.oldHosts.mul (room.reach.mul room.reach)).padded))
  obtain ⟨ec,cmp⟩:=room.comparison
  obtain ⟨ep,panel⟩:=room.packed
  have p (n:ℕ):Bounded (fun h i=>2^(n*(s h i).digitArea)):=by
    apply Bounded.pow_of_linear (K:=n*ep)
    exact panel.mono (fun h ok i=>by simpa [Nat.mul_assoc] using Nat.mul_le_mul_left n (ok i))
  have converter:=((c 26).mul (Bounded.pow_of_linear cmp)).add ((c 2).mul (p 11))
  have rank:=((c 4).mul (p 10)).add (((room.blocks.mul (c 3)).mul (room.reach.mul room.slots)).mul room.rows.padded)
  have out:=((((c 8).add ((c 2).mul room.cap)).mul (c 2)).mul (p 9)).add ((room.blocks.mul ((c 2).mul room.cap)).mul room.rows.padded)
  have side:=((((c 2).mul (p 2)).add converter).add rank).add ((c 32).mul (p 8))
  simpa [coreRoof,signedBound,peerWords,directoryWords,rankWords,converterWords,formatterWords,outputWords,candidates,span] using
    dirs.add (side.add out)

set_option maxHeartbeats 1500000 in
theorem rate (s:∀h,ι h→SignedExtent) (r:ScalarRoom s):Bounded (fun h i=>(s h i).roof 0):=by
  have c (n:ℕ):Bounded (ι:=ι) (fun _ _=>n):=Bounded.const n
  obtain ⟨u,lin⟩:=r.packed
  have power (n:ℕ):Bounded (fun h i=>2^(n*(s h i).digitArea)):=by
    apply Bounded.pow_of_linear (K:=n*u)
    exact lin.mono (fun h ok i=>by simpa [Nat.mul_assoc] using Nat.mul_le_mul_left n (ok i))
  have one:Bounded (fun h i=>2^(s h i).digitArea):=by simpa using power 1
  have look:Bounded (fun h i=>2^(s h i).lookupArea):=by
    apply (power 2).of_le
    intro h i
    apply Nat.pow_le_pow_right (by decide)
    have win:=(Nat.le_mul_of_pos_right (s h i).fieldBits (r.batch h i))
    change (s h i).fieldBits*(s h i).lanes+(s h i).fieldBits≤2*((s h i).fieldBits*(s h i).lanes)
    omega
  have two:Bounded (fun h i=>2^(((s h i).fieldBits+(s h i).fieldBits)*(s h i).lanes)):=by
    simpa only [digitArea,two_mul,Nat.add_mul] using power 2
  have pairs:=r.reach.mul r.reach
  have hardware:=one.add ((pairs.mul look).add (one.add (two.add r.rows)))
  have jobs:=r.blocks.mul (r.reach.mul r.slots)
  have queries:=(r.blocks.mul (c 3)).mul ((r.reach.mul r.slots).mul ((r.reach.mul r.slots).add (c 1)))
  obtain ⟨_,route⟩:=r.route
  obtain ⟨_,cmp⟩:=r.comparison
  obtain ⟨_,step⟩:=r.routeQueries
  have fw:=Bounded.pow_of_linear (step.mono (fun h ok i=>(le_max_left _ _).trans (ok i)))
  have bw:=Bounded.pow_of_linear (step.mono (fun h ok i=>(le_max_right _ _).trans (ok i)))
  have idx:Bounded (fun h i=>(s h i).indexWords):=
    (((((r.hosts.mul pairs).padded.add (r.lows.mul r.oldRows.padded)).add r.rows.padded).add r.rows.padded).add r.oldHosts.padded)
  have fwdSmall (h i):(s h i).reverseArea≤(s h i).forwardArea:=
    Nat.mul_le_mul_right _ (Nat.le_add_right ..)
  have backOne:Bounded (fun h i=>2^(s h i).reverseArea):=fw.of_le (fun h i=>Nat.pow_le_pow_right (by decide) (fwdSmall h i))
  have twiceFW:Bounded (fun h i=>2^((s h i).forwardArea+(s h i).forwardArea)):=by
    simpa only [pow_add] using fw.mul fw
  have backLookup:Bounded (fun h i=>2^((s h i).reverseArea+DescentSharedCableNames.Packed.bits (s h i).reach)):=
    twiceFW.of_le (fun h i=>Nat.pow_le_pow_right (by decide) (Nat.add_le_add (fwdSmall h i)
      ((Nat.le_mul_of_pos_right _ (r.batch h i)).trans (fwdSmall h i))))
  have backDouble:Bounded (fun h i=>2^((DescentSharedCableNames.Packed.bits (s h i).reach+DescentSharedCableNames.Packed.bits (s h i).reach)*(s h i).lanes)):=by
    apply twiceFW.of_le;intro h i;apply Nat.pow_le_pow_right (by decide)
    rw [Nat.add_mul];exact Nat.add_le_add (fwdSmall h i) (fwdSmall h i)
  have backPages:Bounded (fun h i=>(s h i).reverseWords):=
    (backOne.add ((r.reach.mul backLookup).add (backOne.add (backDouble.add r.oldRows)))).add r.oldRows.padded.sub
  have peerEq (h i):(s h i).shortPeerKinds=(s h i).oldKey:=by unfold shortPeerKinds oldKey;ring
  have remoteOne:Bounded (fun h i=>2^(s h i).remoteArea):=Bounded.pow_of_linear route
  have peerLookup:Bounded (fun h i=>2^((s h i).peerSelectionArea+(s h i).fieldBits)):=by
    apply remoteOne.of_le;intro h i;apply Nat.pow_le_pow_right (by decide)
    simp only [remoteArea,peerSelectionArea,peerEq,Nat.add_mul]
    exact Nat.add_le_add_left (Nat.le_mul_of_pos_right _ (r.batch h i)) _
  have peerOne:Bounded (fun h i=>2^(s h i).peerSelectionArea):=
    peerLookup.of_le (fun h i=>Nat.pow_le_pow_right (by decide) (Nat.le_add_right ..))
  have prRaw:Bounded (fun h i=>2^((s h i).fieldBits*11*(s h i).lanes)):=by
    simpa only [digitArea,Nat.mul_left_comm,Nat.mul_assoc,Nat.mul_comm] using power 11
  have peerPages:Bounded (fun h i=>(s h i).peerSelectionWords):=
    (prRaw.add (peerOne.add (((pairs.mul r.lows).mul peerLookup).add (one.add (two.add r.rows))))).add r.rows.padded.sub
  have peerRows:=r.hosts.mul (pairs.mul r.lows)
  have peerDir:Bounded (fun h i=>(s h i).peerDirectoryWords):=
    (((((c 5).mul peerRows).add r.oldHosts).add (peerRows.add (c 1)).padded).add (r.oldHosts.add (c 1)).padded).add peerRows.padded
  have large:Bounded (fun h i=>2^(s h i).flagArea):=by
    apply (power 12).of_le
    intro h i;apply Nat.pow_le_pow_right (by decide)
    have bound:(s h i).fieldBits*11+1≤12*(s h i).fieldBits:=by have:=r.digit h i;omega
    simpa [flagArea,digitArea,Nat.mul_assoc] using Nat.mul_le_mul_right (s h i).lanes bound
  have shape:Bounded (fun h i=>2^(s h i).shapeArea):=by
    apply (power 6).of_le
    intro h i;apply Nat.pow_le_pow_right (by decide)
    have bound:4+(s h i).fieldBits*2≤6*(s h i).fieldBits:=by have:=r.digit h i;omega
    simpa [shapeArea,digitArea,Nat.mul_assoc] using Nat.mul_le_mul_right (s h i).lanes bound
  have gate:Bounded (fun h i=>2^(s h i).gateArea):=by
    apply (power 5).of_le
    intro h i;apply Nat.pow_le_pow_right (by decide)
    have bound:4+(s h i).fieldBits≤5*(s h i).fieldBits:=by have:=r.digit h i;omega
    simpa [gateArea,digitArea,Nat.mul_assoc] using Nat.mul_le_mul_right (s h i).lanes bound
  apply (core_rate s r).add
  unfold preparation
  have published0 := (c 3).mul ((r.hosts.mul pairs).padded)
  have published1 := published0.add ((c 2).mul (power 2))
  have published2 := published1.add (hardware)
  have published3 := published2.add (((jobs.mul (c 5)).mul r.rows.padded))
  have published4 := published3.add (((jobs.mul (c 11)).mul r.rows.padded))
  have published5 := published4.add ((((jobs.mul (c 11)).mul r.lows).mul r.oldRows.padded))
  have published6 := published5.add ((((r.reach.mul (r.lows.mul r.reach)).mul (c 2)).mul (Bounded.pow_of_linear route)))
  have published7 := published6.add (((queries.mul (c 11)).mul r.oldRows.padded))
  have published8 := published7.add ((c 26).mul (Bounded.pow_of_linear cmp))
  have published9 := published8.add ((c 4).mul large)
  have published10 := published9.add ((c 4).mul shape)
  have published11 := published10.add ((c 2).mul gate)
  have published12 := published11.add (idx)
  have published13 := published12.add ((c 2).mul fw)
  have published14 := published13.add ((c 2).mul bw)
  have published15 := published14.add (r.rows.padded.sub (y:=fun h i=>(s h i).slab))
  have published16 := published15.add (backPages)
  have published17 := published16.add (peerPages)
  have published18 := published17.add (peerDir)
  exact published18

end SignedExtent
end
end Hierarchy.DescentDatedAddressBook

end OAI
