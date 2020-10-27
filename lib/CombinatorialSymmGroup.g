# It tests if The permutation TheSigma is such that
# Permuted(EXT1, TheSigma) differ from EXT2 only by
# scalar multiplications and an affine transformation
# The equation solved is EXT1[i] A = Alpha[i] EXT2[sigma(i)]
KernelTestProjectiveEquivalence:=function(EXT1, EXT2, TheSigma)
  local ListEqua, n, nbVert, ListUnk, i, j, iVert, nbUnk, eEqua, jVert, idx, Amat, AlphaVect, eDiff, NSP, eSol;
  n:=Length(EXT1[1]);
  nbVert:=Length(EXT1);
  # EXT must be a non-decomposable polytope
  if RankMat(EXT1)<>n then
    Error("The matrix EXT1 is not full dimensional");
  fi;
  if RankMat(EXT2)<>n then
    Error("The matrix EXT2 is not full dimensional");
  fi;
  ListUnk:=[];
  for i in [1..n]
  do
    for j in [1..n]
    do
      Add(ListUnk, [0, i, j]);
    od;
  od;
  for iVert in [1..nbVert]
  do
    Add(ListUnk, [1, iVert]);
  od;
  nbUnk:=n*n+nbVert;
  ListEqua:=[];
  for iVert in [1..nbVert]
  do
    for i in [1..n]
    do
      eEqua:=ListWithIdenticalEntries(nbUnk,0);
      for j in [1..n]
      do
        idx:=Position(ListUnk, [0,j,i]);
        eEqua[idx]:=EXT1[iVert][j];
      od;
      jVert:=OnPoints(iVert, TheSigma);
      idx:=Position(ListUnk, [1, iVert]);
      eEqua[idx]:=-EXT2[jVert][i];
      Add(ListEqua, eEqua);
    od;
  od;
  NSP:=NullspaceMat(TransposedMat(ListEqua));
  if Length(NSP)<>1 then
    # this is where non-decomposability is used.
    return rec(reply:=false);
  fi;
  eSol:=NSP[1];
  Amat:=NullMat(n,n);
  for i in [1..n]
  do
    for j in [1..n]
    do
      idx:=Position(ListUnk, [0,i,j]);
      Amat[i][j]:=eSol[idx];
    od;
  od;
  AlphaVect:=ListWithIdenticalEntries(nbVert, 0);
  for iVert in [1..nbVert]
  do
    idx:=Position(ListUnk, [1, iVert]);
    AlphaVect[iVert]:=eSol[idx];
  od;
  for iVert in [1..nbVert]
  do
    jVert:=OnPoints(iVert, TheSigma);
    eDiff:=EXT1[iVert]*Amat - AlphaVect[iVert]*EXT2[jVert];
    if eDiff<>ListWithIdenticalEntries(n,0) then
      Error("We have inconsistency in our book keeping");
    fi;
  od;
  if Minimum(AlphaVect)>0 or Maximum(AlphaVect)<0 then
    return rec(reply:=true, AlphaVect:=AlphaVect, Amat:=Amat);
  fi;
  return rec(reply:=false);
end;

GetFamilyPair:=function(n, ListSets)
  local ListAdjacency, nbC, i, iSet, eSet, eElt, ThePartition;
  ListAdjacency:=[];
  nbC:=n + Length(ListSets);
  for i in [1..nbC]
  do
    Add(ListAdjacency, []);
  od;
  for iSet in [1..Length(ListSets)]
  do
    eSet:=ListSets[iSet];
    for eElt in eSet
    do
      Add(ListAdjacency[eElt], n+iSet);
      Add(ListAdjacency[n+iSet], eElt);
    od;
  od;
  ThePartition:=[[1..n], [n+1..n+Length(ListSets)]];
  return rec(ListAdjacency:=ListAdjacency, 
             ThePartition:=ThePartition);
end;

SetFamilyGroup:=function(n, ListSets)
  local eRec, GRP;
  eRec:=GetFamilyPair(n, ListSets);
  GRP:=SymmetryGroupVertexColoredGraphAdjList(eRec.ListAdjacency, eRec.ThePartition);
  return SecondReduceGroupAction(GRP, [1..n]);
end;

SetFamilyEquivalence:=function(n, ListSets1, ListSets2)
  local eRec1, eRec2, TheReply;
  if Length(ListSets1)<>Length(ListSets2) then
    return false;
  fi;
  eRec1:=GetFamilyPair(n, ListSets1);
  eRec2:=GetFamilyPair(n, ListSets2);
  TheReply:=EquivalenceVertexColoredGraphAdjList(eRec1.ListAdjacency, eRec2.ListAdjacency, eRec1.ThePartition);
  if TheReply=false then
    return false;
  fi;
  return PermList(TheReply{[1..n]});
end;



GetCombinatorialSymmetryGroupFromFacetsOrbitwise:=function(EXT)
  local TheLinearGroup, LORB, eOrb, ListSets, GRP;
  TheLinearGroup:=__TheCore_Automorphism(EXT);
  LORB:=DualDescriptionStandard(EXT, TheLinearGroup);
  ListSets:=[];
  for eOrb in LORB
  do
    Append(ListSets, Orbit(TheLinearGroup, eOrb, OnSets));
  od;
  GRP:=SetFamilyGroup(Length(EXT), ListSets);
  return GRP;
end;


__GetListSetsOfFacets:=function(EXT)
  local FAC, ListSets, eFac, eSet;
  FAC:=DualDescription(EXT);
  ListSets:=[];
  for eFac in FAC
  do
    eSet:=Filtered([1..Length(EXT)], x->EXT[x]*eFac=0);
    Add(ListSets, eSet);
  od;
  return ListSets;
end;




GetCombinatorialSymmetryGroupFromFacets:=function(EXT)
  local ListSets;
  ListSets:=DualDescriptionSets(EXT);
  return SetFamilyGroup(Length(EXT), ListSets);
end;

CombPolytope_Automorphism:=GetCombinatorialSymmetryGroupFromFacets;

CombPolytope_Isomorphism:=function(EXT1, EXT2)
  local nbV, ListSets1, ListSets2;
  if Length(EXT1)<>Length(EXT2) then
    return false;
  fi;
  nbV:=Length(EXT1);
  ListSets1:=DualDescriptionSets(EXT1);
  ListSets2:=DualDescriptionSets(EXT2);
  return SetFamilyEquivalence(nbV, ListSets1, ListSets2);
end;


TestProjectiveEquivalence:=function(EXT1, EXT2, TheSigma)
  local nbVert, EXTred1, eRecDecomp1, EXTred2, eRecDecomp2, nbConn, AlphaVect, eConn1, eConn2, iVert, eVert, iConn, fVert, EXTcompRed1, EXTcompRed2, eTest, EXT2mod, i, eNewEXT, Amat;
  nbVert:=Length(EXT1);
  if Length(EXT1)<>Length(EXT2) then
    return rec(reply:=false);
  fi;
  EXTred1:=ColumnReduction(EXT1).EXT;
  eRecDecomp1:=DirectSumDecompositionPolyhedralCone(EXTred1);
  EXTred2:=ColumnReduction(EXT2).EXT;
  eRecDecomp2:=DirectSumDecompositionPolyhedralCone(EXTred2);
  #
  nbConn:=Length(eRecDecomp1.ListListIdx);
  if nbConn<>Length(eRecDecomp2.ListListIdx) then
    return rec(reply:=false);
  fi;
  AlphaVect:=ListWithIdenticalEntries(nbVert,0);
  for iConn in [1..nbConn]
  do
    eConn1:=eRecDecomp1.ListListIdx[iConn];
    eConn2:=[];
    for eVert in eConn1
    do
      fVert:=OnPoints(eVert, TheSigma);
      Add(eConn2, fVert);
    od;
    if Position(eRecDecomp2.ListListIdx, Set(eConn2))=fail then
      return rec(reply:=false);
    fi;
    EXTcompRed1:=ColumnReduction(EXT1{eConn1}).EXT;
    EXTcompRed2:=ColumnReduction(EXT2{eConn2}).EXT;
    eTest:=KernelTestProjectiveEquivalence(EXTcompRed1, EXTcompRed2, () );
    if eTest.reply=false then
      return rec(reply:=false);
    fi;
    for iVert in [1..Length(eConn1)]
    do
      eVert:=eConn1[iVert];
      AlphaVect[eVert]:=eTest.AlphaVect[iVert];
    od;
  od;
  EXT2mod:=[];
  for i in [1..Length(EXT2)]
  do
    eNewEXT:=AlphaVect[i]*EXT2[OnPoints(i, TheSigma)];
    Add(EXT2mod, eNewEXT);
  od;
  Amat:=FindTransformation(EXTred1, EXTred2, () );
  return rec(reply:=true, AlphaVect:=AlphaVect, Amat:=Amat);
end;

TestMembershipProjectiveGroup:=function(EXT, TheSigma)
  local EXTred, eRecDecomp;
  EXTred:=ColumnReduction(EXT).EXT;
  eRecDecomp:=DirectSumDecompositionPolyhedralCone(EXTred);
  if Length(eRecDecomp.ListConn)> 1 then
    Error("The polytope is decomposable and that is not allowed");
  fi;
  return KernelTestProjectiveEquivalence(EXTred, EXTred, TheSigma).reply;
end;

TestProjectiveIsomorphy:=function(EXT1, EXT2)
  local EXTred1, EXTred2, eRecDecomp1, eRecDecomp2, GRPlin1, GRPlin2, GRPcomb1, GRPcomb2, LORB1, LORB2, ListSets1, ListSets2, eOrb, nbVert, ePermTest, g, LDCS, eDCS, eRepr, test, GRPlinTrans1, EXTredTrans1, gPerm, eReply, eListTest;
  EXTred1:=ColumnReduction(EXT1).EXT;
  eRecDecomp1:=DirectSumDecompositionPolyhedralCone(EXTred1);
  if Length(eRecDecomp1.ListConn)> 1 then
    Error("The polytope is decomposable and that is not allowed");
  fi;
  EXTred2:=ColumnReduction(EXT2).EXT;
  eRecDecomp2:=DirectSumDecompositionPolyhedralCone(EXTred2);
  if Length(eRecDecomp2.ListConn)> 1 then
    Error("The polytope is decomposable and that is not allowed");
  fi;
  if Length(EXTred1)<>Length(EXTred2) then
    return false;
  fi;
  nbVert:=Length(EXTred1);
  if Length(EXTred1[1])<>Length(EXTred2[1]) then
    return false;
  fi;
  eListTest:=__TheCore_Isomorphism(EXTred1, EXTred2);
  if eListTest<>false then
    ePermTest:=PermList(eListTest);
    if KernelTestProjectiveEquivalence(EXTred1, EXTred2, ePermTest).reply=false then
      Error("Error in computation of equivalence");
    fi;
    return ePermTest;
  fi;
  #
  GRPlin1:=__TheCore_Automorphism(EXTred1);
  LORB1:=DualDescriptionStandard(EXTred1, GRPlin1);
  ListSets1:=[];
  for eOrb in LORB1
  do
    Append(ListSets1, Orbit(GRPlin1, eOrb, OnSets));
  od;
  #
  GRPlin2:=__TheCore_Automorphism(EXTred2);
  LORB2:=DualDescriptionStandard(EXTred2, GRPlin2);
  ListSets2:=[];
  for eOrb in LORB2
  do
    Append(ListSets2, Orbit(GRPlin2, eOrb, OnSets));
  od;
  gPerm:=SetFamilyEquivalence(nbVert, ListSets1, ListSets2);
  if gPerm=false then
    return false;
  fi;
  GRPcomb2:=SetFamilyGroup(nbVert, ListSets2);
  #
#  g:=RepresentativeAction(SymmetricGroup([1..nbVert]), GRPcomb1, GRPcomb2);
  GRPlinTrans1:=Group(List(GeneratorsOfGroup(GRPlin1), x->Inverse(gPerm)*x*gPerm));
  EXTredTrans1:=Permuted(EXTred1, gPerm);
  if __TheCore_Automorphism(EXTredTrans1)<>GRPlinTrans1 then
    Error("Incorred group or polytope");
  fi;
  LDCS:=DoubleCosets(GRPcomb2, GRPlinTrans1, GRPlin2);
  for eDCS in LDCS
  do
    eRepr:=Representative(eDCS);
    test:=KernelTestProjectiveEquivalence(EXTredTrans1, EXTred2, eRepr).reply;
    if test<>false then
      eReply:=gPerm*eRepr;
      if KernelTestProjectiveEquivalence(EXTred1, EXTred2, eReply).reply=false then
        Error("Error in computation of equivalence");
      fi;
      return eReply;
    fi;
  od;
  return false;
end;

ProjPolytope_Isomorphism:=function(EXT1, EXT2)
  local GetInfoDecompo, nbVert, eRec1, eRec2, nbIrred, ListCorresp, iIrred, eList, jIrred, eConn1, eConn2, lenConn, eTestEquiv, len, iPt, jPt, EXTred1, EXTred2, i, iConn1, iConn2, iVert1, iVert2, TheSigma, WeFind;
  GetInfoDecompo:=function(EXT)
    local EXTred, nbVert, eRecDecomp, nbConn, ListConnStatus, ListMultiplicity, ListIrred, iConn, EXTred1, eSet, jConn, EXTred2, eTestEquiv;
    EXTred:=ColumnReduction(EXT).EXT;
    nbVert:=Length(EXTred);
    eRecDecomp:=DirectSumDecompositionPolyhedralCone(EXTred);
    nbConn:=Length(eRecDecomp.ListConn);
    ListConnStatus:=ListWithIdenticalEntries(nbConn, 1);
    ListMultiplicity:=[];
    ListIrred:=[];
    for iConn in [1..nbConn]
    do
      if ListConnStatus[iConn]=1 then
        EXTred1:=eRecDecomp.ListEXTred[iConn];
        Add(ListIrred, EXTred1);
        eSet:=[iConn];
        for jConn in [iConn+1..nbConn]
        do
          EXTred2:=eRecDecomp.ListEXTred[jConn];
          eTestEquiv:=TestProjectiveIsomorphy(EXTred1, EXTred2);
          if eTestEquiv<>false then
            ListConnStatus[jConn]:=0;
            Add(eSet, jConn);
          fi;
        od;
        Add(ListMultiplicity, eSet);
      fi;
    od;
    return rec(ListMultiplicity:=ListMultiplicity,
               ListEXTred:=eRecDecomp.ListEXTred, 
               ListIrred:=ListIrred,
               ListListIdx:=eRecDecomp.ListListIdx);
  end;
  if Length(EXT1)<>Length(EXT2) then
    return false;
  fi;
  nbVert:=Length(EXT1);
  eRec1:=GetInfoDecompo(EXT1);
  eRec2:=GetInfoDecompo(EXT2);
  if Length(eRec1.ListIrred)<>Length(eRec2.ListIrred) then
    return false;
  fi;
  if Collected(eRec1.ListMultiplicity)<>Collected(eRec2.ListMultiplicity) then
    return false;
  fi;
  nbIrred:=Length(eRec1.ListIrred);
  ListCorresp:=ListWithIdenticalEntries(nbIrred,0);
  for iIrred in [1..nbIrred]
  do
    WeFind:=false;
    for jIrred in [1..nbIrred]
    do
      EXTred1:=eRec1.ListIrred[iIrred];
      EXTred2:=eRec2.ListIrred[jIrred];
      eTestEquiv:=TestProjectiveIsomorphy(EXTred1, EXTred2);
      if eTestEquiv<>false then
        ListCorresp[iIrred]:=jIrred;
        WeFind:=true;
        if Length(eRec1.ListMultiplicity[iIrred])<>Length(eRec2.ListMultiplicity[jIrred]) then
          return false;
        fi;
      fi;
    od;
    if WeFind=false then
      return false;
    fi;
  od;
  if PermList(ListCorresp)=fail then
    Error("Error in computation of correspondences");
  fi;
  eList:=ListWithIdenticalEntries(nbVert,0);
  for iIrred in [1..nbIrred]
  do
    jIrred:=ListCorresp[iIrred];
    len:=Length(eRec1.ListMultiplicity[iIrred]);
    for i in [1..len]
    do
      iConn1:=eRec1.ListMultiplicity[iIrred][i];
      iConn2:=eRec2.ListMultiplicity[jIrred][i];
      eConn1:=eRec1.ListListIdx[iConn1];
      eConn2:=eRec2.ListListIdx[iConn2];
      lenConn:=Length(eConn1);
      eTestEquiv:=TestProjectiveIsomorphy(eRec1.ListEXTred[iConn1], eRec2.ListEXTred[iConn2]);
      if eTestEquiv=false then
        Error("Something is very wrong");
      fi;
      for iPt in [1..lenConn]
      do
        jPt:=OnPoints(iPt, eTestEquiv);
        iVert1:=eConn1[iPt];
        iVert2:=eConn2[jPt];
        eList[iVert1]:=iVert2;
      od;
    od;
  od;
  TheSigma:=PermList(eList);
  if TestProjectiveEquivalence(EXT1, EXT2, TheSigma).reply=false then
    Error("We have some errors to solve in the code");
  fi;
  return TheSigma;
end;



GetIntermediateGroup:=function(TheSubGroup, TheSuperGroup, FuncMembership)
  local eDCS, ListGens, eRepr, ListDCS;
  ListGens:=[];
  ListDCS:=DoubleCosets(TheSuperGroup, TheSubGroup, TheSubGroup);
#  Print("|ListDCS|=", Length(ListDCS), "\n");
  for eDCS in ListDCS
  do
    eRepr:=Representative(eDCS);
    if FuncMembership(eRepr)=true then
      Add(ListGens, eRepr);
    fi;
  od;
  Append(ListGens, GeneratorsOfGroup(TheSubGroup));
  return Group(ListGens);
end;

GetIntermediateGroup_V2:=function(TheSubGroup, TheSuperGroup, FuncMembership)
  local TheListGens, GRP, LDCS, IsFinished, nbDCS, iDCS, eRepr;
  TheListGens:=ShallowCopy(GeneratorsOfGroup(TheSubGroup));
  GRP:=Group(TheListGens);
  while(true)
  do
    LDCS:=DoubleCosets(TheSuperGroup, GRP, GRP);
    IsFinished:=true;
    nbDCS:=Length(LDCS);
    for iDCS in [1..nbDCS]
    do
      eRepr:=Representative(LDCS[iDCS]);
      if FuncMembership(eRepr)=true then
        if not(eRepr in GRP) then
          Add(TheListGens, eRepr);
          GRP:=Group(TheListGens);
          IsFinished:=false;
          break;
        fi;
      fi;
    od;
    if IsFinished=true then
      break;
    fi;
  od;
  return GRP;
end;





GetKskelGroup:=function(EXT, TheLinearGroup, nbNautyLevels, nbInternLevels)
  local SPAN_function, LISTINFOS, ListSizes, ThePartition, nb, i, TotalSize, TheGRA, eOrb, O, eSet, eElt, RetGRP, RelevantFamily, iLevel, TheSpann, FuncMembership;
  SPAN_function:=function(face, TheStab, EXTwork)
    return SPAN_face_LinearProgramming(face, TheStab, EXTwork, TheLinearGroup, []);
  end;
  LISTINFOS:=KernelSkeletonSearch(TheLinearGroup, EXT, nbNautyLevels+1, SPAN_function);
  ListSizes:=[];
  ThePartition:=[];
  nb:=0;
  for i in [0..nbNautyLevels]
  do
    TotalSize:=Sum(LISTINFOS[i+1].ListSizes);
    Add(ListSizes, TotalSize);
    Add(ThePartition, [nb+1..nb+TotalSize]);
    nb:=nb+TotalSize;
  od;
  # if nbNautyLevels=1 then we can just take the graph instead of
  # the bipartite graph.
  TheGRA:=NullGraph(Group(()), Sum(ListSizes));
  nb:=0;
  for i in [1..nbNautyLevels]
  do
    for eOrb in LISTINFOS[i+1].ListRepresentent
    do
      O:=Orbit(TheLinearGroup, eOrb, OnSets);
      for eSet in O
      do
        nb:=nb+1;
        for eElt in eSet
        do
          AddEdgeOrbit(TheGRA, [eElt, Length(EXT)+nb]);
          AddEdgeOrbit(TheGRA, [Length(EXT)+nb, eElt]);
        od;
      od;
    od;
  od;
  RetGRP:=SymmetryGroupVertexColoredGraph(TheGRA, ThePartition);
  RelevantFamily:=LISTINFOS[nbNautyLevels+1].ListRepresentent;
  for iLevel in [1..nbInternLevels]
  do
    TheSpann:=SPAN_K_Faces(TheLinearGroup, RelevantFamily, EXT, SPAN_function);
    FuncMembership:=function(ePerm)
      local IsItInImage, eSet, fSet;
      IsItInImage:=function(fSet)
        local lSet, g;
        for lSet in TheSpann.ListRepresentent
        do
          g:=RepresentativeAction(TheLinearGroup, lSet, fSet, OnSets);
          if g<>fail then
            return true;
          fi;
        od;
        return false;
      end;
      for eSet in TheSpann.ListRepresentent
      do
        fSet:=OnSets(eSet, ePerm);
        if IsItInImage(fSet)=false then
          return false;
        fi;
      od;
      return true;
    end;
    RetGRP:=GetIntermediateGroup(TheLinearGroup, RetGRP, FuncMembership);
    RelevantFamily:=TheSpann.ListRepresentent;
  od;
  return RetGRP;
end;

GetCombinatorialGroup:=function(EXT, TheLinearGroup, TheSuperGroup)
  local O, FuncMembership;
  O:=DualDescriptionStandard(EXT, TheLinearGroup);
  FuncMembership:=function(ePerm)
    local IsItInImage, eSet, fSet;
    IsItInImage:=function(fSet)
      local lSet, g;
      for lSet in O
      do
        g:=RepresentativeAction(TheLinearGroup, lSet, fSet, OnSets);
        if g<>fail then
          return true;
        fi;
      od;
      return false;
    end;
    for eSet in O
    do
      fSet:=OnSets(eSet, ePerm);
      if IsItInImage(fSet)=false then
        return false;
      fi;
    od;
    return true;
  end;
  return GetIntermediateGroup(TheLinearGroup, TheSuperGroup, FuncMembership);
end;


GetProjectiveGroupNonDecomposable:=function(EXT)
  local EXTred, eRecDecomp, GRPlin, LORB, ListSets, eOrb, GRPcomb, FuncMembership;
  EXTred:=ColumnReduction(EXT).EXT;
  eRecDecomp:=DirectSumDecompositionPolyhedralCone(EXTred);
  if Length(eRecDecomp.ListConn)> 1 then
    Error("The polytope is decomposable and that is not allowed");
  fi;
  GRPlin:=__TheCore_Automorphism(EXTred);
  LORB:=DualDescriptionStandard(EXTred, GRPlin);
  ListSets:=[];
  for eOrb in LORB
  do
    Append(ListSets, Orbit(GRPlin, eOrb, OnSets));
  od;
  GRPcomb:=SetFamilyGroup(Length(EXTred), ListSets);
  FuncMembership:=function(ePerm)
    return KernelTestProjectiveEquivalence(EXTred, EXTred, ePerm).reply;
  end;
  return GetIntermediateGroup(GRPlin, GRPcomb, FuncMembership);
end;

ProjPolytope_Automorphism:=function(EXT)
  local EXTred, nbVert, eRecDecomp, ListGenerators, nbConn, ListConnStatus, iConn, jConn, EXTred1, EXTred2, nbVertSmall, eTestEquiv, eList, iVert, jVert, iVertSmall, jVertSmall, EXTredSmall, GRPproj, eGen;
  EXTred:=ColumnReduction(EXT).EXT;
  nbVert:=Length(EXTred);
  eRecDecomp:=DirectSumDecompositionPolyhedralCone(EXTred);
  ListGenerators:=[];
  nbConn:=Length(eRecDecomp.ListConn);
  ListConnStatus:=ListWithIdenticalEntries(nbConn, 1);
  for iConn in [1..nbConn-1]
  do
    if ListConnStatus[iConn]=1 then
      for jConn in [iConn+1..nbConn]
      do
        EXTred1:=eRecDecomp.ListEXTred[iConn];
        EXTred2:=eRecDecomp.ListEXTred[jConn];
        nbVertSmall:=Length(EXTred1);
        eTestEquiv:=TestProjectiveIsomorphy(EXTred1, EXTred2);
        if eTestEquiv<>false then
          ListConnStatus[jConn]:=0;
          eList:=ListWithIdenticalEntries(nbVert, 0);
          for iVert in [1..nbVert]
          do
            eList[iVert]:=iVert;
          od;
          for iVertSmall in [1..nbVertSmall]
          do
            jVertSmall:=OnPoints(iVertSmall, eTestEquiv);
            iVert:=eRecDecomp.ListListIdx[iConn][iVertSmall];
            jVert:=eRecDecomp.ListListIdx[jConn][jVertSmall];
            eList[iVert]:=jVert;
            eList[jVert]:=iVert;
          od;
          Add(ListGenerators, PermList(eList));
        fi;
      od;
    fi;
  od;
  for iConn in [1..nbConn]
  do
    if ListConnStatus[iConn]=1 then
      EXTredSmall:=eRecDecomp.ListEXTred[iConn];
      nbVertSmall:=Length(EXTredSmall);
      GRPproj:=GetProjectiveGroupNonDecomposable(EXTredSmall);
      for eGen in GeneratorsOfGroup(GRPproj)
      do
        eList:=ListWithIdenticalEntries(nbVert, 0);
        for iVert in [1..nbVert]
        do
          eList[iVert]:=iVert;
        od;
        for iVertSmall in [1..nbVertSmall]
        do
          jVertSmall:=OnPoints(iVertSmall, eGen);
          iVert:=eRecDecomp.ListListIdx[iConn][iVertSmall];
          jVert:=eRecDecomp.ListListIdx[iConn][jVertSmall];
          eList[iVert]:=jVert;
        od;
        Add(ListGenerators, PermList(eList));
      od;
    fi;
  od;
  for eGen in ListGenerators
  do
    if TestProjectiveEquivalence(EXT, EXT, eGen).reply=false then
      Error("We have some errors in the projective code");
    fi;
  od;
  return Group(ListGenerators);
end;
