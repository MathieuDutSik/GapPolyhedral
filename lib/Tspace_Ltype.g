#
# this is correct, despite the fact that Lspace is different.
# the needs are different.
RigidityDegree:=function(ListOrbitDelaunay, eCase)
  local DimInvForm, ListEqualities, eOrb;
  ListEqualities:=[];
  for eOrb in ListOrbitDelaunay
  do
    Append(ListEqualities, ListEqualitiesDelaunay(eOrb.EXT, eCase.Basis));
  od;
  return Length(eCase.Basis)-RankMat(ListEqualities);
end;



RandomPrimitiveElement:=function(eCase, PathInitial, IsSaving)
  local nbTry, DelCO, TheGramMat, RigidityKillingDelaunay, KillingAdjacency, iter, MaximalMemorySave, DimSpace;
  nbTry:=0;
  DimSpace:=Length(eCase.Basis);
  RigidityKillingDelaunay:=function(EXT_Delaunay)
    local pos, ListEqua;
    ListEqua:=ListEqualitiesDelaunay(EXT_Delaunay, eCase.Basis);
    pos:=First(ListEqua, x->x<>ListWithIdenticalEntries(DimSpace+1, 0));
    if pos<>fail then
      Print("Kill with a |EXT|=", Length(EXT_Delaunay), "\n");
      return true;
    fi;
    return false;
  end;
  KillingAdjacency:=function(EXT1, EXT2)
    return false;
  end;
  MaximalMemorySave:=false;
  while(true)
  do
    TheGramMat:=RandomPositiveElementFixedSymmetry(eCase);
    for iter in [1..12]
    do
      DelCO:=DelaunayDescriptionStandardKernel(TheGramMat, eCase.SymmGrpPtWs, PathInitial, IsSaving, RigidityKillingDelaunay, KillingAdjacency, MaximalMemorySave);
      if DelCO<>"fail by Delaunay" then
        return rec(GramMat:=TheGramMat, DelCO:=DelCO);
      fi;
      TheGramMat:=TheGramMat+eCase.SuperMat;
    od;
    nbTry:=nbTry+1;
    Print("failure at try Nr.", nbTry, "  retrying...\n");
  od;
end;




Periodic_RandomPrimitiveElement:=function(eCase, PathInitial, IsSaving)
  local nbTry, DelCO, TheGramMat, RigidityKillingDelaunay, KillingAdjacency, iter, ListGens, MatrixGRP, DimSpace;
  nbTry:=0;
  DimSpace:=Length(eCase.Basis);
  RigidityKillingDelaunay:=function(EXT_Delaunay)
    local pos, ListEqua;
    ListEqua:=ListEqualitiesDelaunay(EXT_Delaunay, eCase.Basis);
    pos:=First(ListEqua, x->x<>ListWithIdenticalEntries(DimSpace+1, 0));
    if pos<>fail then
      Print("Kill with a |EXT|=", Length(EXT_Delaunay), "\n");
      return "fail by Delaunay";
    fi;
    return false;
  end;
  KillingAdjacency:=function(EXT1, EXT2)
    return false;
  end;
  ListGens:=List(GeneratorsOfGroup(eCase.SymmGrpPtWs), x->AffineExtensionPreservingCosetStructure(eCase.ListCosets, x));
  MatrixGRP:=Group(ListGens);
  while(true)
  do
    TheGramMat:=RandomPositiveElementFixedSymmetry(eCase);
    for iter in [1..12]
    do
      DelCO:=Periodic_DelaunayDescriptionStandardKernel(TheGramMat, MatrixGRP, eCase.ListCosets, PathInitial, IsSaving, RigidityKillingDelaunay, KillingAdjacency);
      Print("DelCO=", DelCO, "\n");
      if DelCO<>"fail by Delaunay" then
        return rec(GramMat:=TheGramMat, DelCO:=DelCO);
      fi;
      TheGramMat:=TheGramMat+eCase.SuperMat;
    od;
    nbTry:=nbTry+1;
    Print("failure at try Nr.", nbTry, "  retrying...\n");
  od;
end;





# this function returns a primitive Tspace Ltype that
# contain the SuperMat in its neighborhood.
RandomPrimitiveElementNeighborhood:=function(eCase, PathInitial, IsSaving)
  local nbTry, DelCO, TheGramMat, KillingDelaunay, KillingAdjacency, W, Coeff, DimSpace;
  nbTry:=0;
  DimSpace:=Length(eCase.Basis);
  W:=BasisExpansion(eCase.Basis, eCase.SuperMat);
  KillingDelaunay:=function(EXT_Delaunay)
    local SetEqualities, eVect;
    SetEqualities:=Set(ListEqualitiesDelaunay(EXT_Delaunay, eCase.Basis));
    for eVect in SetEqualities
    do
      if eVect*W=0 then
        if eVect<>ListWithIdenticalEntries(DimSpace, 0) then
          return true;
        fi;
      fi;
    od;    
    return false;
  end;
  KillingAdjacency:=function(EXT1, EXT2)
    local ExtractedBasis, eVert, RedIneq;
    ExtractedBasis:=RowReduction(EXT1, Length(EXT1[1])).EXT;
    eVert:=Difference(Set(EXT2), Set(EXT1))[1];
    RedIneq:=VoronoiLinearInequality(ExtractedBasis, eVert, eCase.Basis);
    if RedIneq*W<0 then
      return true;
    fi;
    return false;
  end;
  Coeff:=1;
  while(true)
  do
    TheGramMat:=RandomPositiveElementFixedSymmetry(eCase);
    while(true)
    do
      DelCO:=DelaunayDescriptionStandardKernel(TheGramMat, eCase.SymmGrpPtWs, PathInitial, IsSaving, KillingDelaunay, KillingAdjacency);
      if DelCO="fail by Delaunay" then
        break;
      fi;
      if DelCO<>"fail by Adjacency" then
        return rec(GramMat:=TheGramMat, DelCO:=DelCO);
      fi;
      TheGramMat:=TheGramMat+Coeff*eCase.SuperMat;
      Coeff:=Coeff+1;
      nbTry:=nbTry+1;
      Print("failure by Adjacency at try Nr.", nbTry, "  retrying...\n");
    od;
    nbTry:=nbTry+1;
    Print("failure by Delaunay at try Nr.", nbTry, "  retrying...\n");
  od;
end;








FindRepartitionningInfoNextGeneration:=function(eIdx, ListOrbitDelaunay, ListInformationsOneFlipping, InteriorElement, DataPolyhedralTiling)
  local n, ListPermGenList, ListMatGens, StandardGroupUpdate, PermGRP, MatGRP, phi, ListVertices, ListOrbitCenter, FuncInsertVertex, FuncInsertGenerator, FuncInsertCenter, IsFinished, nbCent, iCent, eEnr, eCase, iComp, TotalListVertices, eVert, eVertRed, HeightVert, ListOrbitFacet, eRec, iOrb, RenormStabilizer, ListAdj, LEV, eAdj, jInc, iInc, nbOrb, eFac, TheStab, FuncInsertFacet, FAC, Stab, CP, RepartIsRespawn, RepartIsBankSave, RepartPath, RepartPathBank, RepartPathTmp, Data, BF, FuncStabilizer, FuncIsomorphy, FuncInvariant, TheSet;
  n:=Length(ListOrbitDelaunay[1].EXT[1])-1;
  ListPermGenList:=[];
  ListMatGens:=[];
  StandardGroupUpdate:=function()
    local ListGen;
    ListGen:=List(ListPermGenList, x->PermList(x));
    PermGRP:=PersoGroupPerm(ListGen);
    MatGRP:=PersoGroupMatrix(ListMatGens, n+1);
    phi:=GroupHomomorphismByImagesNC(PermGRP, MatGRP, ListGen, ListMatGens);
  end;
  StandardGroupUpdate();
  ListVertices:=[];
  ListOrbitCenter:=[];
  FuncInsertVertex:=function(eVert)
    local O, ADDL, iGen;
    if Position(ListVertices, eVert)=fail then
      O:=Orbit(MatGRP, eVert, OnPoints);
      Append(ListVertices, O);
      for iGen in [1..Length(ListPermGenList)]
      do
        ADDL:=List(O, x->Position(ListVertices, x*ListMatGens[iGen]));
        Append(ListPermGenList[iGen], ADDL);
      od;
    fi;
  end;
  FuncInsertGenerator:=function(eMat)
    local eList, testBelong, GRPlocal, ListVert, eVert, Lstat, i, j, g;
    eList:=List(ListVertices, x->Position(ListVertices, x*eMat));
    if Position(eList, fail)<>fail then
      testBelong:=false;
      GRPlocal:=Group(Union(Set(ListMatGens), [eMat]));
      ListVert:=Union(List(ListVertices, x->Set(Orbit(GRPlocal, x, OnPoints))));
      for eVert in ListVert
      do
        FuncInsertVertex(eVert);
      od;
    else
      testBelong:=PermList(eList) in PermGRP;
    fi;
    if testBelong=false then
      eList:=List(ListVertices, x->Position(ListVertices, x*eMat));
      Add(ListMatGens, eMat);
      Add(ListPermGenList, eList);
      StandardGroupUpdate();
    fi;
  end;
  FuncInsertCenter:=function(TheRec)
    local LVert, eVert, iOrbFound, iOrb, eGen, eBigMat, Linc;
    LVert:=List(ListOrbitDelaunay[TheRec.iDelaunay].EXT, x->x*TheRec.eBigMat);
    for eVert in LVert
    do
      FuncInsertVertex(eVert);
    od;
    StandardGroupUpdate();
    iOrbFound:=0;
    for iOrb in [1..Length(ListOrbitCenter)]
    do
      if ListOrbitCenter[iOrb].iDelaunay=TheRec.iDelaunay then
        iOrbFound:=iOrb;
      fi;
    od;
    if iOrbFound=0 then
      for eGen in GeneratorsOfGroup(ListOrbitDelaunay[TheRec.iDelaunay].TheStab.PermutationStabilizer)
      do
        eBigMat:=Image(ListOrbitDelaunay[TheRec.iDelaunay].TheStab.PhiPermMat, eGen);
        FuncInsertGenerator(Inverse(TheRec.eBigMat)*eBigMat*TheRec.eBigMat);
      od;
      Linc:=List(LVert, x->Position(ListVertices, x));
      Add(ListOrbitCenter, rec(iDelaunay:=TheRec.iDelaunay, eBigMat:=TheRec.eBigMat, Status:="NO", Linc:=Linc, EXT:=LVert));
    else
      FuncInsertGenerator(Inverse(TheRec.eBigMat)*ListOrbitCenter[iOrbFound].eBigMat);
    fi;
  end;
  FuncInsertCenter(rec(iDelaunay:=eIdx, eBigMat:=IdentityMat(n+1,0)));
  while(true)
  do
    IsFinished:=true;
    nbCent:=Length(ListOrbitCenter);
    for iCent in [1..nbCent]
    do
      eEnr:=ListOrbitCenter[iCent];
      if eEnr.Status="NO" then
        IsFinished:=false;
        eEnr.Status:="YES";
        for eCase in ListInformationsOneFlipping
        do
          if eEnr.iDelaunay=eCase.Input then
            FuncInsertCenter(rec(iDelaunay:=eCase.iDelaunay, eBigMat:=eCase.eBigMat*eEnr.eBigMat));
          fi;
        od;
      fi;
    od;
    if IsFinished=true then
      break;
    fi;
  od;
  # second part, the convex decomposition
  TotalListVertices:=[];
  for eVert in ListVertices
  do
    eVertRed:=eVert{[2..n+1]};
    HeightVert:=eVertRed*InteriorElement*eVertRed;
    Add(TotalListVertices, Concatenation(eVert, [HeightVert]));
  od;
  if RankMat(TotalListVertices)<Length(TotalListVertices[1]) then
    Error("TotalListVertices is not full dimensional");
  fi;
  ListOrbitFacet:=[];
  RenormStabilizer:=function(Stab)
    local PermGen, MatrixGen, eGen, TheList, iVert, h1, h2, fGen, eMat, GRPperm, GRPmat, PhiPermMat;
    PermGen:=[];
    MatrixGen:=[];
    for eGen in GeneratorsOfGroup(Stab)
    do
      TheList:=[];
      for iVert in [1..Length(ListOrbitFacet[iOrb].Linc)]
      do
        h1:=ListOrbitFacet[iOrb].Linc[iVert];
        h2:=OnPoints(h1, eGen);
        Add(TheList, Position(ListOrbitFacet[iOrb].Linc, h2));
      od;
      fGen:=PermList(TheList);
      Add(PermGen, fGen);
      eMat:=Image(phi, eGen);
      Add(MatrixGen, eMat);
    od;
    GRPperm:=PersoGroupPerm(PermGen);
    GRPmat:=PersoGroupMatrix(MatrixGen, n+1);
    PhiPermMat:=GroupHomomorphismByImagesNC(GRPperm, GRPmat, PermGen, MatrixGen);
    return rec(PermutationStabilizer:=GRPperm, PhiPermMat:=PhiPermMat);
  end;
  for iComp in [1..Length(ListOrbitCenter)]
  do
    eRec:=ListOrbitCenter[iComp];
    Add(ListOrbitFacet, rec(eFac:=FindFacetInequality(TotalListVertices, eRec.Linc), Linc:=eRec.Linc, EXT:=eRec.EXT, Status:="NO", Position:="lower", iDelaunayOrigin:=eRec.iDelaunay, eBigMat:=eRec.eBigMat));
  od;
  FuncInsertFacet:=function(eFac)
    local Linc, EXT, iVert, iOrb, g, ThePos;
    Linc:=Filtered([1..Length(ListVertices)], x->TotalListVertices[x]*eFac=0);
    EXT:=ListVertices{Linc};
    for iOrb in [1..Length(ListOrbitFacet)]
    do
      g:=RepresentativeAction(PermGRP, ListOrbitFacet[iOrb].Linc, Linc, OnSets);
      if g<>fail then
        return rec(iOrb:=iOrb, eBigMat:=Image(phi, g));
      fi;
    od;
    if eFac[Length(eFac)]=0 then
      ThePos:="barrel";
    else
      ThePos:="higher";
    fi;
    Add(ListOrbitFacet, rec(eFac:=eFac, EXT:=EXT, Linc:=Linc, Status:="NO", Position:=ThePos));
#    Print("New facet(Delaunay):  |V|=", Length(EXT), "  Pos=", ThePos, "\n");
    return rec(iOrb:=Length(ListOrbitFacet), eBigMat:=IdentityMat(n+1));
  end;
  FuncStabilizer:=function(EXT)
    local ListInc, GRP, ListGen, eGen;
    ListInc:=List(EXT, x->Position(TotalListVertices, x));
    if Length(ListInc) < 30 then
      return Group(());
    fi;
    GRP:=Stabilizer(PermGRP, ListInc, OnSets);
    ListGen:=[];
    for eGen in GeneratorsOfGroup(GRP)
    do
      Add(ListGen, PermList(List(ListInc, x->Position(ListInc, OnPoints(x, eGen)))));
    od;
    return PersoGroupPerm(ListGen);
  end;
  FuncIsomorphy:=function(EXT1, EXT2)
    local ListInc1, ListInc2, ePerm;
    ListInc1:=List(EXT1, x->Position(TotalListVertices, x));
    ListInc2:=List(EXT2, x->Position(TotalListVertices, x));
    ePerm:=RepresentativeAction(PermGRP, ListInc1, ListInc2, OnSets);
    if ePerm=fail then
      return false;
    else
      return PermList(List(ListInc1, x->Position(ListInc2, OnPoints(x, ePerm))));
    fi;
  end;
  FuncInvariant:=function(EXT)
    return Length(EXT);
  end;
  RepartPathBank:=Concatenation(DataPolyhedralTiling.PathSAVE, "TheBank/");
  Exec("mkdir -p ", RepartPathBank);
  RepartPathTmp:=Concatenation(DataPolyhedralTiling.PathSAVE, "tmp/");
  Exec("mkdir -p ", RepartPathTmp);
  BF:=BankRecording(rec(Saving:=DataPolyhedralTiling.Saving, BankPath:=RepartPathBank), FuncStabilizer, FuncIsomorphy, FuncInvariant, OnSetsGroupFormalism(500));
  RepartIsBankSave:=function(EllapsedTime, OrdGRP, EXT, TheDepth)
    if TheDepth=0 then
      return false;
    fi;
    if Length(EXT)<=n+4 then
      return false;
    fi;
    return true;
  end;
  RepartIsRespawn:=function(OrdGRP, EXT, TheDepth)
    if Length(EXT)>100 then
      return true;
    fi;
    if TheDepth>=2 then
      return false;
    fi;
    if OrdGRP<=600 then
      return false;
    fi;
    if Length(EXT)<=60 then
      return false;
    fi;
    return true;
  end;
  Data:=rec(TheDepth:=0, ThePath:=RepartPathTmp,
            IsBankSave:=RepartIsBankSave, 
            IsRespawn:=RepartIsRespawn,
            GetInitialRays:=GetInitialRays_LinProg,
            Saving:=false,
            DualDescriptionFunction:=DataPolyhedralTiling.DualDescriptionFunction, 
            GroupFormalism:=OnSetsGroupFormalism(500), 
            ThePathSave:="/irrelevant/");
  while(true)
  do
    IsFinished:=true;
    nbOrb:=Length(ListOrbitFacet);
    for iOrb in [1..nbOrb]
    do
      if ListOrbitFacet[iOrb].Status="NO" then
        TheSet:=Set(ListOrbitFacet[iOrb].Linc);
        Stab:=Stabilizer(PermGRP, TheSet, OnSets);
        TheStab:=RenormStabilizer(Stab);
        ListOrbitFacet[iOrb].TheStab:=TheStab;
        ListOrbitFacet[iOrb].Size:=Order(PermGRP)/Order(TheStab.PermutationStabilizer);
        ListAdj:=[];
        FAC:=ListAdjacentOrbitwise_Facet(TotalListVertices, Stab, TheSet, Data, BF);
        for eFac in FAC
        do
          eAdj:=FuncInsertFacet(eFac);
          LEV:=[];
          for iInc in [1..Length(ListOrbitFacet[iOrb].Linc)]
          do
            jInc:=ListOrbitFacet[iOrb].Linc[iInc];
            if TotalListVertices[jInc]*eFac=0 then
              Add(LEV, iInc);
            fi;
          od;
          eAdj.eInc:=LEV;
          Add(ListAdj, eAdj);
        od;
        ListOrbitFacet[iOrb].ListAdj:=ListAdj;
        ListOrbitFacet[iOrb].Status:="YES";
        IsFinished:=false;
      fi;
    od;
    if IsFinished=true then
      break;
    fi;
  od;
  for iOrb in [1..Length(ListOrbitFacet)]
  do
    Unbind(ListOrbitFacet[iOrb].eFac);
    Unbind(ListOrbitFacet[iOrb].Linc);
  od;
  BF.FuncClearAccount();
#  Print("|Sym|=", Order(PermGRP) );
#  Print("  Repart |V|=", Length(ListVertices));
  return ListOrbitFacet;
end;











#
#
# InteriorElement is a GramMatrix, it must be the one from which 
# ListOrbitDelaunay was created.
FlippingLtype:=function(ListOrbitDelaunay, InteriorElement, ListInformationsOneFlipping, DataPolyhedralTiling)
  local Gra, n, ListMatched, eCase, eSet, ListConn, ListGroupMelt, ListGroupUnMelt, RepartInfo, INTS, eConn, ListInformationCenter, ListVertices, SYMGRP, LORB, ListInfo, NewListOrbitDelaunay, eRec, iDelaunay, iInfo, iOrb, i,
DataTheEquivariantLtypeDomain, ListAdj, TheDATA, TheHistory, eAdj, TheOrb, TheOrbFacet, iDelaunayOld, Pos, iter, eMat2, eTrans2, BigMat2, AdjacentDelaunayCenterOld, iFacet, eFacet, EXT2, TheMat, g, TheFoundAdj, fAdj, Linc, eExt, iInc, iOrbFound, test, jFacet,
  WSR, WSR2, TheMat2, TheMat3, ImageEXT, LLinc, TheFoundAdj2, TheFoundAdj3, LincEXT, iV, eMat1, ImageEXTbarrel, kFacet, iDelaunayOrigin, jDelaunayOrigin, LLinc2, gAdj, hAdj, eMat3, EXT1, EXT3, EXT4, EXT5, EXT6, EXT7, LLinc3, iConn, jInfo, iFacet2, tAdj, LLinc4, BigMat1,
  TheFoundAdj4, TheMat4, TheFoundAdj1, TheMat1, jDelaunayOld, Pos2, ListCenterLow, ListCenterUpp, LORB2, ListCenterLow2, ListCenterUpp2;
  n:=Length(ListOrbitDelaunay[1].EXT[1])-1;
  Gra:=NullGraph(Group(()), Length(ListOrbitDelaunay));
  ListMatched:=[];
  for eCase in ListInformationsOneFlipping
  do
    eSet:=[eCase.Input, eCase.iDelaunay];
    Append(ListMatched, eSet);
    if eCase.Input<>eCase.iDelaunay then
      AddEdgeOrbit(Gra, eSet);
      AddEdgeOrbit(Gra, Reversed(eSet));
    fi;
  od;
  ListMatched:=Set(ListMatched);
  ListConn:=ConnectedComponents(Gra);
  ListGroupMelt:=[];
  ListGroupUnMelt:=[];
  # this code take care of the cases of RepartitionningDelaunay
  # being composed of only one orbit of Delaunay.
  for eConn in ListConn
  do
    if Length(Intersection(eConn, ListMatched))>0 then
      Add(ListGroupMelt, eConn);
    else
      Add(ListGroupUnMelt, eConn);
    fi;
  od;
  ListInfo:=[];
#  Print("Beginning the flipping operation\n");
  for eConn in ListGroupMelt
  do
    LORB2:=FindRepartitionningInfoNextGeneration(eConn[1], ListOrbitDelaunay, ListInformationsOneFlipping, InteriorElement, DataPolyhedralTiling);
    ListCenterLow2:=[];
    ListCenterUpp2:=[];
    for eFacet in LORB2
    do
      if eFacet.Position="lower" then
        Add(ListCenterLow2, eFacet.Size);
      fi;
      if eFacet.Position="higher" then
        Add(ListCenterUpp2, eFacet.Size);
      fi;
    od;
#    Print("  low=", ListCenterLow2, "  upp=", ListCenterUpp2, "\n");
    Add(ListInfo, LORB2);
  od;
  #
  NewListOrbitDelaunay:=[];
  for eConn in ListGroupUnMelt
  do
    if Length(eConn)<>1 then
      Error("Error of connected component computation");
    fi;
    iDelaunay:=eConn[1];
    Add(NewListOrbitDelaunay, ["old", iDelaunay]);
  od;
  for iInfo in [1..Length(ListInfo)]
  do
    for iFacet in [1..Length(ListInfo[iInfo])]
    do
      TheOrbFacet:=ListInfo[iInfo][iFacet];
      if TheOrbFacet.Position="higher" then
        Add(NewListOrbitDelaunay, ["new", iInfo, iFacet]);
      fi;
    od;
  od;
  #
  DataTheEquivariantLtypeDomain:=[];
  for iOrb in [1..Length(NewListOrbitDelaunay)]
  do
    TheHistory:=NewListOrbitDelaunay[iOrb];
    if TheHistory[1]="old" then
      iDelaunay:=TheHistory[2];
      TheDATA:=rec(EXT:=ListOrbitDelaunay[iDelaunay].EXT, TheStab:=ListOrbitDelaunay[iDelaunay].TheStab);
    else
      iInfo:=TheHistory[2];
      iFacet:=TheHistory[3];
      TheDATA:=rec(EXT:=ListInfo[iInfo][iFacet].EXT, TheStab:=ListInfo[iInfo][iFacet].TheStab);
    fi;
    Add(DataTheEquivariantLtypeDomain, TheDATA);
  od;
  #
#  Print("Treating the adjacency story\n");
  for iOrb in [1..Length(NewListOrbitDelaunay)]
  do
    TheHistory:=NewListOrbitDelaunay[iOrb];
    ListAdj:=[];
    if TheHistory[1]="old" then
      iDelaunay:=TheHistory[2];
      for eAdj in ListOrbitDelaunay[iDelaunay].Adjacencies
      do
        iDelaunayOld:=eAdj.iDelaunay;
        Pos:=Position(ListGroupUnMelt, [iDelaunayOld]);
        if Pos<>fail then
          Add(ListAdj, rec(eBigMat:=eAdj.eBigMat, iDelaunay:=Pos, eInc:=eAdj.eInc, Input:=iOrb));
          if Intersection(Set(List(DataTheEquivariantLtypeDomain[Pos].EXT, u->u*eAdj.eBigMat)), Set(DataTheEquivariantLtypeDomain[iOrb].EXT))<>Set(DataTheEquivariantLtypeDomain[iOrb].EXT{eAdj.eInc}) then
            Error("We have an error. Cass 1");
          fi;
        else
          for iConn in [1..Length(ListGroupMelt)]
          do
            eConn:=ListGroupMelt[iConn];
            if Position(eConn, iDelaunayOld)<>fail then
              iInfo:=iConn;
            fi;
          od;
          for i in [1..Length(ListInfo[iInfo])]
          do
            if ListInfo[iInfo][i].Position="lower" then
              if ListInfo[iInfo][i].iDelaunayOrigin=iDelaunayOld then
                iFacet:=i;
              fi;
            fi;
          od;
          eFacet:=ListInfo[iInfo][iFacet];
          BigMat2:=eFacet.eBigMat;
          ImageEXT:=List(ListOrbitDelaunay[iDelaunayOld].EXT, u->u*eAdj.eBigMat);
          Linc:=Set(List(ListOrbitDelaunay[iDelaunay].EXT{eAdj.eInc}, u->Position(ImageEXT, u)));
          for fAdj in eFacet.ListAdj
          do
            g:=RepresentativeAction(eFacet.TheStab.PermutationStabilizer, fAdj.eInc, Linc, OnSets);
            if g<>fail then
              TheFoundAdj:=fAdj;
              TheMat:=Image(eFacet.TheStab.PhiPermMat, g);
            fi;
          od;
          iOrbFound:=TheFoundAdj.iOrb;
          if ListInfo[iInfo][iOrbFound].Position="barrel" then
            Error("Illogic error concerning the structure of repartitionning polytope");
          fi;
          Pos:=Position(NewListOrbitDelaunay, ["new", iInfo, iOrbFound]);
          BigMat1:=TheFoundAdj.eBigMat*TheMat*Inverse(BigMat2)*eAdj.eBigMat;
          Add(ListAdj, rec(eBigMat:=BigMat1, iDelaunay:=Pos, eInc:=eAdj.eInc, Input:=iOrb));
          if Intersection(Set(List(DataTheEquivariantLtypeDomain[Pos].EXT, u->u*BigMat1)), Set(DataTheEquivariantLtypeDomain[iOrb].EXT))<>Set(DataTheEquivariantLtypeDomain[iOrb].EXT{eAdj.eInc}) then
            Error("We have an error case 2");
          fi;
        fi;
      od;
    else
      iInfo:=TheHistory[2];
      iFacet:=TheHistory[3];
      for eAdj in ListInfo[iInfo][iFacet].ListAdj
      do
        jFacet:=eAdj.iOrb;
        if ListInfo[iInfo][jFacet].Position="barrel" then
          # search mapping
          eMat1:=eAdj.eBigMat;
          LincEXT:=ListInfo[iInfo][iFacet].EXT{eAdj.eInc};
          WSR:=ListInfo[iInfo][jFacet];
          ImageEXTbarrel:=List(WSR.EXT, u->u*eMat1);
          LLinc:=Set(List(LincEXT, u->Position(ImageEXTbarrel, u)));
          # search a lower facet
          Unbind(TheFoundAdj);
          for fAdj in ListInfo[iInfo][jFacet].ListAdj
          do
            if ListInfo[iInfo][fAdj.iOrb].Position="lower" then
              TheFoundAdj:=fAdj;
            fi;
          od;
          kFacet:=TheFoundAdj.iOrb;
          eMat2:=TheFoundAdj.eBigMat;
          iDelaunayOrigin:=ListInfo[iInfo][kFacet].iDelaunayOrigin;
          ImageEXT:=List(ListInfo[iInfo][kFacet].EXT, u->u*TheFoundAdj.eBigMat);
          LLinc2:=Set(List(ListInfo[iInfo][jFacet].EXT{TheFoundAdj.eInc}, u->Position(ImageEXT, u)));
          for gAdj in ListOrbitDelaunay[iDelaunayOrigin].Adjacencies
          do
            g:=RepresentativeAction(ListOrbitDelaunay[iDelaunayOrigin].TheStab.PermutationStabilizer, gAdj.eInc, LLinc2, OnSets);
            if g<>fail then
              TheFoundAdj2:=gAdj;
              TheMat2:=Image(ListOrbitDelaunay[iDelaunayOrigin].TheStab.PhiPermMat, g);
            fi;
          od;
          # analysing the adjacent old Delaunay
          jDelaunayOrigin:=TheFoundAdj2.iDelaunay;
          eMat3:=TheFoundAdj2.eBigMat;
          ImageEXT:=List(ListOrbitDelaunay[jDelaunayOrigin].EXT, u->u*eMat3);
          LLinc3:=Set(List(ListOrbitDelaunay[iDelaunayOrigin].EXT{TheFoundAdj2.eInc}, u->Position(ImageEXT, u)));
          # finding the corresponding barrel facet
          for iConn in [1..Length(ListGroupMelt)]
          do
            if Position(ListGroupMelt[iConn], jDelaunayOrigin)<>fail then
              jInfo:=iConn;
            fi;
          od;
          for i in [1..Length(ListInfo[jInfo])]
          do
            if ListInfo[jInfo][i].Position="lower" then
              if ListInfo[jInfo][i].iDelaunayOrigin=jDelaunayOrigin then
                iFacet2:=i;
              fi;
            fi;
          od;
          for hAdj in ListInfo[jInfo][iFacet2].ListAdj
          do
            g:=RepresentativeAction(ListInfo[jInfo][iFacet2].TheStab.PermutationStabilizer, hAdj.eInc, LLinc3, OnSets);
            if g<>fail then
              TheFoundAdj3:=hAdj;
              TheMat3:=Image(ListInfo[jInfo][iFacet2].TheStab.PhiPermMat, g);
            fi;
          od;
          BigMat1:=TheFoundAdj3.eBigMat*TheMat3*Inverse(ListInfo[jInfo][iFacet2].eBigMat)*eMat3*TheMat2*ListInfo[iInfo][kFacet].eBigMat*eMat2*eMat1;
          EXT7:=List(ListInfo[jInfo][TheFoundAdj3.iOrb].EXT, u->u*BigMat1);
          if Set(EXT7)<>Set(ImageEXTbarrel) then
            Error("we reached a critical error in the barrel image");
          fi;
          LLinc4:=Set(List(LincEXT, u->Position(EXT7, u)));
          for tAdj in ListInfo[jInfo][TheFoundAdj3.iOrb].ListAdj
          do
            g:=RepresentativeAction(ListInfo[jInfo][TheFoundAdj3.iOrb].TheStab.PermutationStabilizer, tAdj.eInc, LLinc4, OnSets);
            if g<>fail then
              TheFoundAdj4:=tAdj;
              TheMat4:=Image(ListInfo[jInfo][TheFoundAdj3.iOrb].TheStab.PhiPermMat, g);
            fi;
          od;
          Pos:=Position(NewListOrbitDelaunay, ["new", jInfo, TheFoundAdj4.iOrb]);
          BigMat2:=TheFoundAdj4.eBigMat*TheMat4*BigMat1;
          Add(ListAdj, rec(eBigMat:=BigMat2, iDelaunay:=Pos, eInc:=eAdj.eInc, Input:=iOrb));
          if Intersection(Set(List(DataTheEquivariantLtypeDomain[Pos].EXT, u->u*BigMat2)), Set(DataTheEquivariantLtypeDomain[iOrb].EXT))<>Set(DataTheEquivariantLtypeDomain[iOrb].EXT{eAdj.eInc}) then
            Error("We have an error case 3");
          fi;
        elif ListInfo[iInfo][jFacet].Position="lower" then
          # the facet jFacet
          iDelaunayOrigin:=ListInfo[iInfo][jFacet].iDelaunayOrigin;
          eMat1:=eAdj.eBigMat;
          ImageEXT:=List(ListInfo[iInfo][jFacet].EXT, u->u*eMat1);
          LLinc:=Set(List(ListInfo[iInfo][iFacet].EXT{eAdj.eInc}, u->Position(ImageEXT, u)));
          for fAdj in ListOrbitDelaunay[iDelaunayOrigin].Adjacencies
          do
            g:=RepresentativeAction(ListOrbitDelaunay[iDelaunayOrigin].TheStab.PermutationStabilizer, fAdj.eInc, LLinc, OnSets);
            if g<>fail then
              TheFoundAdj1:=fAdj;
              TheMat1:=Image(ListOrbitDelaunay[iDelaunayOrigin].TheStab.PhiPermMat, g);
            fi;
          od;
          jDelaunayOld:=TheFoundAdj1.iDelaunay;
          Pos:=Position(ListGroupUnMelt, [jDelaunayOld]);
          # another case splitting
          if Pos<>fail then
            Pos2:=Position(NewListOrbitDelaunay, ["old", jDelaunayOld]);
            BigMat1:=TheFoundAdj1.eBigMat*TheMat1*ListInfo[iInfo][jFacet].eBigMat*eAdj.eBigMat;
            Add(ListAdj, rec(eBigMat:=BigMat1, iDelaunay:=Pos2, eInc:=eAdj.eInc, Input:=iOrb));
            if Intersection(Set(List(DataTheEquivariantLtypeDomain[Pos2].EXT, u->u*BigMat1)), Set(DataTheEquivariantLtypeDomain[iOrb].EXT))<>Set(DataTheEquivariantLtypeDomain[iOrb].EXT{eAdj.eInc}) then
              Error("We have an error case 4");
            fi;
          else
            for iConn in [1..Length(ListGroupMelt)]
            do
              if Position(ListGroupMelt[iConn], jDelaunayOld)<>fail then
                jInfo:=iConn;
              fi;
            od;
            for i in [1..Length(ListInfo[jInfo])]
            do
              if ListInfo[jInfo][i].Position="lower" then
                if ListInfo[jInfo][i].iDelaunayOrigin=jDelaunayOld then
                  iFacet2:=i;
                fi;
              fi;
            od;
            ImageEXT:=List(ListOrbitDelaunay[jDelaunayOld].EXT, u->u*TheFoundAdj1.eBigMat);
            LLinc2:=Set(List(ListOrbitDelaunay[iDelaunayOrigin].EXT{TheFoundAdj1.eInc}, u->Position(ImageEXT, u)));
            Unbind(TheFoundAdj2);
            for gAdj in ListInfo[jInfo][iFacet2].ListAdj
            do
              g:=RepresentativeAction(ListInfo[jInfo][iFacet2].TheStab.PermutationStabilizer, gAdj.eInc, LLinc2, OnSets);
              if g<>fail then
                TheFoundAdj2:=gAdj;
                TheMat2:=Image(ListInfo[jInfo][iFacet2].TheStab.PhiPermMat, g);
              fi;
            od;
            Pos:=Position(NewListOrbitDelaunay, ["new", jInfo, TheFoundAdj2.iOrb]);
            BigMat1:=TheFoundAdj2.eBigMat*TheMat2*Inverse(ListInfo[jInfo][iFacet2].eBigMat)*TheFoundAdj1.eBigMat*TheMat1*ListInfo[iInfo][jFacet].eBigMat*eAdj.eBigMat;
            Add(ListAdj, rec(eBigMat:=BigMat1, iDelaunay:=Pos, eInc:=eAdj.eInc, Input:=iOrb));
            if Intersection(Set(List(DataTheEquivariantLtypeDomain[Pos].EXT, u->u*BigMat1)), Set(DataTheEquivariantLtypeDomain[iOrb].EXT))<>Set(DataTheEquivariantLtypeDomain[iOrb].EXT{eAdj.eInc}) then
              Error("We have an error case 5");
            fi;
          fi;
        else
          Pos:=Position(NewListOrbitDelaunay, ["new", iInfo, jFacet]);
          Add(ListAdj, rec(eBigMat:=eAdj.eBigMat, iDelaunay:=Pos, eInc:=eAdj.eInc, Input:=iOrb));
          if Intersection(Set(List(DataTheEquivariantLtypeDomain[Pos].EXT, u->u*eAdj.eBigMat)), Set(DataTheEquivariantLtypeDomain[iOrb].EXT))<>Set(DataTheEquivariantLtypeDomain[iOrb].EXT{eAdj.eInc}) then
            Error("We have an error case 6");
          fi;
        fi;
      od;
    fi;
    DataTheEquivariantLtypeDomain[iOrb].Adjacencies:=ListAdj;
  od;
#  Print("Flipping operation finished\n");
  return DataTheEquivariantLtypeDomain;
end;



__ListOrbEdges:=function(EXT, GroupExt)
  return Filtered(__RepresentativeOrbitTwoSet(GroupExt, [1..Length(EXT)]), x->TestAdjacency(EXT[x[1]], EXT[x[2]], EXT, []));
end;



DualDescriptionZeroFirst:=function(FAC)
  local len, FACred, EXTred;
  len:=Length(FAC[1]);
  FACred:=List(FAC, x->x{[2..len]});
  EXTred:=DualDescription(FACred);
  return List(EXTred, x->Concatenation([0], x));
end;

OutputToCOOP_PACOOP:=function(FileName, OneLtype, eCase, MaxIte, AbsGap, option, InteriorPt)
  local n, FAC1, EXT2, FAC2, TheSum, eExt, GramMat, output, ListRad, nbDelaunay, eDelaunay, EXTred, CP, EXTp, EXTnew, iExt, jExt, i, MaxRad, nbMat, iMat, eMat, iRow, iCol, nbFac, iEXT, iFac, eFac, expo, TheText, ListStatusFace, ListVector, ListLinearForm, VE, EXT, DDA, FuncInsert, eVect, LRST, ePair, eLine, eCol, TheLcm, ListEXT, ListEXTscaled, TheDiv, TheQuot, ListRadius, eSol, iCase, MaxRadius, ListBasisAsVect, GramMatAsVect, eFrac, eStr;
  n:=Length(eCase.Basis[1]);
  FAC1:=WriteFaceInequalities(OneLtype, eCase);
  EXT2:=DualDescription(FAC1.ListInequalities);
  FAC2:=EliminationByRedundancyCone(FAC1.ListInequalities, EXT2);
  TheSum:=[];
  for eExt in EXT2
  do
    TheSum:=TheSum+eExt;
  od;
  GramMat:=FuncComputeMat(eCase.Basis, TheSum);
  #
  output:=OutputTextFile(FileName, true);
  AppendTo(output, n, "\n\n");
  #
  nbDelaunay:=Length(OneLtype);
  AppendTo(output, nbDelaunay, "\n");
  ListEXT:=[];
  TheLcm:=1;
  for eDelaunay in OneLtype
  do
    EXTred:=RowReduction(eDelaunay.EXT, n+1).EXT;
    EXTp:=List([2..Length(EXTred)], x->EXTred[x]-EXTred[1]);
    EXTnew:=List(EXTp, x->x{[2..n+1]});
    for eLine in EXTnew
    do
      for eCol in eLine
      do
        TheLcm:=LcmInt(TheLcm, DenominatorRat(eCol));
      od;
    od;
    Add(ListEXT, EXTnew);
  od;
  ListEXTscaled:=[];
  for EXTnew in ListEXT
  do
    Add(ListEXTscaled, TheLcm*EXTnew);
    for iEXT in [1..Length(EXTnew)]
    do
      eExt:=TheLcm*EXTnew[iEXT];
      for i in [1..n]
      do
        AppendTo(output, eExt[i], " ");
      od;
      AppendTo(output, "\n");
    od;
    AppendTo(output, "\n");
  od;
  #
  #
  # the orbits of edges of Delaunay
  if option="pacoop" then
    ListVector:=[];
    ListLinearForm:=[];
    FuncInsert:=function(TheVector)
      local eList;
      eList:=List(eCase.Basis, x->TheVector*x*TheVector);
      if Position(ListLinearForm, eList)=fail then
        Add(ListVector, TheVector);
        Add(ListLinearForm, eList);
      fi;
    end;
    for eDelaunay in OneLtype
    do
      LRST:=__ListOrbEdges(eDelaunay.EXT, eDelaunay.TheStab.PermutationStabilizer);
      for ePair in LRST
      do
        VE:=eDelaunay.EXT[ePair[1]]-eDelaunay.EXT[ePair[2]];
        FuncInsert(VE{[2..n+1]});
      od;
    od;
    AppendTo(output, Length(ListVector), "\n");
    WriteMatrix(output, ListVector);
    AppendTo(output, "\n");
  fi;
  #
  #
  #
  nbMat:=Length(eCase.Basis);
  AppendTo(output, nbMat, "\n");
  for iMat in [1..Length(eCase.Basis)]
  do
    eMat:=eCase.Basis[iMat];
    for iRow in [1..n]
    do
      for iCol in [1..iRow]
      do
        AppendTo(output, eMat[iRow][iCol], " ");
      od;
      AppendTo(output, "\n");
    od;
    AppendTo(output, "\n");
  od;
  # dead end status
  nbFac:=Length(FAC2);
  AppendTo(output, nbFac, "\n");
  ListStatusFace:="";
  for eFac in FAC2
  do
    TheSum:=0;
    for eExt in EXT2
    do
      if eFac*eExt=0 then
        TheSum:=TheSum+eExt;
      fi;
    od;
    if RankMat(FuncComputeMat(eCase.Basis, TheSum))=n then
      ListStatusFace:=Concatenation(ListStatusFace, "0 ");
    else
      ListStatusFace:=Concatenation(ListStatusFace, "1 ");
    fi;
  od;
  AppendTo(output, ListStatusFace, "\n");
  for iFac in [1..nbFac]
  do
    eFac:=FAC2[iFac];
    for iCol in [2..nbMat+1]
    do
      AppendTo(output, eFac[iCol], " ");
    od;
    AppendTo(output, "\n");
  od;
  if InteriorPt=1 then
    ListBasisAsVect:=List(eCase.Basis, SymmetricMatrixToVector);
    GramMatAsVect:=SymmetricMatrixToVector(GramMat);
    eSol:=SolutionMat(ListBasisAsVect, GramMatAsVect);
    ListRadius:=[];
    for EXT in ListEXTscaled
    do
      # maybe some change is to be done here
      EXTnew:=List(EXT, x->Concatenation([1], x));
      CP:=CenterRadiusDelaunayPolytopeGeneral(GramMat, EXTnew);
      Add(ListRadius, CP.SquareRadius);
    od;
    MaxRadius:=Maximum(ListRadius);
    TheDiv:=1;
    while(true)
    do
      TheQuot:=MaxRadius/(TheDiv*TheDiv);
      if TheQuot < 1 then
        break;
      fi;
      TheDiv:=TheDiv+1;
    od;
    TheDiv:=TheDiv*TheLcm*TheLcm;
    for iCase in [1..Length(eCase.Basis)]
    do
      eFrac:=eSol[iCase]/TheDiv;
      eStr:=GetFractionAsReal(eFrac);
      AppendTo(output, " ", eStr);
    od;
    AppendTo(output, "\n");
  fi;
  #
  #
  AppendTo(output, "\n", MaxIte, "\n");
  #
  AppendTo(output, "\n", AbsGap, "\n");
  CloseStream(output);
end;












OrbitShortVector:=function(GramMat, GRPinf, TheNorm)
  local SHV, ListVectors, eV, GrpMat, O, ListOrbit, eO, siZ;
  SHV:=ShortestVectors(GramMat, TheNorm);
  ListVectors:=[];
  for eV in SHV.vectors
  do
    Add(ListVectors, eV);
    Add(ListVectors, -eV);
  od;
  GrpMat:=Group(GRPinf.ListMat);
  O:=Orbits(GrpMat, ListVectors, OnPoints);
  ListOrbit:=[];
  for eO in O
  do
    eV:=eO[1];
    siZ:=Length(eO);
    Add(ListOrbit, rec(norm:=eV*GramMat*eV, vector:=eV, size:=siZ, OrdStab:=GRPinf.order/siZ));
  od;
  return ListOrbit;
end;





IsEquivalentLtype:=function(eCase, DiscInfo, eChar2)
  local testIso, eCos, eRepr, test, ListCosets;
  if IsBound(eCase.ArithmeticEquivalence)=true then
    testIso:=eCase.ArithmeticEquivalence([DiscInfo.GramMat], [eChar2]);
  else
    testIso:=FuncTestIsomorphyLattice(DiscInfo.GramMat, eChar2);
  fi;
  if testIso=false then
    return false;
  fi;
  if eCase.IsBravaisSpace=false then
    if IsBound(eCase.CharacteristicFamilyVector) then
      ListCosets:=PersoRightCosets(eCase.CharacteristicFamilyVector, DiscInfo.TheAutGroup, eCase.SymmGrpPtWs);
      if ListCosets=fail then
        ListCosets:=List(RightCosets(DiscInfo.TheAutGroup, eCase.SymmGrpPtWs), x->Representative(x));
      fi;
    else
      ListCosets:=List(RightCosets(DiscInfo.TheAutGroup, eCase.SymmGrpPtWs), Representative);
    fi;
    for eCos in ListCosets
    do
      eRepr:=testIso*Inverse(eCos);
      test:=__IsGlobalSpaceStabilizer(eCase.Basis, eRepr);
      if test=true then
        return eRepr;
      fi;
    od;
    Print("Pass the first test but not the second\n");
    return false;
  else
    return testIso;
  fi;
end;




Periodic_IsEquivalentLtype:=function(eCase, DiscInfo, eChar2)
  local testIso, eCos, eRepr, ListGroupCosets;
  testIso:=FuncTestIsomorphyLattice(DiscInfo.GramMat, eChar2);
  if testIso=false then
    return false;
  fi;
  if IsBound(eCase.CharacteristicFamilyVector) then
    ListGroupCosets:=PersoRightCosets(eCase.CharacteristicFamilyVector, DiscInfo.TheAutGroup, eCase.SymmGrpPtWs);
    if ListGroupCosets=fail then
      ListGroupCosets:=List(RightCosets(DiscInfo.TheAutGroup, eCase.SymmGrpPtWs), x->Representative(x));
    fi;
  else
    ListGroupCosets:=List(RightCosets(DiscInfo.TheAutGroup, eCase.SymmGrpPtWs), x->Representative(x));
  fi;
  for eCos in ListGroupCosets
  do
    eRepr:=testIso*Inverse(eCos);
    if __IsGlobalSpaceStabilizer(eCase.Basis, eRepr) then
      if AffineExtensionPreservingCosetStructure(eCase.ListCosets, eRepr)<>false then
        return eRepr;
      fi;
    fi;
  od;
  Print("Pass the first test but not the second\n");
  return false;
end;






LtypeDatabaseManagement:=function(PathLtype, IsSaving, MemorySave)
  local ListLtype, ListLtypeStatus, ListLtypeInv, ListDiscInfo, ListListNormGens, FuncInsertLtype, FuncGetLtype, FuncGetStatus, FuncGetDiscInfo, FuncGetInv, FuncGetListNorm, Recover, FuncGetNumberLtype, FuncLtypeInsertGenerators, FuncGetAllLtypes, FuncGetLtypeAllInfo;
  if MemorySave=true and IsSaving=false then
    Print("MemorySave=", MemorySave, "\n");
    Print("IsSaving=", IsSaving, "\n");
    Error("You cannot save memory without using disk, sorry for that");
  fi;
  ListLtype:=[];
  ListLtypeStatus:=[];
  ListLtypeInv:=[];
  ListDiscInfo:=[];
  ListListNormGens:=[];
  FuncInsertLtype:=function(Ltype, DiscInfo, TheInv)
    local nbDelaunay, FileLtype, FileDiscInfo, FileINV;
    Add(ListLtypeStatus, "NO");
    nbDelaunay:=Length(ListLtypeStatus);
    FileLtype:=Concatenation(PathLtype, "Ltype", String(nbDelaunay));
    FileDiscInfo:=Concatenation(PathLtype, "DiscInfo", String(nbDelaunay));
    FileINV:=Concatenation(PathLtype, "TheINV", String(nbDelaunay));
    SaveDataToFilePlusGzipPlusTouchPlusTest(FileLtype, Ltype, IsSaving);
    SaveDataToFilePlusTouchPlusTest(FileINV, TheInv, IsSaving);
    SaveDataToFilePlusTouchPlusTest(FileDiscInfo, DiscInfo, IsSaving);
    if MemorySave=false then
      Add(ListLtype, Ltype);
    fi;
    Add(ListLtypeInv, TheInv);
    Add(ListDiscInfo, DiscInfo);
  end;
  FuncGetLtype:=function(iOrb)
    local FileLtype;
    if MemorySave=false then
      return ListLtype[iOrb];
    fi;
    FileLtype:=Concatenation(PathLtype, "Ltype", String(iOrb));
    return ReadAsFunctionPlusGzip(FileLtype);
  end;
  FuncGetLtypeAllInfo:=function(iOrb)
    local DiscInfo;
    DiscInfo:=FuncGetDiscInfo(iOrb);
    return rec(GramMat:=DiscInfo.GramMat, Ltype:=FuncGetLtype(iOrb));
  end;
  FuncGetStatus:=function(iOrb)
    return ListLtypeStatus[iOrb];
  end;
  FuncGetDiscInfo:=function(iOrb)
    return ListDiscInfo[iOrb];
  end;
  FuncGetInv:=function(iOrb)
    return ListLtypeInv[iOrb];
  end;
  FuncGetListNorm:=function(iOrb)
    local FileListNorm;
    if MemorySave=false then
      return ListListNormGens[iOrb];
    fi;
    FileListNorm:=Concatenation(PathLtype, "ListNorm", String(iOrb));
    return ReadAsFunction(FileListNorm)();
  end;
  Recover:=function()
    local iOrb, FileLtype, FileListNorm, FileDiscInfo, FileINV, TheInv, DiscInfo, Ltype, ListNorm;
    iOrb:=1;
    while(true)
    do
      FileLtype:=Concatenation(PathLtype, "Ltype", String(iOrb));
      FileListNorm:=Concatenation(PathLtype, "ListNorm", String(iOrb));
      FileDiscInfo:=Concatenation(PathLtype, "DiscInfo", String(iOrb));
      FileINV:=Concatenation(PathLtype, "TheINV", String(iOrb));
      if IsExistingFilePlusGzipPlusTouchPlusTest(FileLtype)=true then
        TheInv:=ReadAsFunction(FileINV)();
        DiscInfo:=ReadAsFunction(FileDiscInfo)();
        Add(ListLtypeInv, TheInv);
        Add(ListDiscInfo, DiscInfo);
        if MemorySave=false then
          Ltype:=ReadAsFunctionPlusGzip(FileLtype);
          Add(ListLtype, Ltype);
        fi;
        if IsExistingFilePlusTouch(FileListNorm, IsSaving)=true then
          ListLtypeStatus[iOrb]:="YES";
          if MemorySave=false then
            ListNorm:=ReadAsFunction(FileListNorm)();
            Add(ListListNormGens, ListNorm);
          fi;
        fi;
      else
        break;
      fi;
      iOrb:=iOrb+1;
    od;
  end;
  FuncGetNumberLtype:=function()
    return Length(ListLtypeStatus);
  end;
  FuncGetAllLtypes:=function()
    local LST, iOrb;
    LST:=[];
    for iOrb in [1..Length(ListLtypeStatus)]
    do
      Add(LST, FuncGetLtypeAllInfo(iOrb));
    od;
    return LST;
  end;
  FuncLtypeInsertGenerators:=function(ListNormGens, iOrb)
    local FileListNorm;
    if MemorySave=false then
      Add(ListListNormGens, ListNormGens);
    fi;
    FileListNorm:=Concatenation(PathLtype, "ListNorm", String(iOrb));
    SaveDataToFilePlusTouch(FileListNorm, ListNormGens);
    ListLtypeStatus[iOrb]:="YES";
  end;
  return rec(FuncInsertLtype:=FuncInsertLtype, 
             FuncGetLtype:=FuncGetLtype, 
             FuncGetStatus:=FuncGetStatus, 
             FuncGetDiscInfo:=FuncGetDiscInfo, 
             FuncGetInv:=FuncGetInv, 
             FuncGetListNorm:=FuncGetListNorm, 
             Recover:=Recover, 
             FuncGetAllLtypes:=FuncGetAllLtypes, 
             FuncGetNumberLtype:=FuncGetNumberLtype, 
             FuncLtypeInsertGenerators:=FuncLtypeInsertGenerators);
end;

# For a positive semidefinite matrix
# we need to find a canonical rescaling of it
# which will be invariant by the group action
# for rational matrices we use Gcd reductions.
# Otherwise this has to be provided as input function.
EnumerationProcedureLtypeCore:=function(eCase, LtypeDatabase, DataPolyhedralTiling, LtypeGeomFunctions)
  local FuncInsert, IsFinished, FACINEQ, FACred, EXTred, eFac, TheSumFace, eExt, NewGramMatFace, i, Pos, FlippingInfo, TheFlip, iOrb, UPD, n, jOrb, test, ThePath, RML, ListNormGen, CoopFile, PacoopFile, DiscInfo, nbOrbit, testIso, TheLtype, ScalarCanonicalization, nbFacRed, iFac, ListNormGenTotal;
  #
  BasicCoherencyCheckups(eCase);
  n:=Length(eCase.Basis[1]);
  if IsBound(eCase.ScalarCanonicalization)=true then
    ScalarCanonicalization:=eCase.ScalarCanonicalization;
  else
    ScalarCanonicalization:=RemoveFractionMatrix;
  fi;
  #
  FuncInsert:=function(OneLtype)
    local FAC1, FAC2, EXT2, ListRank, eExt, GramMat, i, iOrb, testIso, eInv, ListSizeDelaunay, eDelaunay, ListStatusFace, eFac, TheSum, TheRecord, nbType, MyDiscInfo;
    FAC1:=WriteFaceInequalities(OneLtype, eCase);
    EXT2:=DualDescription(FAC1.ListInequalities);
    FAC2:=EliminationByRedundancyCone(FAC1.ListInequalities, EXT2);
    ListRank:=List(EXT2, x->RankMat(FuncComputeMat(eCase.Basis, x)));
    ListSizeDelaunay:=List(OneLtype, x->[Length(x.EXT), Order(x.TheStab.PermutationStabilizer)]);
    ListStatusFace:=[];
    for eFac in FAC2
    do
      Add(ListStatusFace, RankMat(FuncComputeMat(eCase.Basis, Sum(Filtered(EXT2, x->eFac*x=0)))));
    od;
    eInv:=rec(BasicInv:=[
         Length(FAC1.ListInequalities),
         Length(FAC2),
         Length(EXT2)],
         RankExtremeRay:=Collected(ListRank),
         DelaunayRepartition:=Collected(ListSizeDelaunay),
         StatusFaces:=Collected(ListStatusFace));
    GramMat:=Sum(List(EXT2, u->ScalarCanonicalization(FuncComputeMat(eCase.Basis, u))));
    for iOrb in [1..LtypeDatabase.FuncGetNumberLtype()]
    do
      if LtypeDatabase.FuncGetInv(iOrb)=eInv then
        testIso:=LtypeGeomFunctions.IsEquivalentLtype(eCase, LtypeDatabase.FuncGetDiscInfo(iOrb), GramMat);
        if testIso<>false then
          return testIso;
        fi;
      fi;
    od;
    MyDiscInfo:=LtypeGeomFunctions.GetDiscInfo(GramMat);
    LtypeDatabase.FuncInsertLtype(OneLtype, MyDiscInfo, eInv);
    nbType:=LtypeDatabase.FuncGetNumberLtype();
    return -1;
    Print("Find a new Ltype, now we have ", nbType, " Ltypes\n");
  end;
  #
  if LtypeDatabase.FuncGetNumberLtype()=0 then
    RML:=LtypeGeomFunctions.PrimitiveElementFct();
#    Print("Just before insert\n");
    FuncInsert(RML.DelCO);
  fi;
  #
  ListNormGenTotal:=[];
  while(true)
  do
    IsFinished:=true;
    nbOrbit:=LtypeDatabase.FuncGetNumberLtype();
    for iOrb in [1..nbOrbit]
    do
      if LtypeDatabase.FuncGetStatus(iOrb)="NO" then
        ListNormGen:=[];
        Print("Beginning treatment of orbit ", iOrb, "/", LtypeDatabase.FuncGetNumberLtype(), "\n");
        IsFinished:=false;
        #
        #
        TheLtype:=LtypeDatabase.FuncGetLtype(iOrb);
        DiscInfo:=LtypeDatabase.FuncGetDiscInfo(iOrb);
        FACINEQ:=WriteFaceInequalities(TheLtype, eCase);
        EXTred:=DualDescription(FACINEQ.ListInequalities);
        FACred:=EliminationByRedundancyCone(FACINEQ.ListInequalities, EXTred);
        nbFacRed:=Length(FACred);
        for iFac in [1..nbFacRed]
        do
          Print("Treating iFac=", iFac, "/", nbFacRed, "  |ListNormGenTotal|=", Length(ListNormGenTotal), "\n");
          eFac:=FACred[iFac];
          TheSumFace:=Sum(Filtered(EXTred, x->x*eFac=0));
          NewGramMatFace:=FuncComputeMat(eCase.Basis, TheSumFace);
          if RankMat(NewGramMatFace)=n and LtypeGeomFunctions.KillingFace(eFac)=false then
            Pos:=Position(FACINEQ.ListInequalities, eFac);
            FlippingInfo:=FACINEQ.ListInformations[Pos];
            TheFlip:=FlippingLtype(TheLtype, DiscInfo.GramMat, FlippingInfo, DataPolyhedralTiling);
            testIso:=FuncInsert(TheFlip);
            if testIso<>-1 then
              test:=IsNormalizingTspace(eCase.Basis, testIso);
              if test=false then
                Error(" the matrix does not normalize the Tspace as required");
              fi;
              Add(ListNormGen, testIso);
              AddSet(ListNormGenTotal, testIso);
            fi;
          fi;
        od;
        Print("\n");
        LtypeDatabase.FuncLtypeInsertGenerators(ListNormGen, iOrb);
      fi;
    od;
    if IsFinished=true then
      break;
    fi;
  od;
end;



EnumerationProcedureLtypeStandard:=function(eCase, PathSave, IsSaving, MemorySave, ThePrimEltFct, KillingFace)
  local PathLtype, LtypeDatabase, PrimitiveElementFct, RepartPath, DataPolyhedralTiling, FuncGetCoopPacoop, FuncGetAllLtypes, LtypeGeomFunctions, GetDiscInfo, Nval, MyDualDescription, NvalCopy, FuncGetAllExtremeRays;
  PathLtype:=Concatenation(PathSave, "Ltypes/");
  Exec("mkdir -p ", PathLtype);
  LtypeDatabase:=LtypeDatabaseManagement(PathLtype, IsSaving, MemorySave);
  PrimitiveElementFct:=function()
    local PathInitial;
    PathInitial:=Concatenation(PathSave, "InitialLtype/");
    Exec("mkdir -p ", PathInitial);
    return ThePrimEltFct(eCase, PathInitial, IsSaving);
  end;
  RepartPath:=Concatenation(PathSave, "Repartitionning/");
  Exec("mkdir -p ", RepartPath);
  DataPolyhedralTiling:=rec(PathSAVE:=RepartPath, Saving:=IsSaving);
  DataPolyhedralTiling.DualDescriptionFunction:=poly_private@DualDescriptionLRS_Reduction;
  if eCase.IsBravaisSpace=false then
    GetDiscInfo:=function(GramMat)
      local TheAutGroup;
      if IsBound(eCase.ArithmeticAutomorphismGroup)=true then
        TheAutGroup:=eCase.ArithmeticAutomorphismGroup([GramMat]);
      else
        TheAutGroup:=MatrixAutomorphismGroupGramMatrix(GramMat);
      fi;
      return rec(GramMat:=GramMat, TheAutGroup:=TheAutGroup);
    end;
  else
    GetDiscInfo:=function(GramMat)
      return rec(GramMat:=GramMat, TheAutGroup:="void");
    end;
  fi;
  LtypeGeomFunctions:=rec(KillingFace:=KillingFace, 
        PrimitiveElementFct:=PrimitiveElementFct, 
        IsEquivalentLtype:=IsEquivalentLtype, 
        GetDiscInfo:=GetDiscInfo);
  EnumerationProcedureLtypeCore(eCase, LtypeDatabase, DataPolyhedralTiling, LtypeGeomFunctions);
  FuncGetCoopPacoop:=function(ThePrefix)
    local iOrbit, OneLtype, FileCOOP, FilePACOOP;
#    ThePrefix:=Concatenation(PathSave, "CoopPacoop/");
    for iOrbit in [1..LtypeDatabase.FuncGetNumberLtype()]
    do
      OneLtype:=LtypeDatabase.FuncGetLtype(iOrbit);
      FileCOOP:=Concatenation(ThePrefix, "Coop", String(iOrbit));
      FilePACOOP:=Concatenation(ThePrefix, "Pacoop", String(iOrbit));
      OutputToCOOP_PACOOP(FileCOOP, OneLtype, eCase, 100, "1e-7", "coop");
      OutputToCOOP_PACOOP(FilePACOOP, OneLtype, eCase, 100, "1e-7", "pacoop");
    od;
  end;
  FuncGetAllLtypes:=function()
    return LtypeDatabase.FuncGetAllLtypes();
  end;
  FuncGetAllExtremeRays:=function()
    local ListListExtremeRay, eLType, FAC1, EXT2, ListExtremeRay, eEXT, GramMat;
    ListListExtremeRay:=[];
    for eLType in LtypeDatabase.FuncGetAllLtypes()
    do
      FAC1:=WriteFaceInequalities(eLType.Ltype, eCase);
      EXT2:=DualDescription(FAC1.ListInequalities);
      ListExtremeRay:=[];
      for eEXT in EXT2
      do
        GramMat:=FuncComputeMat(eCase.Basis, eEXT);
        Add(ListExtremeRay, GramMat);
      od;
      Add(ListListExtremeRay, ListExtremeRay);
    od;
    return ListListExtremeRay;
  end;
  return rec(FuncGetCoopPacoop:=FuncGetCoopPacoop, 
             FuncGetAllLtypes:=FuncGetAllLtypes, 
             FuncGetAllExtremeRays:=FuncGetAllExtremeRays, 
             LtypeDatabase:=LtypeDatabase);
end;



Periodic_EnumerationProcedureLtypeStandard:=function(eCase, PathSave, IsSaving, MemorySave, ThePrimEltFct, KillingFace)
  local PathLtype, LtypeDatabase, PrimitiveElementFct, RepartPath, DataPolyhedralTiling, FuncGetCoopPacoop, FuncGetAllLtypes, LtypeGeomFunctions, GetDiscInfo;
  PathLtype:=Concatenation(PathSave, "Ltypes/");
  Exec("mkdir -p ", PathLtype);
  LtypeDatabase:=LtypeDatabaseManagement(PathLtype, IsSaving, MemorySave);
  PrimitiveElementFct:=function()
    local PathInitial;
    PathInitial:=Concatenation(PathSave, "InitialLtype/");
    Exec("mkdir -p ", PathInitial);
    return ThePrimEltFct(eCase, PathInitial, IsSaving);
  end;
  RepartPath:=Concatenation(PathSave, "Repartitionning/");
  Exec("mkdir -p ", RepartPath);
  DataPolyhedralTiling:=rec(PathSAVE:=RepartPath,
                            DualDescriptionFunction:=poly_private@DualDescriptionLRS_Reduction,
			    Saving:=IsSaving);
  GetDiscInfo:=function(GramMat)
    local TheAutGroup;
    TheAutGroup:=MatrixAutomorphismGroupGramMatrix(GramMat);
    return rec(GramMat:=GramMat, TheAutGroup:=TheAutGroup);
  end;
  LtypeGeomFunctions:=rec(KillingFace:=KillingFace, 
        PrimitiveElementFct:=PrimitiveElementFct, 
        IsEquivalentLtype:=Periodic_IsEquivalentLtype, 
        GetDiscInfo:=GetDiscInfo);
  EnumerationProcedureLtypeCore(eCase, LtypeDatabase, DataPolyhedralTiling, LtypeGeomFunctions);
  FuncGetAllLtypes:=function()
    return LtypeDatabase.FuncGetAllLtypes();
  end;
  return rec(FuncGetAllLtypes:=FuncGetAllLtypes, 
             LtypeDatabase:=LtypeDatabase);
end;



GetLtypeInvariants:=function(TheLtype)
  local n, ListEXT, ListISO, FuncInsert, eSymp, GramMat, GRP, GRA, eGen, iSymp, eIso, eImg, jSymp, ListConn, eConn, ListSympInvariant, EXT, Antipodal;
  n:=Length(TheLtype.GramMat);
  ListEXT:=[];
  ListISO:=[];
  FuncInsert:=function(EXT)
    local eIso, eIsoRed, eIsoRedMod1;
    eIso:=Isobarycenter(EXT);
    eIsoRed:=eIso{[2..n+1]};
    eIsoRedMod1:=VectorMod1(eIsoRed);
    Add(ListEXT, EXT);
    Add(ListISO, eIsoRedMod1);
  end;
  Antipodal:=function(EXT)
    local RetEXT, eVect, eVectRed, fVect;
    RetEXT:=[];
    for eVect in EXT
    do
      eVectRed:=eVect{[2..n+1]};
      fVect:=Concatenation([1], -eVectRed);
      Add(RetEXT, fVect);
    od;
    return RetEXT;
  end;
  for eSymp in TheLtype.Ltype
  do
    FuncInsert(eSymp.EXT);
    FuncInsert(Antipodal(eSymp.EXT));
  od;
  GramMat:=TheLtype.GramMat;
  GRP:=ArithmeticAutomorphismGroup([GramMat]);
  GRA:=NullGraph(Group(()), Length(ListEXT));
  for eGen in GeneratorsOfGroup(GRP)
  do
    for iSymp in  [1..Length(ListEXT)]
    do
      eIso:=ListISO[iSymp];
      eImg:=VectorMod1(eIso*eGen);
      jSymp:=Position(ListISO, eImg);
      if iSymp<>jSymp then
        AddEdgeOrbit(GRA, [iSymp, jSymp]);
        AddEdgeOrbit(GRA, [jSymp, iSymp]);
      fi;
    od;
  od;
  ListConn:=ConnectedComponents(GRA);
  ListSympInvariant:=[];
  for eConn in ListConn
  do
    EXT:=ListEXT[eConn[1]];
    Add(ListSympInvariant, rec(Size:=Length(eConn), Volume:=AbsInt(DeterminantMat(EXT))));
  od;
  return rec(GrpSize:=Order(GRP), SimplexInvariant:=ListSympInvariant);
end;



# eCase:=rec(
#   Basis   the basis of the space considered
#   IsBravaisSpace  whether or not the space is the space
#                   of invariant matrices under a group
#   SuperMat   a positive definite matrix belonging to the space considered
#   SymmGrpPtWs   the symmetry group of the case considered.
#              it has to satisfy 
#        U*M*TransposedMat(U)=M for any matrix M in the basis
# returns the full of Ltype in the corresponding Tspace.
EnumerationProcedureLtype:=function(eCase)
  local PathSave, KillingFace;
  KillingFace:=function(eFac)
    return false;
  end;
  PathSave:=Filename(POLYHEDRAL_tmpdir, "");
  return EnumerationProcedureLtypeStandard(eCase, PathSave, false, false, RandomPrimitiveElement, KillingFace);
end;


Periodic_EnumerationProcedureLtype:=function(eCase)
  local PathSave, KillingFace;
  KillingFace:=function(eFac)
    return false;
  end;
  PathSave:=Filename(POLYHEDRAL_tmpdir, "");
  return Periodic_EnumerationProcedureLtypeStandard(eCase, PathSave, false, false, Periodic_RandomPrimitiveElement, KillingFace);
end;

# eCase:=rec(
#   Basis   the basis of the space considered
#   IsBravaisSpace  whether or not the space is the space
#                   of invariant matrices under a group
#   SuperMat   a positive definite matrix belonging to the space considered
#   SymmGrpPtWs   the symmetry group of the case considered.
#              it has to satisfy 
#        U*M*TransposedMat(U)=M for any matrix M in the basis
# returns the full list of Ltypes of the Tspace that
# contain the SuperMat.
EnumerationProcedureLtypeNeighborhood:=function(eCase)
  local PathSave, KillingFace, AdditionalProcedure, W;
  W:=BasisExpansion(eCase.Basis, eCase.SuperMat);
  KillingFace:=function(eFac)
    if eFac*W=0 then
      return false;
    fi;
    return true;
  end;
  PathSave:=Filename(POLYHEDRAL_tmpdir, "");
  return EnumerationProcedureLtypeStandard(eCase, PathSave, false, false, RandomPrimitiveElementNeighborhood, KillingFace);
end;



FuncAnalysisList:=function(UVWX)
  local iOrb, eLtype, FC1, FC2, IsTriangulation, nbTrig, IsTrig;
  FC1:=function(eLtype)
    local eFacet;
    for eFacet in eLtype
    do
      Print("One Delaunay, Stab=", Order(eFacet.TheStab.PermutationStabilizer), "  nbv=", Length(eFacet.EXT), "\n");
    od;
  end;
  FC2:=function(eLtype)
    local ListInfo, eFacet;
    ListInfo:=[];
    for eFacet in eLtype
    do
      Add(ListInfo, [Length(eFacet.EXT), Order(eFacet.TheStab.PermutationStabilizer)]);
    od;
    Print(ListInfo, "\n");
  end;
  IsTriangulation:=function(eLtype)
    local eFacet, reply;
    reply:=true;
    for eFacet in eLtype
    do
      if Length(eFacet.EXT)>Length(eFacet.EXT[1]) then
        reply:=false;
      fi;
    od;
    return reply;    
  end;
  nbTrig:=0;
  for iOrb in [1..Length(UVWX)]
  do
    Print("Considering Ltype, Nr.", iOrb, "\n");
    eLtype:=UVWX[iOrb].Ltype;
    IsTrig:=IsTriangulation(eLtype);
    FC2(eLtype);
#    Print(IsTrig, "\n");
    if IsTrig=true then
      nbTrig:=nbTrig+1;
    fi;
    Print("\n");
  od;
  Print("Found ", nbTrig, " triangulations\n");
end;








OutputToPackingSearchProgram:=function(FileName, GramMat, OneLtype)
  local output, n, nbDel, i, j, TheDel, h, VE;
  n:=Length(GramMat);
  output:=OutputTextFile(FileName, true);;
  AppendTo(output, "gramMatrix := Matrix(Q,", n, ",", n, ",\n");
  AppendTo(output, "[");
  for i in [1..n]
  do
    for j in [1..n]
    do
      AppendTo(output, GramMat[i][j]);
      if (j<n) then
        AppendTo(output, ",");
      fi;
    od;
    if (i<n) then
      AppendTo(output, ",");
    fi;
    AppendTo(output, "\n");
  od;
  AppendTo(output, "]);\n");
  AppendTo(output, "\n");

  nbDel:=Length(OneLtype);
  AppendTo(output, "Centers := Matrix(Q, ", nbDel, ",", n, ",\n");
  AppendTo(output, "[");
  for i in [1..nbDel]
  do
    TheDel:=OneLtype[i];
    h:=TheDel.Center[j+1]-TheDel.EXT[1];
    VE:=h{[2..n+1]};
    for j in [1..n]
    do
      AppendTo(output, h[j]);
      if (j<n) then
        AppendTo(output, ",");
      fi;
    od;
    if (i<nbDel) then
      AppendTo(output, ",");
    fi;
    AppendTo(output, "\n");
  od;
  AppendTo(output, "]);\n");
  CloseStream(output);
end;

VOR_LTYPE_GetPrincipalType:=function(n)
  local GramMat, eG, GRP, LFC;
  GramMat:=LatticeAn(n).GramMat;
  eG:=Inverse(GramMat);
  GRP:=Group([-IdentityMat(n)]);
  LFC:=DelaunayComputationStandardFunctions(eG);
  return LFC.GetDelaunayDescriptionSmallerGroup(GRP);
end;


VOR_LTYPE_GetRigidLattices:=function(n)
  local eDir, eFile, D4gram, TrivGram;
  if n>5 then
    Error("Rigid lattices are only known for n<=5");
  fi;
  if n=5 then
    eDir:=DirectoriesPackageLibrary("MyPolyhedral", "DATA/RigidLattices")[1];
    eFile:=Filename(eDir, Concatenation("ListRigidDim", String(n)));
    #
    return ReadAsFunction(eFile)();
  fi;
  if n=4 then
    D4gram:=LatticeDn(4).TheGram;
    return [D4gram];
  fi;
  if n=3 or n=2 then
    return [];
  fi;
  if n=1 then
    TrivGram:=[[1]];
    return [TrivGram];
  fi;
  Error("We should not reach that stage");
end;




VOR_LTYPE_GetPrimitiveLtype:=function(n)
  local eDir, eFile, U, ListLtype;
  if n>5 then
    Error("Primitive Ltypes are only known for n<=5");
  fi;
  eDir:=DirectoriesPackageLibrary("MyPolyhedral", "DATA/PrimitiveLtype")[1];
  eFile:=Filename(eDir, Concatenation("File", String(n)));
  #
  U:=ReadAsFunction(eFile)();
  if n=5 then
    ListLtype:=U.ListDIM5.ListLtype;
  else
    ListLtype:=U.ListLtypes;
  fi;
  return ListLtype;
end;


VOR_LTYPE_GetListConfiguration:=function(ListLtype)
  local n, GRP, TheBasis, eCase, nbType, ListConfiguration, iLType, ListOrbitDelaunay, RecIneq, ListIneq, ListIneqRed, EXT, ListMat, eEXT, eMat, i, TheDim;
  n:=Length(ListLtype[1].GramMat);
  TheDim:=n*(n+1)/2;
  GRP:=Group([-IdentityMat(n)]);
  TheBasis:=InvariantFormDutourVersion(GeneratorsOfGroup(GRP));
  eCase:=rec(Basis:=TheBasis);
  #
  nbType:=Length(ListLtype);
  ListConfiguration:=[];
  for iLType in [1..nbType]
  do
    Print("iLType=", iLType, "/", nbType, "\n");
    ListOrbitDelaunay:=ListLtype[iLType].Ltype;
    RecIneq:=WriteFaceInequalities(ListOrbitDelaunay, eCase);
    ListIneq:=RecIneq.ListInequalities;
    ListIneqRed:=List(ListIneq, x->x{[2..TheDim+1]});
    EXT:=DualDescription(ListIneqRed);
    ListMat:=[];
    for eEXT in EXT
    do
      eMat:=NullMat(n,n);
      for i in [1..TheDim]
      do
        eMat:=eMat+eEXT[i]*TheBasis[i];
      od;
      Add(ListMat, RemoveFractionMatrix(eMat));
    od;
    Add(ListConfiguration, ListMat);
  od;
  return ListConfiguration;
end;





VOR_LTYPE_GetInvariant:=function(ListMat)
  local ListRnk, eMat, SHV, ListVect;
  ListRnk:=List(ListMat, RankMat);
  eMat:=Sum(ListMat);
  SHV:=ShortestVectorDutourVersion(eMat);
  ListVect:=List(ListMat, SymmetricMatrixToVector);
  return rec(CollRnk:=Collected(ListRnk),
             nbShort:=Length(SHV), eDet:=DeterminantMat(eMat), 
             LinInv:=LinPolytope_Invariant(ListVect));
end;


VOR_LTYPE_DoSelection:=function(ListConfiguration, optProg)
  local n, ListMaximal, NewListConfiguration, ListInvariant, FuncInsert, eSingularity, ListVect, ListSets, eSet, ListMat, eIrregInfo, eMat;
  n:=Length(ListConfiguration[1][1]);
  NewListConfiguration:=[];
  ListInvariant:=[];
  FuncInsert:=function(eNewSing)
    local eNewMat, eSing, eMat, eIsom, iSing, eNewInv;
    eNewMat:=Sum(eNewSing);
    eNewInv:=VOR_LTYPE_GetInvariant(eNewSing);
    for iSing in [1..Length(NewListConfiguration)]
    do
      if ListInvariant[iSing]=eNewInv then
        eSing:=NewListConfiguration[iSing];
        eMat:=Sum(eSing);
        if optProg="ISOM" then
          eIsom:=ArithmeticIsomorphism_Isom([eNewMat], [eMat]);
        elif optProg="NAUTY" then
          eIsom:=ArithmeticIsomorphism_Nauty([eNewMat], [eMat]);
        else
          Error("Not an acceptable option");
        fi;
        if eIsom<>false then
          return;
        fi;
      fi;
    od;
    Add(NewListConfiguration, eNewSing);
    Add(ListInvariant, eNewInv);
#    Print("Now |NewListConfiguration|=", Length(NewListConfiguration), "\n");
  end;
  for eSingularity in ListConfiguration
  do
    ListVect:=List(eSingularity, SymmetricMatrixToVector);
    if Length(ListVect)>1 then
      ListSets:=DualDescriptionSets(ListVect);
      for eSet in ListSets
      do
        ListMat:=eSingularity{eSet};
        eMat:=Sum(ListMat);
        if RankMat(eMat)=n then
          FuncInsert(ListMat);
        fi;
      od;
    fi;
  od;
  return rec(ListConfiguration:=NewListConfiguration);
end;


VOR_LTYPE_GetTotalInfo:=function(ListConfiguration, optProg)
  local n, TotalInfo, eRecEnum, ListVect, rnk, FileSave, ListSize;
  n:=Length(ListConfiguration[1][1]);
  TotalInfo:=[];
  eRecEnum:=rec(ListConfiguration:=ListConfiguration);
  while(true)
  do
    Add(TotalInfo, eRecEnum);
    ListVect:=List(eRecEnum.ListConfiguration[1], SymmetricMatrixToVector);
    rnk:=RankMat(ListVect);
    FileSave:=Concatenation("DATA_TEMP/List", String(n), "_rnk", String(rnk));
    SaveDataToFilePlusTouch(FileSave, eRecEnum);
    #
    eRecEnum:=VOR_LTYPE_DoSelection(ListConfiguration, optProg);
    Print( " |ListConfiguration|=", Length(eRecEnum.ListConfiguration), "\n");
    ListConfiguration:=eRecEnum.ListConfiguration;
    if Length(ListConfiguration)=0 then
      break;
    fi;
  od;
  ListSize:=List(TotalInfo, x->Length(x.ListConfiguration));
  Print("ListSize=", ListSize, "\n");
  return TotalInfo;
end;





VOR_LTYPE_Inclusions:=function(n, optProg)
  local TheDim, eDim, FileSave1, TheList1, nbCase1, FileSave2, TheList2, nbCase2, ListINV1, GetPosition, TheListSuper, TheListSub, iCase1, iCase2, ListVect, ListSets, eSet, ListMat, eMat, eConf;
  TheDim:=n*(n+1)/2;
  #
  FileSave1:=Concatenation("DATA_TEMP/List", String(n), "_rnk1");
  TheList1:=ReadAsFunction(FileSave1)().ListConfiguration;
  nbCase1:=Length(TheList1);
  TheListSub:=[];
  for iCase1 in [1..nbCase1]
  do
    Add(TheListSub, []);
  od;
  FileSave2:=Concatenation("DATA_TEMP/Inclusions/ListSubIdx", String(n), "_rnk1");
  SaveDataToFilePlusTouch(FileSave2, TheListSub);
  #
  FileSave1:=Concatenation("DATA_TEMP/List", String(n), "_rnk", String(TheDim));
  TheList1:=ReadAsFunction(FileSave1)().ListConfiguration;
  nbCase1:=Length(TheList1);
  TheListSuper:=[];
  for iCase1 in [1..nbCase1]
  do
    Add(TheListSuper, []);
  od;
  FileSave2:=Concatenation("DATA_TEMP/Inclusions/ListSuperIdx", String(n), "_rnk", String(TheDim));
  SaveDataToFilePlusTouch(FileSave2, TheListSuper);
  #
  for eDim in [1..TheDim-1]
  do
    Print("eDim=", eDim, " / ", TheDim, "\n");
    FileSave1:=Concatenation("DATA_TEMP/List", String(n), "_rnk", String(eDim));
    TheList1:=ReadAsFunction(FileSave1)().ListConfiguration;
    nbCase1:=Length(TheList1);
    #
    FileSave2:=Concatenation("DATA_TEMP/List", String(n), "_rnk", String(eDim+1));
    TheList2:=ReadAsFunction(FileSave2)().ListConfiguration;
    nbCase2:=Length(TheList2);
    #
    ListINV1:=List(TheList1, VOR_LTYPE_GetInvariant);
    GetPosition:=function(ListMat)
      local eNewMat, eNewInv, iCase1, eSing, eMat, eIsom;
      eNewMat:=Sum(ListMat);
      eNewInv:=VOR_LTYPE_GetInvariant(ListMat);
      for iCase1 in [1..nbCase1]
      do
        if ListINV1[iCase1]=eNewInv then
          eSing:=TheList1[iCase1];
          eMat:=Sum(eSing);
          if optProg="ISOM" then
            eIsom:=ArithmeticIsomorphism_Isom([eNewMat], [eMat]);
          elif optProg="NAUTY" then
            eIsom:=ArithmeticIsomorphism_Nauty([eNewMat], [eMat]);
          else
            Error("Not an acceptable option");
          fi;
          if eIsom<>false then
            return iCase1;
          fi;
        fi;
      od;
      Print("We should not reach that stage\n");
      Print(NullMat(5));
    end;
    TheListSuper:=[];
    TheListSub:=[];
    for iCase1 in [1..nbCase1]
    do
      Add(TheListSuper, []);
    od;
    for iCase2 in [1..nbCase2]
    do
      Add(TheListSub, []);
    od;
    #
    for iCase2 in [1..nbCase2]
    do
      eConf:=TheList2[iCase2];
      ListVect:=List(eConf, SymmetricMatrixToVector);
      ListSets:=DualDescriptionSets(ListVect);
      for eSet in ListSets
      do
        ListMat:=eConf{eSet};
        eMat:=Sum(ListMat);
        if RankMat(eMat)=n then
          iCase1:=GetPosition(ListMat);
          Add(TheListSuper[iCase1], iCase2);
          Add(TheListSub[iCase2], iCase1);
        fi;
      od;
    od;
    #
    FileSave1:=Concatenation("DATA_TEMP/Inclusions/ListSuperIdx", String(n), "_rnk", String(eDim));
    SaveDataToFilePlusTouch(FileSave1, TheListSuper);
    FileSave2:=Concatenation("DATA_TEMP/Inclusions/ListSubIdx", String(n), "_rnk", String(eDim+1));
    SaveDataToFilePlusTouch(FileSave2, TheListSub);
  od;
end;





GetConjugacyInvariantOfGroup:=function(eGRP)
  local LGen, SpaceAntisymInv, SpaceSymInv, eInv, ListInvElt, eElt, ePol, eCoeffChar, eCoeffMin, eEltInv;
  LGen:=GeneratorsOfGroup(eGRP);
  SpaceAntisymInv:=InvariantAntisymmetricForm(LGen);
  SpaceSymInv:=InvariantFormDutourVersion(LGen);
  eInv:=rec(order:=Order(eGRP), dimSym:=Length(SpaceSymInv), dimAntiSym:=Length(SpaceAntisymInv));
  if Order(eGRP) < 20 then
    ListInvElt:=[];
    for eElt in eGRP
    do
      ePol:=CharacteristicPolynomial(eElt);
      eCoeffChar:=CoefficientsOfUnivariatePolynomial(ePol);
      ePol:=MinimalPolynomial(eElt);
      eCoeffMin:=CoefficientsOfUnivariatePolynomial(ePol);
      eEltInv:=rec(eCoeffChar:=eCoeffChar, eCoeffMin:=eCoeffMin);
      Add(ListInvElt, eEltInv);
    od;
    eInv.ListInvElt:=Collected(ListInvElt);
  fi;
  return eInv;
end;



GetCaratStyleInformation:=function(n)
  local ListSymb, ListGRP, ListNames, ListInv, eSymb, LGrp, i;
  ListSymb:=CaratCrystalFamilies[n];
  ListGRP:=[];
  ListNames:=[];
  ListInv:=[];
  for eSymb in ListSymb
  do
    LGrp:=BravaisGroupsCrystalFamily(eSymb);
    for i in [1..Length(LGrp)]
    do
      Add(ListGRP, LGrp[i]);
      Add(ListNames, rec(eSymb:=eSymb, i:=i));
      Add(ListInv, GetConjugacyInvariantOfGroup(LGrp[i]));
    od;
  od;
  return rec(ListSymb:=ListSymb, ListGRP:=ListGRP, ListNames:=ListNames, ListInv:=ListInv);
end;



VOR_LTYPE_GetListZonotopal:=function(n)
  local TheDim, ListCones, eDim, eFile, TheList, nbCase, iCase, eCase, ListRank, ListHighRank, ListConeIdx, ListListConeIdx, TheInt, TheListSuper, ListConeMaximal, RecConeZonotopal, FileSave1;
  TheDim:=n*(n+1)/2;
  ListListConeIdx:=[];
  ListCones:=[];
  for eDim in [1..TheDim]
  do
    eFile:=Concatenation("DATA_TEMP/List", String(n), "_rnk", String(eDim));
    TheList:=ReadAsFunction(eFile)().ListConfiguration;
    nbCase:=Length(TheList);
    ListConeIdx:=[];
    for iCase in [1..nbCase]
    do
      eCase:=TheList[iCase];
      ListRank:=List(eCase, RankMat);
      ListHighRank:=Filtered(ListRank, x->x>1);
      if Length(ListHighRank)=0 then
        Add(ListCones, eCase);
        Add(ListConeIdx, iCase);
      fi;
    od;
    Print("n=", n, " eDim=", eDim, " / ", TheDim, " nbCase=", nbCase, " |ListConeIdx|=", Length(ListConeIdx), "\n");
    Add(ListListConeIdx, ListConeIdx);
  od;
  #
  # Now determining the maximal cones.
  #
  ListConeMaximal:=[];
  for eDim in [1..TheDim-1]
  do
    eFile:=Concatenation("DATA_TEMP/List", String(n), "_rnk", String(eDim));
    TheList:=ReadAsFunction(eFile)().ListConfiguration;
    #
    FileSave1:=Concatenation("DATA_TEMP/Inclusions/ListSuperIdx", String(n), "_rnk", String(eDim));
    TheListSuper:=ReadAsFunction(FileSave1)();
    #
    for iCase in ListListConeIdx[eDim]
    do
      TheInt:=Intersection(ListListConeIdx[eDim+1], TheListSuper[iCase]);
      if Length(TheInt)=0 then
        Add(ListConeMaximal, TheList[iCase]);
      fi;
    od;
  od;
  #
  eFile:=Concatenation("DATA_TEMP/List", String(n), "_rnk", String(TheDim));
  TheList:=ReadAsFunction(eFile)().ListConfiguration;
  Append(ListConeMaximal, TheList{ListListConeIdx[TheDim]});
  Print("|ListConeMaximal|=", Length(ListConeMaximal), "\n");
  #
  Print("|ListCones|=", Length(ListCones), "\n");
  eFile:=Concatenation("DATA_TEMP/ListZonotopal", String(n));
  RecConeZonotopal:=rec(ListCones:=ListCones,
            ListConeMaximal:=ListConeMaximal);
  SaveDataToFile(eFile, RecConeZonotopal);
end;


VOR_LTYPE_GetBravaisGroups:=function(n)
  local eSymb, i, GetName, TheDim, eDim, eFile1, TheList1, nbCase1, ListGrpName, eConf, eConfRed, SumConf, eGRP, eName, eFileSave, LGrp, TotalRec, IsTotallyInvariant, eNameTotInv, eGRPtotInv, TestConf, eOrder, OrderInducePermGroup;
  TotalRec:=GetCaratStyleInformation(n);
  GetName:=function(GRP)
    local eInv, i, eEquiv;
    eInv:=GetConjugacyInvariantOfGroup(GRP);
    for i in [1..Length(TotalRec.ListNames)]
    do
      if eInv=TotalRec.ListInv[i] then
        eEquiv:=RepresentativeAction(GL(n, Integers), TotalRec.ListGRP[i], GRP);
        if eEquiv<>fail then
          return TotalRec.ListNames[i];
        fi;
      fi;
    od;
    Error("We should never reach that stage");
  end;
  TheDim:=n*(n+1)/2;
  IsTotallyInvariant:=function(eConf, eGRP)
    local eMat, eGen;
    for eMat in eConf
    do
      for eGen in GeneratorsOfGroup(eGRP)
      do
        if eGen*eMat*TransposedMat(eGen)<>eMat then
	  return false;
	fi;
      od;
    od;
    return true;
  end;
  OrderInducePermGroup:=function(eConf, eGRP)
    local ListPermGen, eGen, eList, eMat, NewMat, pos, ePerm, GRPperm;
    ListPermGen:=[];
    for eGen in GeneratorsOfGroup(eGRP)
    do
      eList:=[];
      for eMat in eConf
      do
        NewMat:=eGen*eMat*TransposedMat(eGen);
        pos:=Position(eConf, NewMat);
        if pos=fail then
	  Error("Thinking error here 1");
	fi;
        Add(eList, pos);
      od;
      ePerm:=PermList(eList);
      if ePerm=fail then
        Error("Thinking error here 2");
      fi;
      Add(ListPermGen, ePerm);
    od;
    GRPperm:=Group(ListPermGen);
    return Order(GRPperm);
  end;

  for eDim in [1..TheDim]
  do
    eFile1:=Concatenation("DATA_TEMP/List", String(n), "_rnk", String(eDim));
    TheList1:=ReadAsFunction(eFile1)().ListConfiguration;
    nbCase1:=Length(TheList1);
    Print("GetBravaisGroup eDim=", eDim, " / ", TheDim, " nbCase1=", nbCase1, "\n");
    ListGrpName:=[];
    for eConf in TheList1
    do
      eConfRed:=List(eConf, RemoveFractionMatrix);
      SumConf:=Sum(eConfRed);
      eGRP:=ArithmeticAutomorphismGroup([SumConf]);
      eName:=GetName(eGRP);
      if IsTotallyInvariant(eConf, eGRP) then
        eGRPtotInv:=eGRP;
	eNameTotInv:=eName;
      else
        TestConf:=Concatenation([SumConf], eConfRed);
	eGRPtotInv:=ArithmeticAutomorphismGroup(TestConf);
	eNameTotInv:=GetName(eGRPtotInv);
      fi;
      eOrder:=OrderInducePermGroup(eConfRed, eGRP);
      Add(ListGrpName, rec(eName:=eName, eOrder:=eOrder, eNameTotInv:=eNameTotInv));
    od;
    eFileSave:=Concatenation("DATA_TEMP/GRP/List", String(n), "_rnk", String(eDim));
    SaveDataToFilePlusTouch(eFileSave, ListGrpName);
  od;
end;


VOR_PrintMatrix:=function(ListColumn, ListRow, TheMatrix, eFileTex)
  local nbCol, nbRow, output, iCol, iRow, eVal;
  nbCol:=Length(ListColumn);
  nbRow:=Length(ListRow);
  RemoveFileIfExist(eFileTex);
  output:=OutputTextFile(eFileTex, true);
  AppendTo(output, "\\begin{center}\n");
  AppendTo(output, "\\begin{tabular}{|c|");
  for iCol in [1..nbCol]
  do
    AppendTo(output, "c");
  od;
  AppendTo(output, "|}\n");
  AppendTo(output, "\\hline\n");
  for iCol in [1..nbCol]
  do
    AppendTo(output, " & ", ListColumn[iCol]);
  od;
  AppendTo(output, "\\\\\n");
  AppendTo(output, "\\hline\n");
  for iRow in [1..nbRow]
  do
    AppendTo(output, ListRow[iRow]);
    for iCol in [1..nbCol]
    do
      AppendTo(output, " &");
      eVal:=TheMatrix[iRow][iCol];
      if eVal<>0 then
        AppendTo(output, eVal);
      fi;
    od;
    AppendTo(output, "\\\\\n");
  od;
  AppendTo(output, "\\hline\n");
  AppendTo(output, "\\end{tabular}\n");
  AppendTo(output, "\\end{center}\n");
  CloseStream(output);
  LATEX_Compilation(eFileTex);
end;


VOR_PrintListLine:=function(ListLine, ListHeader, nbCol, eFileTex)
  local nbRow, nbEnt, nbPerLine, output, iCol, iRow, iPerLine, pos, eEnt;
  nbRow:=UpperInteger(Length(ListLine) / nbCol);
  RemoveFileIfExist(eFileTex);
  nbEnt:=Length(ListLine);
  nbPerLine:=Length(ListLine[1]);
  output:=OutputTextFile(eFileTex, true);
  AppendTo(output, "\\begin{center}\n");
  AppendTo(output, "\\begin{tabular}{");
  for iCol in [1..nbCol]
  do
    AppendTo(output, "|");
    for iPerLine in [1..nbPerLine]
    do
      AppendTo(output, "c|");
    od;
  od;
  AppendTo(output, "}\n");
  #
  AppendTo(output, "\\hline\n");
  for iCol in [1..nbCol]
  do
    for iPerLine in [1..nbPerLine]
    do
      if iPerLine>1 or iCol>1 then
        AppendTo(output, " & ");
      fi;
      AppendTo(output, ListHeader[iPerLine]);
    od;
  od;
  AppendTo(output, "\\\\\n");
  AppendTo(output, "\\hline\n");
  #
  for iRow in [1..nbRow]
  do
    for iCol in [1..nbCol]
    do
      pos:=iRow + nbRow*(iCol-1);
      if pos<=nbEnt then
        eEnt:=ListLine[pos];
      else
        eEnt:=ListWithIdenticalEntries(nbPerLine, "");
      fi;
      for iPerLine in [1..nbPerLine]
      do
        if iCol>1 or iPerLine>1 then
	  AppendTo(output, " & ");
	fi;
	AppendTo(output, eEnt[iPerLine]);
      od;
    od;
    if iRow<nbRow then
      AppendTo(output, "\\\\");
    fi;
    AppendTo(output, "\n");
  od;
  AppendTo(output, "\\\\\n");
  AppendTo(output, "\\hline\n");
  AppendTo(output, "\\end{tabular}\n");
  AppendTo(output, "\\end{center}\n");
  CloseStream(output);
  LATEX_Compilation(eFileTex);
end;





VOR_LTYPE_TablePossibleGroup:=function(n)
  local eListList, TheDim, rnk, eFile, eRecEnum, eList, TotalSet, nbVal, ListColumn, pos, eFileTex, TheMatrix, eVal, TotalRec, ListFrequency, ePerm, TotalSetSort, ListFrequencySort, eFileFreqTex, output, iVal, eName, eInv, SortingInfo, nbCol, iCol, iLine, nbLine, eMult, eNameTotInv, eListRed, ListListOrder, ListOrder;
  eListList:=[];
  TotalRec:=GetCaratStyleInformation(n);
  TheDim:=n*(n+1)/2;
  TotalSet:=[];
  ListListOrder:=[];
  for rnk in [1..TheDim]
  do
    Print("VOR_LTYPE_TablePossibleGroup, rnk=", rnk, " / ", TheDim, "\n");
    eFile:=Concatenation("DATA_TEMP/GRP/List", String(n), "_rnk", String(rnk));
    eList:=ReadAsFunction(eFile)();
    eListRed:=List(eList, x->x.eNameTotInv);
    TotalSet:=Union(TotalSet, Set(eListRed));
    Add(eListList, eListRed);
    ListOrder:=List(eList, x->x.eOrder);
    Add(ListListOrder, ListOrder);
  od;
  Print("TotalSet=", Length(TotalSet), "\n");
  nbVal:=Length(TotalSet);
  TheMatrix:=NullMat(nbVal, TheDim);
  ListFrequency:=ListWithIdenticalEntries(nbVal,0);
  ListColumn:=[];
  for rnk in [1..TheDim]
  do
    Add(ListColumn, rnk);
    for eVal in eListList[rnk]
    do
      pos:=Position(TotalSet, eVal);
      TheMatrix[pos][rnk]:=TheMatrix[pos][rnk]+1;
      ListFrequency[pos]:=ListFrequency[pos]+1;
    od;
  od;
  eFileTex:="Tables/TablePossibleGroup_pre.tex";
  VOR_PrintMatrix(ListColumn, TotalSet, TheMatrix, eFileTex);
  #
  #
  SortingInfo:=List(ListFrequency, x->1/x);
  ePerm:=SortingPerm(SortingInfo);
  TotalSetSort:=Permuted(TotalSet, ePerm);
  ListFrequencySort:=Permuted(ListFrequency, ePerm);
  eFileFreqTex:="Tables/TableFrequency_pre.tex";
  RemoveFileIfExist(eFileFreqTex);
  output:=OutputTextFile(eFileFreqTex, true);
  AppendTo(output, "\\begin{center}\n");
  nbCol:=3;
  AppendTo(output, "\\begin{tabular}{|");
  for iCol in [1..nbCol]
  do
    AppendTo(output, "c|c|c|");
  od;
  AppendTo(output, "}\n");
  eMult:=nbCol*3;
  AppendTo(output, "\\cline{1-", eMult, "}\n");
  for iCol in [1..nbCol]
  do
    if iCol>1 then
      AppendTo(output, " & ");
    fi;
    AppendTo(output, "name & order & frequency");
  od;
  AppendTo(output, "\\\\\n");
  AppendTo(output, "\\cline{1-", eMult, "}\n");
  nbLine:=UpperInteger(nbVal/nbCol);
  for iLine in [1..nbLine]
  do
    for iCol in [1..nbCol]
    do
      iVal:=iLine + nbLine*(iCol-1);
      if iCol>1 then
        AppendTo(output, " & ");
      fi;
      if iVal <= nbVal then
        eName:=TotalSetSort[iVal];
        pos:=Position(TotalRec.ListNames, eName);
        eInv:=TotalRec.ListInv[pos];
        AppendTo(output, eName.eSymb, " :", eName.i, " & ", eInv.order, " & ", ListFrequencySort[iVal]);
      else
        AppendTo(output, " & & ");
      fi;
    od;
    AppendTo(output, "\\\\\n");
  od;
  AppendTo(output, "\\cline{1-", eMult, "}\n");
  AppendTo(output, "\\end{tabular}\n");
  AppendTo(output, "\\end{center}\n");
  CloseStream(output);
  LATEX_Compilation(eFileFreqTex);
  #
  return rec(eListList:=eListList,
             ListListOrder:=ListListOrder,
             ListFrequency:=ListFrequency,
	     TotalRec:=TotalRec);
end;


GetRecordGroupListMatrix:=function(ListMatrix)
  local n, TheSum, eMat, GRP, ListPermGens, eGen, eList, ePerm, GRPperm;
  n:=Length(ListMatrix[1]);
  TheSum:=NullMat(n, n);
  for eMat in ListMatrix
  do
    TheSum:=TheSum + eMat;
  od;
  GRP:=ArithmeticAutomorphismGroup([TheSum]);
  ListPermGens:=[];
  for eGen in GeneratorsOfGroup(GRP)
  do
    eList:=List(ListMatrix, x->Position(ListMatrix, eGen*x*TransposedMat(eGen)));
    ePerm:=PermList(eList);
    Add(ListPermGens, ePerm);
  od;
  GRPperm:=Group(ListPermGens);
  return rec(GRP:=GRP, GRPperm:=GRPperm);
end;


VOR_LTYPE_GetEulerPoincareCharacteristic:=function(n)
  local TheDim, eDim, ListSumInverse, SumEulerPoincareChar, eFile, TheList, nbCase, eSumInverse, iCase, eCase, RecGRoup, RecGroup, TheString, ePow, eNum, eDen, eStrFrac;
  TheDim:=n*(n+1)/2;
  ListSumInverse:=[];
  SumEulerPoincareChar:=0;
  TheString:="";
  for eDim in [1..TheDim]
  do
    eFile:=Concatenation("DATA_TEMP/List", String(n), "_rnk", String(eDim));
    TheList:=ReadAsFunction(eFile)().ListConfiguration;
    nbCase:=Length(TheList);
    eSumInverse:=0;
    for iCase in [1..nbCase]
    do
      eCase:=TheList[iCase];
      RecGroup:=GetRecordGroupListMatrix(eCase);
      eSumInverse:=eSumInverse + 1/Order(RecGroup.GRP);
    od;
    ePow:=(-1)^(eDim);
    SumEulerPoincareChar:=SumEulerPoincareChar + ePow * eSumInverse;
    Add(ListSumInverse, eSumInverse);
    eNum:=NumeratorRat(eSumInverse);
    eDen:=DenominatorRat(eSumInverse);
    eStrFrac:=Concatenation("\\frac{", String(eNum), "}{", String(eDen), "}");
    if ePow=1 then
      TheString:=Concatenation(TheString, " + ", eStrFrac);
    else
      TheString:=Concatenation(TheString, " - ", eStrFrac);
    fi;
    Print("eDim=", eDim, " nbCase=", nbCase, " eSumInverse=", eSumInverse, "\n");
  od;
  Print("SumEulerPoincareChar=", SumEulerPoincareChar, "\n");
  Print("TheString=", TheString, "\n");
end;



VOR_LTYPE_GetMaximalParallelotope:=function(n)
  local TheDim, ListCase, eDim, eFile1, TheList1, eFile2, TheList2, eFileSup, TheListSup, IsMaximalParallelotope, iCase1, eCase, nbCase1;
  TheDim:=n*(n+1)/2;
  ListCase:=[];
  for eDim in [1..TheDim]
  do
    eFile1:=Concatenation("DATA_TEMP/List", String(n), "_rnk", String(eDim));
    TheList1:=ReadAsFunction(eFile1)().ListConfiguration;
    nbCase1:=Length(TheList1);
    Print("GetMaximalParallelotope eDim=", eDim, " / ", TheDim, " nbCase1=", nbCase1, "\n");
    if eDim<TheDim then
      eFile2:=Concatenation("DATA_TEMP/List", String(n), "_rnk", String(eDim+1));
      TheList2:=ReadAsFunction(eFile2)().ListConfiguration;
    fi;
    eFileSup:=Concatenation("DATA_TEMP/Inclusions/ListSuperIdx", String(n), "_rnk", String(eDim));
    TheListSup:=ReadAsFunction(eFileSup)();
    IsMaximalParallelotope:=function(iCase1)
      local ListRank1, nbRank1, iCase2, ListRank2, nbRank2;
      ListRank1:=List(TheList1[iCase1], RankMat);
      nbRank1:=Length(Filtered(ListRank1, x->x=1));
      for iCase2 in TheListSup[iCase1]
      do
        ListRank2:=List(TheList2[iCase2], RankMat);
        nbRank2:=Length(Filtered(ListRank2, x->x=1));
        if nbRank2<nbRank1 then
          Error("Logical error in number of rank 1 matrices");
        fi;
        if nbRank2 > nbRank1 then
          return false;
        fi;
      od;
      return true;
    end;
    for iCase1 in [1..nbCase1]
    do
      if IsMaximalParallelotope(iCase1) then
        eCase:=rec(eDim:=eDim, iCase:=iCase1);
        Add(ListCase, eCase);
      fi;
    od;
  od;
  return ListCase;
end;



VOR_LTYPE_GetRigidFormsAndGeometry:=function(ListConfiguration)
  local n, ListRigidForm, TheAct, FuncInsert, nbLtype, iLtype, eGramMat;
  n:=Length(ListConfiguration[1][1]);
  ListRigidForm:=[];
  TheAct:=function(x, g)
    return Inverse(g)*x*TransposedMat(Inverse(g));
  end;
  FuncInsert:=function(eGramRigid, iLtype)
    local nbRigidForm, SumMat, GRP, eRecO, ListRec, eMat, fMat, SumMatB, NewRec, iRigidForm, test, eRec;
    nbRigidForm:=Length(ListRigidForm);
    SumMat:=Sum(ListConfiguration[iLtype]);
    GRP:=ArithmeticAutomorphismGroup([eGramRigid]);
    eRecO:=OrbitWithAction(GRP, SumMat, TheAct);
    Print("|eRecO.ListElement|=", Length(eRecO.ListElement), "\n");
    ListRec:=[];
    for eMat in eRecO.ListElement
    do
      fMat:=Inverse(eMat);
      SumMatB:=fMat*SumMat*TransposedMat(fMat);
      NewRec:=rec(iLtype:=iLtype, eMat:=fMat, SumMat:=SumMatB);
      Add(ListRec, NewRec);
    od;
    Print("|ListRec|=", Length(ListRec), "\n");
    for iRigidForm in [1..nbRigidForm]
    do
      test:=ArithmeticIsomorphism([eGramRigid], [ListRigidForm[iRigidForm].eGramRigid]);
      if test<>false then
        for eRec in ListRec
        do
          NewRec:=rec(iLtype:=iLtype, eMat:=test*eRec.eMat, SumMat:=test*eRec.SumMat*TransposedMat(test));
          Add(ListRigidForm[iRigidForm].ListRec, NewRec);
        od;
        return;
      fi;
    od;
    Add(ListRigidForm, rec(eGramRigid:=eGramRigid, GRP:=GRP, ListRec:=ListRec));
    Print("|ListRigidForm|=", Length(ListRigidForm), "\n");
  end;
  nbLtype:=Length(ListConfiguration);
  for iLtype in [1..nbLtype]
  do
    Print("iLtype=", iLtype, " / ", nbLtype, "\n");
    for eGramMat in ListConfiguration[iLtype]
    do
      if RankMat(eGramMat)=n then
        FuncInsert(eGramMat, iLtype);
      fi;
    od;
  od;
  return ListRigidForm;
end;




VOR_LTYPE_GetZoneContracted:=function(n)
  local TheDim, ListZoneContracted, ListZoneContractedGeneralized, ListZonotope, ListSumLowerDim, FuncInsertGeneralized, FuncInsertClassic, rnk, eFile, eRecEnum, eConf;
  TheDim:=n*(n+1)/2;
  ListZoneContracted:=[];
  ListZoneContractedGeneralized:=[];
  ListZonotope:=[];
  ListSumLowerDim:=[];
  FuncInsertGeneralized:=function(eConf)
    local ListRank, eMat, eRank, eInv, nbZoneCont, iZoneCont, fZoneCont, eIsom, NewConf, RecConf, iMat, eSet, ListVect, SumHighRank, eSetSat, DefaultRank, DefaultNumber, SimplicialityDefect;
    eSet:=[];
    for iMat in [1..Length(eConf)]
    do
      eMat:=eConf[iMat];
      eRank:=RankMat(eMat);
      if eRank>1 then
        Add(eSet, iMat);
      fi;
    od;
    if Length(eSet)=0 then
      Add(ListZonotope, eConf);
      return;
    fi;
    if RankMat(Sum(eConf{eSet})) < n then
      Add(ListSumLowerDim, eConf);
      return;
    fi;
    ListVect:=List(eConf, SymmetricMatrixToVector);
    eSetSat:=FaceSaturation(ListVect, eSet);
    DefaultRank:=RankMat(ListVect) - RankMat(ListVect{eSetSat});
    DefaultNumber:=Length(ListVect) - Length(eSetSat);
    SimplicialityDefect:=DefaultNumber - DefaultRank;
    SumHighRank:=Sum(eConf{eSetSat});
    eInv:=VOR_LTYPE_GetInvariant(eConf{eSetSat});
    nbZoneCont:=Length(ListZoneContractedGeneralized);
    for iZoneCont in [1..nbZoneCont]
    do
      fZoneCont:=ListZoneContractedGeneralized[iZoneCont];
      if fZoneCont.eInv=eInv then
        eIsom:=ArithmeticIsomorphism_Isom([SumHighRank], [fZoneCont.SumHighRank]);
        if eIsom<>false then
          if eIsom*SumHighRank*TransposedMat(eIsom)<>fZoneCont.SumHighRank then
            Error("Need to debug");
          fi;
          NewConf:=List(eConf, x->eIsom * x * TransposedMat(eIsom));
          Add(ListZoneContractedGeneralized[iZoneCont].ListSubFamily, NewConf);
          Add(ListZoneContractedGeneralized[iZoneCont].ListSimplicialityDefect, SimplicialityDefect);
          return;
        fi;
      fi;
    od;
    ListRank:=List(eConf{eSetSat}, RankMat);
    RecConf:=rec(eConfHigh:=eConf{eSetSat}, ListRank:=ListRank, eInv:=eInv, SumHighRank:=SumHighRank, ListSubFamily:=[eConf], ListSimplicialityDefect:=[0]);
    Add(ListZoneContractedGeneralized, RecConf);
    Print("Now |ListZoneContractedGeneralized|=", Length(ListZoneContractedGeneralized), "\n");
  end;
  FuncInsertClassic:=function(eConf)
    local ListRank, eMat, eRank, eInv, nbZoneCont, iZoneCont, fZoneCont, eIsom, NewConf, RecConf, iMat, eSet, ListVect, SumHighRank, eSetSat, eSetRank1, LFC, RecVor, eSymbol;
    eSet:=[];
    eSetRank1:=[];
    for iMat in [1..Length(eConf)]
    do
      eMat:=eConf[iMat];
      eRank:=RankMat(eMat);
      if eRank>1 then
        Add(eSet, iMat);
      fi;
      if eRank=1 then
        Add(eSetRank1, iMat);
      fi;
    od;
    if Length(eSetRank1)>0 then
      return;
    fi;
    SumHighRank:=Sum(eConf{eSet});
    if RankMat(SumHighRank)<n then
      return;
    fi;
    LFC:=DelaunayComputationStandardFunctions(SumHighRank);
    RecVor:=LFC.GetVoronoiVertices();
    eSymbol:=Concatenation(String(RecVor.FAC), ",", String(RecVor.EXT));
    ListRank:=List(eConf{eSet}, RankMat);
    RecConf:=rec(eConfHigh:=eConf{eSet}, ListRank:=ListRank, SumHighRank:=SumHighRank, eSymbol:=eSymbol);
    Add(ListZoneContracted, RecConf);
    Print("Now |ListZoneContracted|=", Length(ListZoneContracted), "\n");
  end;
  for rnk in [1..TheDim]
  do
    eFile:=Concatenation("DATA_TEMP/List", String(n), "_rnk", String(rnk));
    eRecEnum:=ReadAsFunction(eFile)();
    Print("rnk=", rnk, " |ListConfiguration|=", Length(eRecEnum.ListConfiguration), "\n");
    for eConf in eRecEnum.ListConfiguration
    do
      FuncInsertGeneralized(eConf);
      FuncInsertClassic(eConf);
    od;
  od;
  return rec(ListZoneContractedGeneralized:=ListZoneContractedGeneralized,
             ListZoneContracted:=ListZoneContracted,
             ListZonotope:=ListZonotope,
             ListSumLowerDim:=ListSumLowerDim);
end;




DecomposeDomainIntoZoneContracted:=function(ListMatrix, ListOrbitTotallyZoneCont)
  local n, RecGroup, ListVector, rnk, ListRank, nbVect, eSet1, eSetHigh, rnkHigh, rnk1, rnkDiff, ListMatSel, ListBlockFinal, eOrbit, ListVectorExpand, len, eSubset, test, eBlock, EXT, ListMatrGens, ListAbsDet, eGen, eMat, TheVol, ListVolume, eSet, eTotSet, EXTtot, eVol, TheDiff, O, ListCanonic, eO, eCanonic, PartListVol, pos, nbHigh, GetDinst, TestSetMat, TestEquivalence, eBigSet, nbBlock, ListTotSet, GRA, eInt, eTotInt, i, j, ListFAC, FACtot, TheSpace;
  n:=Length(ListMatrix[1]);
  RecGroup:=GetRecordGroupListMatrix(ListMatrix);
  ListVector:=List(ListMatrix, SymmetricMatrixToVector);
  nbVect:=Length(ListVector);
  rnk:=RankMat(ListVector);
  ListRank:=List(ListMatrix, RankMat);
  Print("   rnk=", rnk, " nbVect=", nbVect, " ListRank=", ListRank, "\n");
  #
  eSet1:=Filtered([1..nbVect], x->ListRank[x]=1);
  eSetHigh:=Filtered([1..nbVect], x->ListRank[x]>1);
  nbHigh:=Length(eSetHigh);
  rnk1:=ZeroRankMat(ListVector{eSet1});
  rnkDiff:=rnk - rnk1;
  ListMatSel:=ListMatrix{eSetHigh};
  #
  GetDinst:=function(ListMat)
    return Concatenation([Sum(ListMat)], ListMat);
  end;
  TestEquivalence:=function(ListMat1, ListMat2)
    local eSumMat1, eSumMat2, test, Pmat, ListMat1img;
    eSumMat1:=Sum(ListMat1);
    eSumMat2:=Sum(ListMat2);
    test:=ArithmeticIsomorphism([eSumMat1], [eSumMat2]);
    if test=false then
      return false;
    fi;
    Pmat:=test;
    if Pmat*eSumMat1*TransposedMat(Pmat)<>eSumMat2 then
      Error("Problem in the code");
    fi;
    ListMat1img:=List(ListMat1, x->Pmat*x*TransposedMat(Pmat));
    if Set(ListMat1img)<>Set(ListMat2) then
      Print("Return false here\n");
      return false;
    fi;
    return Pmat;
  end;
  ListBlockFinal:=[];
  for eOrbit in ListOrbitTotallyZoneCont
  do
    ListVectorExpand:=List(eOrbit, SymmetricMatrixToVector);
    if RankMat(ListVectorExpand)=rnkDiff then
      len:=Length(ListVectorExpand);
      for eSubset in Combinations([1..nbHigh], len)
      do
        TestSetMat:=ListMatSel{eSubset};
        if RankMat(Sum(TestSetMat))=n then
          test:=TestEquivalence(TestSetMat, eOrbit);
          if test<>false then
            eBlock:=eSetHigh{eSubset};
	    eBigSet:=Concatenation(eBlock, eSet1);
            if RankMat(ListVector{eBigSet})<>rnk then
              Error("We have an inconsistency");
            fi;
            Add(ListBlockFinal, eBlock);
          fi;
        fi;
      od;
    fi;
  od;
  #
#  Print("RankMat(ListVector)=", RankMat(ListVector), "\n");
  EXT:=PolytopizationGeneralCone(ListVector);
#  Print("RankMat(EXT)=", RankMat(EXT), "\n");
  TheVol:=VolumeComputationPolytope(EXT);
  ListVolume:=[];
  nbBlock:=Length(ListBlockFinal);
  Print("   ListBlockFinal=", ListBlockFinal, "\n");
  for eSet in ListBlockFinal
  do
    eTotSet:=Concatenation(eSet, eSet1);
    EXTtot:=EXT{eTotSet};
    if RankMat(EXTtot)<>rnk then
      Error("Error in the rank of EXTtot");
    fi;
    eVol:=VolumeComputationPolytope(EXTtot);
    Add(ListVolume, eVol);
  od;
  Print("   Collected(ListVolume)=", ListVolume, "\n");
  Print("   Collected(NoFr(ListVolume))=", RemoveFraction(ListVolume), "\n");
  TheDiff:=TheVol - Sum(ListVolume);
#  Print("TheDiff=", TheDiff, "\n");
  if TheDiff<>0 then
    Error("Please correct this volume error");
  fi;
  O:=Orbits(RecGroup.GRPperm, ListBlockFinal, OnSets);
  ListCanonic:=[];
  for eO in O
  do
    eSet:=eO[1];
    eTotSet:=Set(Concatenation(eSet, eSet1));
    ListTotSet:=List(eO, x->Concatenation(x, eSet1));
    eCanonic:=rec(ListMatrix:=ListMatrix{eSet}, ListMatrixTot:=ListMatrix{eTotSet}, ListTotSet:=ListTotSet);
    if RankMat(ListVector{eTotSet})<>rnk then
      Error("We have an error in our system");
    fi;
    Add(ListCanonic, eCanonic);
  od;
  GRA:=NullGraph(Group(()), nbBlock);
  for i in [1..nbBlock-1]
  do
    for j in [i+1..nbBlock]
    do
      eInt:=Intersection(ListBlockFinal[i], ListBlockFinal[j]);
      eTotInt:=Union(eInt, eSet1);
      if RankMat(ListVector{eTotInt})=rnk-1 then
        AddEdgeOrbit(GRA, [i,j]);
        AddEdgeOrbit(GRA, [j,i]);
      fi;
    od;
  od;
  if IsConnectedGraph(GRA)=false then
    Error("The connectivity is not true and that is likely a bug");
  fi;
  ListFAC:=[];
  for i in [1..nbBlock]
  do
    eSet:=eO[1];
    eTotSet:=Set(Concatenation(eSet, eSet1));
    Add(ListFAC, DualDescription(EXT{eTotSet}));
  od;
  for i in [1..nbBlock-1]
  do
    for j in [i+1..nbBlock]
    do
      FACtot:=Concatenation(ListFAC[i], ListFAC[j]);
      TheSpace:=LinearDeterminedByInequalities(FACtot);
      if RankMat(TheSpace)>rnk then
        Error("The intersection between FAC orbit i and j is non-trivial");
      fi;
    od;
  od;
  Print("   |ListBlockFinal|=", Length(ListBlockFinal), "  |ListCanonic|=", Length(ListCanonic), "\n");
  return rec(ListBlockFinal:=ListBlockFinal, ListCanonic:=ListCanonic);
end;


DecomposeDomainIntoZoneContractedLowerDimensional:=function(ListMatrix, TheRecord)
  local n, ListVect, ListFacet, GetSetInformation, rnk, RecGroup, ListFacets, ListCases, FuncInsert, IsFinished, ListListRepresentative, iRec, eRec, eRepr, fFacet, ListLocalFacet, eCanonic, eCase, nbCase, eSet, ListVectSel, NewRec, i, ListNbOrbit, nbBlock, nbVect;
  n:=Length(ListMatrix[1]);
  ListVect:=List(ListMatrix, SymmetricMatrixToVector);
  nbVect:=Length(ListVect);
  ListFacets:=DualDescriptionSets(ListVect);
  GetSetInformation:=function(uSet)
    local ListIncident, eFacet, nbIncd, TheInt, iIncd, rnk1, rnk2, DeltaRank, IsFace, TheReply;
    ListIncident:=[];
    for eFacet in ListFacets
    do
      if IsSubset(eFacet, uSet)=true then
        Add(ListIncident, eFacet);
      fi;
    od;
    rnk2:=RankMat(ListVect{uSet});
    nbIncd:=Length(ListIncident);
    if nbIncd>0 then
      TheInt:=ListIncident[1];
      for iIncd in [2..nbIncd]
      do
        TheInt:=Intersection(TheInt, ListIncident[iIncd]);
      od;
    else
      TheInt:=[1..nbVect];
    fi;
    rnk1:=RankMat(ListVect{TheInt});
    DeltaRank:=rnk1 - rnk2;
    IsFace:=TheInt=uSet;
    TheReply:=rec(nbIncd:=nbIncd,
                  DeltaRank:=DeltaRank,
		  SaturationSet:=TheInt, 
                  IsFace:=IsFace);
    return TheReply;
  end;
  rnk:=RankMat(ListVect);
  RecGroup:=GetRecordGroupListMatrix(ListMatrix);
  ListCases:=[];
  FuncInsert:=function(fRec)
    local gRec, test, eInf;
    eInf:=GetSetInformation(fRec.eSet);
    if eInf.nbIncd=0 then
      for gRec in ListCases
      do
        if gRec.dim=fRec.dim then
          test:=RepresentativeAction(RecGroup.GRPperm, fRec.eSet, gRec.eSet, OnSets);
          if test<>fail then
	    return;
          fi;
        fi;
      od;
      Add(ListCases, fRec);
    fi;
  end;
  nbBlock:=0;
  for eCanonic in TheRecord.ListCanonic
  do
    eSet:=List(eCanonic.ListMatrixTot, x->Position(ListMatrix,x));
    nbBlock:=nbBlock + Length(eCanonic.ListTotSet);
    if RankMat(ListVect{eSet})<>rnk then
      Error("Rank of eCanonic is not correct");
    fi;
    eCase:=rec(dim:=rnk, eSet:=eSet, status:=false);
    Add(ListCases, eCase);
  od;
  while(true)
  do
    nbCase:=Length(ListCases);
    IsFinished:=true;
    for iRec in [1..nbCase]
    do
      eRec:=ListCases[iRec];
      if eRec.status=false then
        ListCases[iRec].status:=true;
	IsFinished:=false;
	if eRec.dim>1 then
          ListVectSel:=ListVect{eRec.eSet};
          if RankMat(ListVectSel)<>eRec.dim then
            Error("The rank of ListVectSel is not correct");
          fi;
          ListLocalFacet:=DualDescriptionSets(ListVectSel);
	  for fFacet in ListLocalFacet
	  do
            if Length(fFacet)=0 then
              Error("We have fFacet=[]");
            fi;
            if RankMat(ListVectSel{fFacet})<>eRec.dim-1 then
              Error("We have a rank error");
            fi;
            NewRec:=rec(dim:=eRec.dim-1, eSet:=eRec.eSet{fFacet}, status:=false);
	    FuncInsert(NewRec);
          od;
	fi;
      fi;
    od;
    if IsFinished then
      break;
    fi;
  od;
  ListListRepresentative:=[];
  for i in [1..rnk]
  do
    Add(ListListRepresentative, []);
  od;
  for eRec in ListCases
  do
    eRepr:=rec(ListMatrix:=ListMatrix{eRec.eSet}, eSet:=eRec.eSet);
    Add(ListListRepresentative[eRec.dim], eRepr);
  od;
  ListNbOrbit:=List(ListListRepresentative, Length);
  Print("   ListNbOrbit=", ListNbOrbit, "\n");
  if rnk>1 and nbBlock>1 then
    if ListNbOrbit[rnk-1]=0 then
      Error("It is likely an error that we need to solve");
    fi;
    if nbBlock=2 and ListNbOrbit[rnk-1]>1 then
      Error("We have nbBlock=2 but number of facets greater than 1");
    fi;
    if rnk>=3 and nbBlock=2 and ListNbOrbit[rnk-2]>0 then
      Error("Maybe we should debug from that point");
    fi;
  fi;
  return ListListRepresentative;
end;





DecomposeDomainIntoZoneContracted_V1:=function(ListMatrix, ListOrbitTotallyZoneCont)
  local TheSum, eMat, ListVector, ListRank, nbMat, ListBlockFinal, ListBlockWork, NewListBlockWork, eSet, TheListSet, eSmaSet, eBigSet, ListRankSel, IsCorrect, EXT, TheVol, ListVolume, eSet1, eTotSet, EXTtot, eVol, TheDiff, EXTred, rnk, ListPermGens, eGen, eCanonic, ListCanonic, RecGroup, eList, ePerm, O, eO, ListMatrGens, ListAbsDet, FuncIsCorrect_V1, FuncIsCorrectFinal_V1, FuncIsCorrect, FuncIsCorrectFinal, eBlock, IsCorrectFinal, pos, PartListVol, TestEquivalence, TestBelongingOrbit, DoDetCheck;
  RecGroup:=GetRecordGroupListMatrix(ListMatrix);
  #
  ListVector:=List(ListMatrix, SymmetricMatrixToVector);
  rnk:=RankMat(ListVector);
  ListRank:=List(ListMatrix, RankMat);
  Print("   ListRank=", ListRank, "\n");
  nbMat:=Length(ListMatrix);
  eSet1:=Filtered([1..nbMat], x->ListRank[x]=1);
  #
  ListBlockFinal:=Set([]);
  ListBlockWork:=[];
  eSet:=[1..nbMat];
  if Position(ListRank, 1)=fail then
    Add(ListBlockFinal, eSet);
  else
    Add(ListBlockWork, eSet);
  fi;
  FuncIsCorrectFinal_V1:=function(eBigSet)
    local ListRankSel, IsCorrect;
    ListRankSel:=ListRank{eBigSet};
    IsCorrect:=Position(ListRankSel, 1)=fail;
    return IsCorrect;
  end;
  FuncIsCorrect_V1:=function(eBigSet)
    local eTotSet;
    eTotSet:=Union(eBigSet, eSet1);
    if RankMat(ListVector{eTotSet})<>rnk then
      return false;
    fi;
    return true;
  end;
  FuncIsCorrect:=function(eBigSet)
    Print("  eBigSet=", eBigSet, "\n");
    Print("  eSet1=", eSet1, "\n");
    if IsSubset(eBigSet, eSet1)=false then
      Print("  Return false 1\n");
      return false;
    fi;
    if RankMat(ListVector{eBigSet})<>rnk then
      Print("  Return false 2\n");
      return false;
    fi;
    return true;
  end;
  FuncIsCorrectFinal:=function(eBigSet)
    local ListVectRank1, ListVectRankHigh, eVal, rnkTot, rnk1, rnkHigh;
    ListVectRank1:=[];
    ListVectRankHigh:=[];
    for eVal in eBigSet
    do
      if ListRank[eVal]=1 then
        Add(ListVectRank1, ListVector[eVal]);
      else
        Add(ListVectRankHigh, ListVector[eVal]);
      fi;
    od;
    rnkTot:=RankMat(ListVector{eBigSet});
    rnk1:=ZeroRankMat(ListVectRank1);
    rnkHigh:=RankMat(ListVectRankHigh);
    if rnk1<>Length(ListVectRank1) then
      Error("Consistency error");
    fi;
    if rnkTot<>rnk1 + rnkHigh then
      return false;
    fi;
    return true;
  end;
  TestEquivalence:=function(ListMat1, ListMat2)
    local eSumMat1, eSumMat2, test, Pmat, ListMat1img;
    eSumMat1:=Sum(ListMat1);
    eSumMat2:=Sum(ListMat2);
    test:=ArithmeticIsomorphism([eSumMat1], [eSumMat2]);
    if test=false then
      return false;
    fi;
    Pmat:=test;
    if Pmat*eSumMat1*TransposedMat(Pmat)<>eSumMat2 then
      Error("Problem in the code");
    fi;
    ListMat1img:=List(ListMat1, x->Pmat*x*TransposedMat(Pmat));
    if Set(ListMat1img)<>Set(ListMat2) then
      Print("Return false here\n");
      return false;
    fi;
    return Pmat;
  end;
  TestBelongingOrbit:=function(eBlock)
    local IsMatch, eOrbit, ListVectExpand;
    IsMatch:=false;
    for eOrbit in ListOrbitTotallyZoneCont
    do
      ListVectExpand:=List(eOrbit, SymmetricMatrixToVector);
      if RankMat(ListVectExpand)=rnk then
        if TestEquivalence(eOrbit, eBlock)<>false then
          IsMatch:=true;
        fi;
      fi;
    od;
    if IsMatch=false then
      Error("The orbit has not been found to be matching");
    fi;
  end;
  while(true)
  do
    NewListBlockWork:=[];
#    Print("ListBlockWork=", ListBlockWork, "\n");
    for eSet in ListBlockWork
    do
      TheListSet:=DualDescriptionSets(ListVector{eSet});
#      Print("TheListSet=", TheListSet, "\n");
      for eSmaSet in TheListSet
      do
        eBigSet:=Set(eSet{eSmaSet});
        Print("eBigSet=", eBigSet, "\n");
        IsCorrect:=FuncIsCorrect_V1(eBigSet);
        Print("  IsCorrect=", IsCorrect, "\n");
        if IsCorrect=true then
          IsCorrectFinal:=FuncIsCorrectFinal_V1(eBigSet);
          Print("  IsCorrectFinal=", IsCorrectFinal, "\n");
          if IsCorrectFinal then
            AddSet(ListBlockFinal, eBigSet);
          else
            Add(NewListBlockWork, eBigSet);
          fi;
        fi;
      od;
    od;
    if Length(NewListBlockWork)=0 then
      break;
    fi;
    ListBlockWork:=Set(NewListBlockWork);
    Print("   |ListBlockWork|=", Length(ListBlockWork), "\n");
  od;
  for eBlock in ListBlockFinal
  do
    TestBelongingOrbit(ListMatrix{eBlock});
  od;
  # The polytopization is not equivariant
  EXT:=PolytopizationGeneralCone(ListVector);
  DoDetCheck:=false;
  if DoDetCheck=true then
    ListMatrGens:=[];
    ListAbsDet:=[];
    for eGen in GeneratorsOfGroup(RecGroup.GRPperm)
    do
      eMat:=FindTransformation(EXT, EXT, eGen);
      if eMat=fail then
        Error("Error in FindTransformation call");
      fi;
      Add(ListMatrGens, eMat);
      Add(ListAbsDet, AbsInt(DeterminantMat(eMat)));
    od;
    if Set(ListAbsDet)<>[1] then
      Error("Inconsistency in computation of determinants");
    fi;
  fi;
  TheVol:=VolumeComputationPolytope(EXT);
  ListVolume:=[];
  for eBigSet in ListBlockFinal
  do
    EXTtot:=EXT{eBigSet};
    if RankMat(EXTtot)<>rnk then
      Error("Error in the rank of EXTtot");
    fi;
    eVol:=VolumeComputationPolytope(EXTtot);
    Add(ListVolume, eVol);
  od;
  TheDiff:=TheVol - Sum(ListVolume);
  Print("TheDiff=", TheDiff, "\n");
  if TheDiff<>0 then
    Error("Please correct this volume error");
  fi;
  O:=Orbits(RecGroup.GRPperm, ListBlockFinal, OnSets);
  ListCanonic:=[];
  for eO in O
  do
    eSet:=eO[1];
    eCanonic:=rec(ListMatrix:=ListMatrix{eSet});
    Add(ListCanonic, eCanonic);
  od;
  Print("   |ListBlockFinal|=", Length(ListBlockFinal), "  |ListCanonic|=", Length(ListCanonic), "\n");
  return rec(ListBlockFinal:=ListBlockFinal, ListCanonic:=ListCanonic);
end;




VOR_LTYPE_ComputeTableZoneContraction:=function(n)
  local FileSave, ListPos, ListRigidDim5, GetMatrixSymbol, TheInfoZoneContGen, SecFileSave, TheData, nbRec, iRec, eRec, nbFamily, ListStr, eMat, eStr, eColl, TotStr, eEnt, eMult, LFC, RecVor, eSymbol, PrintSeriesInTable, output, ListCaseZoneContracted, ListCaseOther, ListVect, eVect, dim, IsZoneContracted, nbCol, eInfo, eFileTex, ListSort, eRecDescRay, PreListStr, PreListSort, TheSortInfo, ePermFinal, PreTheInfoZoneContGen, ePerm, TheInfoDecompoZoneContract, ListMatrix, TheRec, TheDim, RecInfoAllDecompo, ListInfoAllDecompo, TheInfoDecompoPrincipal, ThiFileSave, ListBlockFinal, ListByRank, TotalNumberContractionDomain, VectNumberDecomposition, RecGroup, NewListBlockFinal, eNbDomain, ListVector, eRank, NumberContDomain, eFamily, RecO, ListOrbitTotallyZoneCont, DeltaDomain, TheRecAllDim, ListListContractionDomain, eDim, eDomain, rnk, ListGroup, sizFamily, nbVect, eOrbit, len, RecGroupHigh, ListRayOneDim, ListRayOneDimSet, i, iFamily, O, hSet, ListSet, fSet, aSet, nbCase, SumEulerPoincareChar, RecEulerPoincareChar, bSet, NewListVector, ListSumInverse, eSumInverse, iCase, eCase, NewMatFamily, ListNumberContractionDomain, ListNumberLtypeDomain, eRecEnum, eFile, ListLine, eLine, ListHeader, BigRecCont, eNumberContractionDomain, nbOrb;
  TheDim:=n*(n+1)/2;
  #
  # The rigid forms, finding symbols of extreme rays.
  #
  ListPos:=ReadAsFunction("DATA_TEMP/IdentificationRigidLatt")();
  ListRigidDim5:=ReadAsFunction("ListRigidDim5")();
  GetMatrixSymbol:=function(eG)
    local i, eIsom, ePos;
    if RankMat(eG)=1 then
      return rec(str:="p_1", sortInfo:=[1,1]);
    fi;
    if RankMat(eG)=4 then
      return rec(str:="\\mathsf{D}_{4}", sortInfo:=[4,1]);
    fi;
    for i in [1..7]
    do
      eIsom:=ArithmeticIsomorphism_Isom([eG], [ListRigidDim5[i]]);
      if eIsom<>false then
        ePos:=ListPos[i];
        return rec(str:=Concatenation("L_{", String(ePos), "}"), sortInfo:=[5,ePos]);
      fi;
    od;
    Error("We should never reach that stage");
  end;
  #
  # Decomposition of the irreducible domains into totally zone contracted objects.
  #
  Print("Before decomposition into contracted domains\n");
  FileSave:=Concatenation("DATA_TEMP/TableData_DecompositionContractionType_", String(n));
#  RemoveFileIfExistPlusTouch(FileSave);
  if IsExistingFilePlusTouch(FileSave) then
    TheInfoDecompoZoneContract:=ReadAsFunction(FileSave)();
  else
    SecFileSave:=Concatenation("DATA_TEMP/ZoneContractions_", String(n));
    TheData:=ReadAsFunction(SecFileSave)();
    TheInfoDecompoZoneContract:=[];
    nbRec:=Length(TheData.ListZoneContractedGeneralized);
    ListOrbitTotallyZoneCont:=[];
    for eRec in TheData.ListZoneContractedGeneralized
    do
      ListMatrix:=eRec.eConfHigh;
      if First(ListMatrix, x->RankMat(x)=1)=fail then
        Add(ListOrbitTotallyZoneCont, ListMatrix);
      fi;
    od;
    for iRec in [1..nbRec]
    do
      Print("iRec=", iRec, " / ", nbRec, "\n");
      ListMatrix:=TheData.ListZoneContractedGeneralized[iRec].eConfHigh;
      TheRec:=DecomposeDomainIntoZoneContracted(ListMatrix, ListOrbitTotallyZoneCont);
      TheRecAllDim:=DecomposeDomainIntoZoneContractedLowerDimensional(ListMatrix, TheRec);
      Add(TheInfoDecompoZoneContract, rec(TheRec:=TheRec, TheRecAllDim:=TheRecAllDim));
    od;
    SaveDataToFilePlusTouch(FileSave, TheInfoDecompoZoneContract);
  fi;
  Print("After decomposition into contracted domains\n");
  #
  # Compute decompositions into contraction types.
  #
  Print("Before computation for all domains\n");
  FileSave:="DATA_TEMP/TableData_NumberDecompositionAllContractionType";
#  RemoveFileIfExistPlusTouch(FileSave);
  if IsExistingFilePlusTouch(FileSave) then
    RecInfoAllDecompo:=ReadAsFunction(FileSave)();
  else
    SecFileSave:=Concatenation("DATA_TEMP/TableData_DecompositionContractionType_", String(n));
    TheInfoDecompoPrincipal:=ReadAsFunction(SecFileSave)();
    #
    ThiFileSave:=Concatenation("DATA_TEMP/ZoneContractions_", String(n));
    TheData:=ReadAsFunction(ThiFileSave)();
    #
    nbRec:=Length(TheInfoDecompoPrincipal);
    ListInfoAllDecompo:=[];
    ListByRank:=ListWithIdenticalEntries(TheDim,0);
    TotalNumberContractionDomain:=0;
    for iRec in [1..nbRec]
    do
      eRec:=TheData.ListZoneContractedGeneralized[iRec];
      ListBlockFinal:=TheInfoDecompoPrincipal[iRec].ListBlockFinal;
      VectNumberDecomposition:=[];
      NumberContDomain:=0;
      for eFamily in eRec.ListSubFamily
      do
        ListPos:=List(eRec.eConfHigh, x->Position(eFamily, x));
        if Position(ListPos, fail)<>fail then
          Error("Inconsistency in the decomposition");
        fi;
        RecGroup:=GetRecordGroupListMatrix(eFamily);
        NewListBlockFinal:=List(ListBlockFinal, x->Set(ListPos{x}));
        RecO:=OrbitsSafe(RecGroup.GRPperm, NewListBlockFinal, OnSets);
        eNbDomain:=Length(RecO.ListRepr);
#        Print("|NewListBlockFinal|=", Length(NewListBlockFinal), " eNbDomain=", eNbDomain, "\n");
        Add(VectNumberDecomposition, eNbDomain);
        NumberContDomain:=NumberContDomain + eNbDomain;
        ListVector:=List(eFamily, SymmetricMatrixToVector);
        eRank:=RankMat(ListVector);
        ListByRank[eRank]:=ListByRank[eRank] + eNbDomain;
      od;
      TotalNumberContractionDomain:=TotalNumberContractionDomain + NumberContDomain;
      DeltaDomain:=NumberContDomain - Length(eRec.ListSubFamily);
      Print("iRec=", iRec, " |eRec.ListSubFamily|=", Length(eRec.ListSubFamily), " NumberContDomain=", NumberContDomain, " DeltaDomain=", DeltaDomain, "\n");
      Add(ListInfoAllDecompo, rec(VectNumberDecomposition:=VectNumberDecomposition, NumberContDomain:=NumberContDomain));
    od;
    #
    RecInfoAllDecompo:=rec(ListInfoAllDecompo:=ListInfoAllDecompo,
                           ListByRank:=ListByRank,
                           TotalNumberContractionDomain:=TotalNumberContractionDomain);
    SaveDataToFilePlusTouch(FileSave, RecInfoAllDecompo);
  fi;
  Print("TotalNumberContractionDomain=", RecInfoAllDecompo.TotalNumberContractionDomain, "\n");
  #
  # Computation of the whole set of contraction domains.
  #
  FileSave:=Concatenation("DATA_TEMP/DATA_ListContractionDomains_", String(n));
#  RemoveFileIfExistPlusTouch(FileSave);
  if IsExistingFilePlusTouch(FileSave) then
    BigRecCont:=ReadAsFunction(FileSave)();
  else
    ListListContractionDomain:=[];
    for eDim in [1..TheDim]
    do
      Add(ListListContractionDomain, []);
    od;
    #
    # Computation of contraction domain
    #
    SecFileSave:=Concatenation("DATA_TEMP/ZoneContractions_", String(n));
    TheData:=ReadAsFunction(SecFileSave)();
    #
    # Zonotopes are trivial
    #
    for eDomain in TheData.ListZonotope
    do
      ListVect:=List(eDomain, SymmetricMatrixToVector);
      rnk:=RankMat(ListVect);
      Add(ListListContractionDomain[rnk], eDomain);
    od;
    #
    # The cones containing a single D4
    #
    for eDomain in TheData.ListSumLowerDim
    do
      ListVect:=List(eDomain, SymmetricMatrixToVector);
      rnk:=RankMat(ListVect);
      nbVect:=Length(eDomain);
      if nbVect<>rnk then
        Error("We have rnk<>nbVect. Rethink is needed");
      fi;
      Add(ListListContractionDomain[rnk], eDomain);
    od;
    #
    # The contraction domains
    #
    SecFileSave:=Concatenation("DATA_TEMP/TableData_DecompositionContractionType_", String(n));
    TheInfoDecompoPrincipal:=ReadAsFunction(SecFileSave)();
    nbRec:=Length(TheInfoDecompoPrincipal);
    #
    ListNumberContractionDomain:=[];
    for iRec in [1..nbRec]
    do
      eNumberContractionDomain:=0;
      Print("iRec=", iRec, " / ", nbRec, "\n");
      eOrbit:=TheInfoDecompoZoneContract[iRec];
      eRec:=TheData.ListZoneContractedGeneralized[iRec];
      len:=Length(eOrbit.TheRecAllDim);
      ListGroup:=[];
      for eFamily in eRec.ListSubFamily
      do
        RecGroup:=GetRecordGroupListMatrix(eFamily);
	Add(ListGroup, RecGroup);
      od;
      RecGroupHigh:=GetRecordGroupListMatrix(eRec.eConfHigh);
      sizFamily:=Length(ListGroup);
      for i in [1..len]
      do
        for eDomain in eOrbit.TheRecAllDim[i]
        do
          for iFamily in [1..sizFamily]
          do
            eFamily:=eRec.ListSubFamily[iFamily];
            ListPos:=List(eRec.eConfHigh, x->Position(eFamily, x));
            ListRayOneDimSet:=Filtered([1..Length(eFamily)], x->Position(eRec.eConfHigh,eFamily[x])=fail);
            ListRayOneDim:=eFamily{ListRayOneDimSet};
            if Position(ListPos, fail)<>fail then
              Error("Inconsistency in the decomposition");
            fi;
            hSet:=Set(List(eDomain.ListMatrix, x->Position(eRec.eConfHigh, x)));
            O:=Orbit(RecGroupHigh.GRPperm, hSet, OnSets);
            RecGroup:=ListGroup[iFamily];
            ListSet:=[];
            for fSet in O
            do
              aSet:=Set(ListPos{fSet});
              Add(ListSet, aSet);
            od;
            RecO:=OrbitsSafe(RecGroup.GRPperm, ListSet, OnSets);
            for bSet in RecO.ListRepr
            do
              NewMatFamily:=Concatenation(eFamily{bSet}, ListRayOneDim);
              NewListVector:=List(NewMatFamily, SymmetricMatrixToVector);
              eRank:=RankMat(NewListVector);
              Add(ListListContractionDomain[eRank], NewMatFamily);
              eNumberContractionDomain:=eNumberContractionDomain+1;
            od;
          od;
        od;
      od;
      Add(ListNumberContractionDomain, eNumberContractionDomain);
    od;
    #
    # Saving the data
    #
    BigRecCont:=rec(ListListContractionDomain:=ListListContractionDomain,
                    ListNumberContractionDomain:=ListNumberContractionDomain);
    SaveDataToFilePlusTouch(FileSave, BigRecCont);
  fi;
  Print("|ListListContractionDomain|=", List(BigRecCont.ListListContractionDomain, Length), "\n");
  #
  # The computation of the Euler Poincare characteristic
  #
  FileSave:=Concatenation("DATA_TEMP/DATA_EulerPoincareCharacteristic_", String(n));
#  RemoveFileIfExistPlusTouch(FileSave);
  if IsExistingFilePlusTouch(FileSave) then
    RecEulerPoincareChar:=ReadAsFunction(FileSave)();
  else
    ListSumInverse:=[];
    SumEulerPoincareChar:=0;
    for eDim in [1..TheDim]
    do
      nbCase:=Length(BigRecCont.ListListContractionDomain[eDim]);
      eSumInverse:=0;
      for iCase in [1..nbCase]
      do
        eCase:=BigRecCont.ListListContractionDomain[eDim][iCase];
        RecGroup:=GetRecordGroupListMatrix(eCase);
        eSumInverse:=eSumInverse + 1/Order(RecGroup.GRP);
      od;
      SumEulerPoincareChar:=SumEulerPoincareChar + (-1)^(eDim) * eSumInverse;
      Add(ListSumInverse, eSumInverse);
      Print("eDim=", eDim, " nbCase=", nbCase, " eSumInverse=", eSumInverse, "\n");
    od;
    RecEulerPoincareChar:=rec(SumEulerPoincareChar:=SumEulerPoincareChar,
                              ListSumInverse:=ListSumInverse);
    SaveDataToFilePlusTouch(FileSave, RecEulerPoincareChar);
  fi;
  Print("SumEulerPoincareChar=", RecEulerPoincareChar.SumEulerPoincareChar, "\n");
  #
  # Computation of additional data for zone contraction
  #
  Print("Before computation of additional table information\n");
  FileSave:="DATA_TEMP/TableData_ZoneContractedGeneralized";
#  RemoveFileIfExistPlusTouch(FileSave);
  if IsExistingFilePlusTouch(FileSave) then
    TheInfoZoneContGen:=ReadAsFunction(FileSave)();
  else
    SecFileSave:=Concatenation("DATA_TEMP/ZoneContractions_", String(n));
    TheData:=ReadAsFunction(SecFileSave)();
    PreTheInfoZoneContGen:=[];
    nbRec:=Length(TheData.ListZoneContractedGeneralized);
    for iRec in [1..nbRec]
    do
      eRec:=TheData.ListZoneContractedGeneralized[iRec];
      Print("iRec=", iRec, " / ", nbRec, "\n");
      nbFamily:=Length(eRec.ListSubFamily);
      #
      ListVect:=[];
      PreListStr:=[];
      PreListSort:=[];
      for eMat in eRec.eConfHigh
      do
        eRecDescRay:=GetMatrixSymbol(eMat);
	eVect:=SymmetricMatrixToVector(eMat);
	Add(ListVect, eVect);
	Add(PreListStr, eRecDescRay.str);
	Add(PreListSort, eRecDescRay.sortInfo);
      od;
      ePerm:=SortingPerm(PreListSort);
      ListStr:=Permuted(PreListStr, ePerm);
      ListSort:=Permuted(PreListSort, ePerm);
      dim:=RankMat(ListVect);
      #
      eColl:=Collected(ListStr);
      TotStr:="\$";
      for eEnt in eColl
      do
        eMult:=eEnt[2];
	if eMult=1 then
	  TotStr:=Concatenation(TotStr, eEnt[1]);
	else
	  TotStr:=Concatenation(TotStr, eEnt[1], "^{", String(eEnt[2]), "}");
	fi;
      od;
      TotStr:=Concatenation(TotStr, "\$");
      #
      LFC:=DelaunayComputationStandardFunctions(eRec.SumHighRank);
      RecVor:=LFC.GetVoronoiVertices();
      eSymbol:=Concatenation(String(Length(RecVor.FAC)), ",", String(Length(RecVor.EXT)));
      IsZoneContracted:=Position(eRec.ListRank,1)=fail;
      #
      TheSortInfo:=[dim, ListSort];
      eInfo:=rec(iRec:=iRec, TotStr:=TotStr, TheSortInfo:=TheSortInfo, eSymbol:=eSymbol, nbFamily:=nbFamily, dim:=dim, IsZoneContracted:=IsZoneContracted);
      Add(PreTheInfoZoneContGen, eInfo);
    od;
    ePermFinal:=SortingPerm(List(PreTheInfoZoneContGen, x->x.TheSortInfo));
    TheInfoZoneContGen:=Permuted(PreTheInfoZoneContGen, ePermFinal);
    SaveDataToFilePlusTouch(FileSave, TheInfoZoneContGen);
  fi;
  Print("After computation of additional table information\n");
  #
  # Now the table itself
  #
  Print("Now building the table\n");
  PrintSeriesInTable:=function(ListCase, nbCol, DoZoneCont)
    local iCol, nbEnt, nbCase, nbLine, iLine, iCase, eCase, nbContDomain, idx;
    AppendTo(output, "\\begin{center}\n");
    AppendTo(output, "\\begin{tabular}{|");
    for iCol in [1..nbCol]
    do
      if DoZoneCont=false then
        AppendTo(output, "c|c|c|c|");
      else
        AppendTo(output, "c|c|c|c|c|");
      fi;
    od;
    AppendTo(output, "}\n");
    #
    nbEnt:=nbCol*4;
    AppendTo(output, "\\cline{1-", nbEnt, "}\n");
    for iCol in [1..nbCol]
    do
      if iCol > 1 then
        AppendTo(output, " & ");
      fi;
      if DoZoneCont=false then
        AppendTo(output, "dim & generator & symbol & nb sec. c.");
      else
        AppendTo(output, "dim & generator & symbol & nb sec. c. & nb cont. d.");
      fi;
    od;
    AppendTo(output, "\\\\\n");
    AppendTo(output, "\\cline{1-", nbEnt, "}\n");
    nbCase:=Length(ListCase);
    nbLine:=UpperInteger(nbCase/nbCol);
    for iLine in [1..nbLine]
    do
      for iCol in [1..nbCol]
      do
        if iCol > 1 then
	  AppendTo(output, " & ");
	fi;
        iCase:=iLine + nbLine*(iCol-1);
	if iCase <= nbCase then
	  idx:=ListCase[iCase];
          eCase:=TheInfoZoneContGen[idx];
          nbContDomain:=BigRecCont.ListNumberContractionDomain[idx];
          if DoZoneCont=false then
            AppendTo(output, eCase.dim, " & ", eCase.TotStr, " & ", eCase.eSymbol, " & ", eCase.nbFamily);
          else
            AppendTo(output, eCase.dim, " & ", eCase.TotStr, " & ", eCase.eSymbol, " & ", eCase.nbFamily, " & ", nbContDomain);
          fi;
	else
          if DoZoneCont=false then
            AppendTo(output, " & & & ");
          else
            AppendTo(output, " & & & & ");
          fi;
	fi;
      od;
      AppendTo(output, "\\\\\n");
    od;
    AppendTo(output, "\\cline{1-", nbEnt, "}\n");
    AppendTo(output, "\\end{tabular}\n");
    AppendTo(output, "\\end{center}\n");
    AppendTo(output, "\n\n");
  end;
  #
  eFileTex:="Tables/Table_Irreducible_pre.tex";
  RemoveFileIfExist(eFileTex);
  output:=OutputTextFile(eFileTex, true);
  nbOrb:=Length(TheInfoZoneContGen);
  ListCaseZoneContracted:=Filtered([1..nbOrb], x->TheInfoZoneContGen[x].IsZoneContracted=true);
  PrintSeriesInTable(ListCaseZoneContracted, 3, false);
  ListCaseOther:=Filtered([1..nbOrb], x->TheInfoZoneContGen[x].IsZoneContracted=false);
  PrintSeriesInTable(ListCaseOther, 2, true);
  CloseStream(output);
  LATEX_Compilation(eFileTex);
  #
  # Table presenting nr of contraction domains and secondary cones
  #
  ListNumberContractionDomain:=List(BigRecCont.ListListContractionDomain, Length);
  ListNumberLtypeDomain:=[];
  for eDim in [1..TheDim]
  do
    eFile:=Concatenation("DATA_TEMP/List", String(n), "_rnk", String(eDim));
    eRecEnum:=ReadAsFunction(eFile)();
    Add(ListNumberLtypeDomain, Length(eRecEnum.ListConfiguration));
  od;
  ListLine:=[];
  for eDim in [1..TheDim]
  do
    eLine:=[String(eDim), String(ListNumberLtypeDomain[eDim]), String(ListNumberContractionDomain[eDim])];
    Add(ListLine, eLine);
  od;
  ListHeader:=["n", "nr. sec. c.", "nr. cont. c."];
  eFileTex:="Tables/Table_NumberLtypeContDomain_pre.tex";
  nbCol:=2;
  VOR_PrintListLine(ListLine, ListHeader, nbCol, eFileTex);
  #
  # total number of contraction domains
  #
#  Print("ListCaseOther=", ListCaseOther, "\n");
  Print("TotalNumberContractionDomain=", Sum(ListNumberContractionDomain), "\n");
end;



VOR_LTYPE_ComputeCanonicalStrings:=function(n)
  local TheDim, rnk, eFile, ListString, eConf, SumConf, LFC, RecVor, TheCanon, FileSave, eRecEnum;
  TheDim:=n*(n+1)/2;
  for rnk in [1..TheDim]
  do
    Print("rnk=", rnk, "\n");
    eFile:=Concatenation("DATA_TEMP/List", String(n), "_rnk", String(rnk));
    eRecEnum:=ReadAsFunction(eFile)();
    ListString:=[];
    for eConf in eRecEnum.ListConfiguration
    do
      SumConf:=Sum(eConf);
      LFC:=DelaunayComputationStandardFunctions(SumConf);
      RecVor:=LFC.GetVoronoiVertices();
      TheCanon:=RecVor.GetCanonicalGraph();
      Add(ListString, rec(str:=TheCanon));
    od;
    FileSave:=Concatenation("DATA_TEMP/Canonical", String(n), "_rnk", String(rnk));
    SaveDataToFilePlusTouch(FileSave, ListString);
  od;
end;



VOR_LTYPE_ComputeFaceLatticeVoronoi:=function(n, RecOpt)
  local TheDim, rnk, eFile, ListInfoSkel, eConf, SumConf, LFC, RecVor, TheCanon, FileSave, eRecEnum, TheSkel, TheInfoSkel, output, FileOut, iConf, u, dim, eList, eLine, eVal, NeedComputation;
  TheDim:=n*(n+1)/2;
  for rnk in [1..TheDim]
  do
    Print("rnk=", rnk, "\n");
    eFile:=Concatenation("DATA_TEMP/List", String(n), "_rnk", String(rnk));
    NeedComputation:=false;
    if RecOpt.SaveFaceLattice then
      FileSave:=Concatenation("DATA_TEMP/FaceLattice", String(n), "_rnk", String(rnk));
      if IsExistingFile(FileSave)=false then
        NeedComputation:=true;
      fi;
    fi;
    if RecOpt.ExportAlexeyGarber then
      FileOut:=Concatenation("DATA_TEMP/FaceLatt_", String(n), "_", String(rnk), ".txt");
      if IsExistingFile(FileOut)=false then
        NeedComputation:=true;
      fi;
    fi;
    if NeedComputation then
      eRecEnum:=ReadAsFunction(eFile)();
      if RecOpt.SaveFaceLattice then
        ListInfoSkel:=[];
      fi;
      if RecOpt.ExportAlexeyGarber then
        output:=OutputTextFile(FileOut, true);
        AppendTo(output, Length(eRecEnum.ListConfiguration), "\n");
        iConf:=0;
      fi;
      for eConf in eRecEnum.ListConfiguration
      do
        SumConf:=Sum(eConf);
        LFC:=DelaunayComputationStandardFunctions(SumConf);
        RecVor:=LFC.GetVoronoiVertices();
        TheInfoSkel:=RecVor.GetFaceLattice();
        if RecOpt.SaveFaceLattice then
          Add(ListInfoSkel, TheInfoSkel);
        fi;
        if RecOpt.ExportAlexeyGarber then
          iConf:=iConf+1;
          AppendTo(output, iConf, "\n");
          #
          AppendTo(output, Length(TheInfoSkel.EXT), "\n");
          WriteMatrix(output, TheInfoSkel.EXT);
          #
          AppendTo(output, Length(TheInfoSkel.FAC), "\n");
          WriteMatrix(output, TheInfoSkel.FAC);
          #
          dim:=Length(TheInfoSkel.eSymbol)-1;
          AppendTo(output, dim, "\n");
          for u in [1..dim]
          do
            eList:=TheInfoSkel.eSymbol[u];
            AppendTo(output, Length(eList), "\n");
            for eLine in eList
            do
              AppendTo(output, Length(eLine), " :");
              for eVal in eLine
              do
                AppendTo(output, " ", eVal);
              od;
              AppendTo(output, "\n");
            od;
          od;
        fi;
      od;
      if RecOpt.SaveFaceLattice then
        SaveDataToFilePlusTouch(FileSave, ListInfoSkel);
      fi;
      if RecOpt.ExportAlexeyGarber then
        CloseStream(output);
      fi;
    fi;
  od;
end;





VOR_LTYPE_ComputeTwoDimComplexes:=function(n)
  local TheDim, rnk, eFile, ListInfoSkel, eConf, SumConf, LFC, RecVor, TheCanon, FileSave, eRecEnum, TheSkel, TheInfoSkel, output, FileOut, iConf, u, dim, eList, eLine, eVal, NeedComputation, TheTwoDimComplex, eSimp, cplx, edges, mat0, mat1, TheDimSpa;
  TheDim:=n*(n+1)/2;
  for rnk in [1..TheDim]
  do
    Print("rnk=", rnk, "\n");
    eFile:=Concatenation("DATA_TEMP/List", String(n), "_rnk", String(rnk));
    NeedComputation:=false;
    #
    FileOut:=Concatenation("DATA_TEMP/TwoDimComplexes_", String(n), "_", String(rnk), ".txt");
    if IsExistingFile(FileOut)=false then
      NeedComputation:=true;
    fi;
    if NeedComputation then
      eRecEnum:=ReadAsFunction(eFile)();
      output:=OutputTextFile(FileOut, true);
      AppendTo(output, Length(eRecEnum.ListConfiguration), "\n");
      iConf:=0;
      for eConf in eRecEnum.ListConfiguration
      do
        SumConf:=Sum(eConf);
        LFC:=DelaunayComputationStandardFunctions(SumConf);
        TheTwoDimComplex:=LFC.GetMagazinovTwoDimensionalComplex();
        #
        iConf:=iConf+1;
        AppendTo(output, iConf, "\n");
        AppendTo(output, Length(TheTwoDimComplex), "\n");
        #
        for eSimp in TheTwoDimComplex
        do
          for eVal in eSimp
          do
            AppendTo(output, " ", eVal);
          od;
          AppendTo(output, "\n");
        od;
        #
      od;
      CloseStream(output);
    fi;
  od;
end;



VOR_LTYPE_ExportFaceLatticeAlexeyGarber:=function(n)
  local TheDim, rnk, FileSave, ListInfoSkel, FileOut, output, iCase, TheInfoSkel, dim, u, eList, eLine, eVal;
  TheDim:=n*(n+1)/2;
  for rnk in [1..TheDim]
  do
    FileSave:=Concatenation("DATA_TEMP/FaceLattice", String(n), "_rnk", String(rnk));
    ListInfoSkel:=ReadAsFunction(FileSave)();
    Print("rnk=", rnk, " in VOR_LTYPE_ExportFaceLatticeAlexeyGarber |ListInfoSkel|=", Length(ListInfoSkel), "\n");
    #
    FileOut:=Concatenation("DATA_TEMP/FaceLatt_", String(n), "_", String(rnk), ".txt");
    RemoveFileIfExist(FileOut);
    output:=OutputTextFile(FileOut, true);
    AppendTo(output, Length(ListInfoSkel), "\n");
    for iCase in [1..Length(ListInfoSkel)]
    do
      TheInfoSkel:=ListInfoSkel[iCase];
      AppendTo(output, iCase, "\n");
      #
      AppendTo(output, Length(TheInfoSkel.EXT), "\n");
      WriteMatrix(output, TheInfoSkel.EXT);
      #
      AppendTo(output, Length(TheInfoSkel.FAC), "\n");
      WriteMatrix(output, TheInfoSkel.FAC);
      #
      dim:=Length(TheInfoSkel.eSymbol)-1;
      AppendTo(output, dim, "\n");
      for u in [1..dim]
      do
        eList:=TheInfoSkel.eSymbol[u];
	AppendTo(output, Length(eList), "\n");
	for eLine in eList
	do
	  AppendTo(output, Length(eLine), " :");
	  for eVal in eLine
	  do
	    AppendTo(output, " ", eVal);
	  od;
	  AppendTo(output, "\n");
	od;
      od;
    od;
    CloseStream(output);
  od;
end;





VOR_LTYPE_ComputeSubordinationInformation:=function(n)
  local TheDim, rnk, eFile, ListSubordination, eConf, SumConf, LFC, RecVor, TheCanon, FileSave, eRecEnum, TheSub;
  TheDim:=n*(n+1)/2;
  for rnk in [1..TheDim]
  do
    Print("rnk=", rnk, "\n");
    eFile:=Concatenation("DATA_TEMP/List", String(n), "_rnk", String(rnk));
    eRecEnum:=ReadAsFunction(eFile)();
    ListSubordination:=[];
    for eConf in eRecEnum.ListConfiguration
    do
      SumConf:=Sum(eConf);
      LFC:=DelaunayComputationStandardFunctions(SumConf);
      RecVor:=LFC.GetVoronoiVertices();
      TheSub:=RecVor.GetSubordinationInformation();
      Add(ListSubordination, TheSub);
    od;
    FileSave:=Concatenation("DATA_TEMP/SUB/Subordination", String(n), "_rnk", String(rnk));
    SaveDataToFilePlusTouch(FileSave, ListSubordination);
  od;
end;


VOR_LTYPE_ComputeEXT_FAC:=function(n)
  local TheDim, rnk, eFile, eConf, SumConf, LFC, RecVor, TheCanon, FileSave, eRecEnum, TheSub, BlockSize, iBlock, nbBlock, iFirst, iLast, NewBlock, NRec, nbConf, iConf;
  TheDim:=n*(n+1)/2;
  BlockSize:=500;
  for rnk in [1..TheDim]
  do
    Print("rnk=", rnk, "\n");
    eFile:=Concatenation("DATA_TEMP/List", String(n), "_rnk", String(rnk));
    eRecEnum:=ReadAsFunction(eFile)();
    nbConf:=Length(eRecEnum.ListConfiguration);
    nbBlock:=UpperInteger(nbConf / BlockSize);
    for iBlock in [1..nbBlock]
    do
      iFirst:=BlockSize*(iBlock-1) + 1;
      iLast:=Minimum(nbConf, BlockSize*iBlock);
      NewBlock:=[];
      for iConf in [iFirst..iLast]
      do
        eConf:=eRecEnum.ListConfiguration[iConf];
        SumConf:=Sum(eConf);
        LFC:=DelaunayComputationStandardFunctions(SumConf);
        RecVor:=LFC.GetVoronoiVertices();
        NRec:=rec(EXT:=RecVor.EXT, FAC:=RecVor.FAC);
        Add(NewBlock, NRec);
      od;
      FileSave:=Concatenation("DATA_TEMP/EXT_FAC", String(n), "_rnk", String(rnk), "_bl", String(iBlock));
      SaveDataToFilePlusTouch(FileSave, NewBlock);
    od;
  od;
end;


VOR_LTYPE_ComputeListDelaunay:=function(n)
  local TheDim, ListDelaunay, FuncInsertDelaunay, rnk, eFile, eConf, SumConf, LFC, eRecDel, eRecEnum;
  TheDim:=n*(n+1)/2;
  ListDelaunay:=[];
  FuncInsertDelaunay:=function(eEXT)
    local fEXT, eTest;
    for fEXT in ListDelaunay
    do
      eTest:=LinPolytopeIntegral_Isomorphism(eEXT, fEXT);
      if eTest<>false then
        return;
      fi;
    od;
    Add(ListDelaunay, eEXT);
  end;
  for rnk in [1..TheDim]
  do
    Print("rnk=", rnk, "\n");
    eFile:=Concatenation("DATA_TEMP/List", String(n), "_rnk", String(rnk));
    eRecEnum:=ReadAsFunction(eFile)();
    for eConf in eRecEnum.ListConfiguration
    do
      SumConf:=Sum(eConf);
      LFC:=DelaunayComputationStandardFunctions(SumConf);
      for eRecDel in LFC.GetDelaunayDescription()
      do
        FuncInsertDelaunay(eRecDel.EXT);
      od;
    od;
  od;
  return ListDelaunay;
end;








VOR_LTYPE_GetLtype_Numbers:=function(n)
  local ListNB, rnk, eFile, eRecEnum, TheDim;
  ListNB:=[];
  TheDim:=n*(n+1)/2;
  for rnk in [1..TheDim]
  do
    Print("rnk=", rnk, "\n");
    eFile:=Concatenation("DATA_TEMP/List", String(n), "_rnk", String(rnk));
    eRecEnum:=ReadAsFunction(eFile)();
    Add(ListNB, Length(eRecEnum.ListConfiguration));
  od;
  return ListNB;
end;




VOR_LTYPE_TableNrExtRay:=function(n)
  local ListListNB, TheDim, rnk, eFile, eRecEnum, eListNB, TotalSet, nbVal, ListColumn, pos, eFileTex, TheMatrix, eVal;
  ListListNB:=[];
  TheDim:=n*(n+1)/2;
  TotalSet:=[];
  for rnk in [1..TheDim]
  do
    Print("VOR_LTYPE_TableNrExtRay, rnk=", rnk, " / ", TheDim, "\n");
    eFile:=Concatenation("DATA_TEMP/List", String(n), "_rnk", String(rnk));
    eRecEnum:=ReadAsFunction(eFile)();
    eListNB:=List(eRecEnum.ListConfiguration, Length);
    TotalSet:=Union(TotalSet, Set(eListNB));
    Add(ListListNB, eListNB);
  od;
  Print("TotalSet=", TotalSet, "\n");
  nbVal:=Length(TotalSet);
  TheMatrix:=NullMat(nbVal, TheDim);
  ListColumn:=[];
  for rnk in [1..TheDim]
  do
    Add(ListColumn, rnk);
    for eVal in ListListNB[rnk]
    do
      pos:=Position(TotalSet, eVal);
      TheMatrix[pos][rnk]:=TheMatrix[pos][rnk]+1;
    od;
  od;
  eFileTex:="Tables/TableNrExtRay_pre.tex";
  VOR_PrintMatrix(ListColumn, TotalSet, TheMatrix, eFileTex);
  return ListListNB;
end;


