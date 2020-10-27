GetGroupIdentifications:=function(TheBound)
  local ListGroups, GetGroupIndex, ListGroupSymbol, i, nbOrbit, iOrbit, eOrbit, TheStab, ListIdx, TheIdx, ListPermGroup, eGroup, TheLen;
  ListGroups:=[];
  GetGroupIndex:=function(eGRP)
    local fGRP, test, iGRP;
    for iGRP in [1..Length(ListGroups)]
    do
      fGRP:=ListGroups[iGRP];
      test:=IsomorphismGroups(eGRP, fGRP);
      if test<>fail then
        return iGRP;
      fi;
    od;
    Add(ListGroups, eGRP);
    return Length(ListGroups);
  end;
  ListGroupSymbol:=[ [] ];
  TheLen:=Length(TheBound.ListOrbitByRank); 
  for i in [2..TheLen]
  do
    nbOrbit:=Length(TheBound.ListOrbitByRank[i]);
    ListIdx:=[];
    for iOrbit in [1..nbOrbit]
    do
      eOrbit:=TheBound.ListOrbitByRank[i][iOrbit];
      TheStab:=eOrbit.TheStab;
      TheIdx:=GetGroupIndex(TheStab);
      Add(ListIdx, TheIdx);
    od;
    Add(ListGroupSymbol, ListIdx);
  od;
  return rec(ListGroupSymbol:=ListGroupSymbol, ListGroups:=ListGroups);
end;



PrintGroupInformationPolyhedralInformation:=function(PolyhedralInformation)
  local TheLen, i, nbOrbit, iOrbit, TheStan, eOrbit, TheStab, SizBound, nbCase, iCase, GetPranks, eGRP, ListGroups, FuncInsert;
  TheLen:=Length(PolyhedralInformation.ListOrbitByRank);
  ListGroups:=[];
  FuncInsert:=function(eGRP)
    local fGRP, test;
    for fGRP in ListGroups
    do
      test:=IsomorphismGroups(eGRP, fGRP);
      if test<>fail then
        return;
      fi;
    od;
    Add(ListGroups, eGRP);
  end;
  GetPranks:=function(eGRP)
    local TheOrd, ListFactor, ListInfos, eFac, TheSylow, eInfo;
    TheOrd:=Order(eGRP);
    ListFactor:=Set(FactorsInt(TheOrd));
    ListInfos:=[];
    for eFac in ListFactor
    do
      TheSylow:=SylowSubgroup(eGRP, eFac);
      eInfo:=rec(p:=eFac, pRank:=Prank(TheSylow));
      Add(ListInfos, eInfo);
    od;
    return ListInfos;
  end;
  for i in [2..TheLen]
  do
    nbOrbit:=Length(PolyhedralInformation.ListOrbitByRank[i]);
    Print("i=", i, "\n");
    for iOrbit in [1..nbOrbit]
    do
      eOrbit:=PolyhedralInformation.ListOrbitByRank[i][iOrbit];
      TheStab:=eOrbit.TheStab;
      FuncInsert(TheStab);
      SizBound:=Length(eOrbit.BoundaryImage.ListElt);
      Print("  iOrbit=", iOrbit, " |Stab|=", Order(TheStab), " SizBound=", SizBound, "\n");
    od;
  od;
  nbCase:=Length(ListGroups);
  for iCase in [1..nbCase]
  do
    eGRP:=ListGroups[iCase];
    Print(" iCase=", iCase, " |G|=", Order(eGRP), " RankInfo=", GetPranks(eGRP), "\n");
  od;
  return ListGroups;
end;




DomainSplitting:=function(OrbitwiseTesselation, ListOrbitSplitted)
  local nbOrbitOld, iOrbit, nbOrbitFacet, iOrbFac, GetFacetInfos, NewTesselation, iOrbitOld, TheStab, NewListAdj, eOrbAdj, jOrbitAdj, eMat1, eFac, pos, eAdj, eFacINFO, eCall, eRecord, ListOrbitNames, iOrbAdj, ListPermGens, ListMatrGens, ListRepFac, TheMatrixStab, TheInvariantVector, ListFacets, ListOrigins, CongrGRP, eList, eGen, PermGRP, phi, TheStabCongr, ListAdj, eFacSought, eFacSought2, pos2, NSP1, NSP2, NSP3, eMatr, ePerm, TheRelOrigin, TheRelAdj, O, TheOrb, eFacInvVect, test, TheStabPerm, eO, posFac, n;
  if Length(Set(ListOrbitSplitted))<>Length(ListOrbitSplitted) then
    Error("No repetition allowed in orbit splitting");
  fi;
  n:=Length(OrbitwiseTesselation[1].ListAdj[1].eFac);
  nbOrbitOld:=Length(OrbitwiseTesselation);
  ListOrbitNames:=[];
  for iOrbit in [1..nbOrbitOld]
  do
    if Position(ListOrbitSplitted, iOrbit)=fail then
      Add(ListOrbitNames, [iOrbit, 0]);
    fi;
  od;
  for iOrbit in ListOrbitSplitted
  do
    nbOrbitFacet:=Length(OrbitwiseTesselation[iOrbit].ListAdj);
    for iOrbFac in [1..nbOrbitFacet]
    do
      Add(ListOrbitNames, [iOrbit, iOrbFac]);
    od;
  od;
  GetFacetInfos:=function(TheRecord, eTransform)
    local ListStabGensCongr, CongrGRP, ListFacets, ListOrigins, iOrbAdj, eAdj, TheOrb, FindElement, eFacRef, ListCases;
    ListStabGensCongr:=List(GeneratorsOfGroup(TheRecord.MatrixStab), x->CongrMap(Inverse(eTransform)*x*eTransform));
    CongrGRP:=PersoGroupMatrix(ListStabGensCongr, n);
    ListFacets:=[];
    ListOrigins:=[];
    ListCases:=[];
    for iOrbAdj in [1..Length(TheRecord.ListAdj)]
    do
      eAdj:=TheRecord.ListAdj[iOrbAdj];
      eFacRef:=eAdj.eFac*CongrMap(eTransform);
      Add(ListCases, eFacRef);
      TheOrb:=Orbit(CongrGRP, eFacRef, OnPoints);
      Append(ListFacets, TheOrb);
      Append(ListOrigins, ListWithIdenticalEntries(Length(TheOrb), iOrbAdj));
    od;
    FindElement:=function(eFac)
      local pos, TheOrigin, eRepr;
      pos:=Position(ListFacets, eFac);
      TheOrigin:=ListOrigins[pos];
      eRepr:=RepresentativeAction(CongrGRP, ListCases[TheOrigin], eFac, OnPoints);
      if eRepr=fail then
        Error("Please debug from here");
      fi;
      return rec(TheOrigin:=TheOrigin, eRepr:=CongrMap(eRepr));
    end;
    return rec(ListFacets:=ListFacets, FindElement:=FindElement);
  end;
  NewTesselation:=[];
  for iOrbitOld in [1..nbOrbitOld]
  do
    if Position(ListOrbitSplitted, iOrbitOld)=fail then
      NewListAdj:=[];
      for eOrbAdj in OrbitwiseTesselation[iOrbitOld].ListAdj
      do
        jOrbitAdj:=eOrbAdj.iRecord;
        eMat1:=eOrbAdj.eEquiv;
        eFac:=eOrbAdj.eFac;
        if Position(ListOrbitSplitted, jOrbitAdj)=fail then
          pos:=Position(ListOrbitNames, [jOrbitAdj, 0]);
          eAdj:=rec(iRecord:=pos, eEquiv:=eMat1, eFac:=eFac);
        else
          eFacINFO:=GetFacetInfos(OrbitwiseTesselation[jOrbitAdj], eMat1);
          eCall:=eFacINFO.FindElement(-eFac);
          pos:=Position(ListOrbitNames, [jOrbitAdj, eCall.TheOrigin]);
          eAdj:=rec(iRecord:=pos, eEquiv:=eMat1*eCall.eRepr, eFac:=eFac);
        fi;
        Add(NewListAdj, eAdj);
      od;
      TheStab:=OrbitwiseTesselation[iOrbitOld].MatrixStab;
      eRecord:=rec(MatrixStab:=TheStab, ListAdj:=NewListAdj, iOrbitOld:=iOrbitOld);
      Add(NewTesselation, eRecord);
    fi;
  od;
  for iOrbitOld in ListOrbitSplitted
  do
    nbOrbitFacet:=Length(OrbitwiseTesselation[iOrbitOld].ListAdj);
    ListRepFac:=List(OrbitwiseTesselation[iOrbitOld].ListAdj, x->x.eFac);
    TheMatrixStab:=OrbitwiseTesselation[iOrbitOld].MatrixStab;
    TheInvariantVector:=GetSpaceInteriorPoint([], ListRepFac, TheMatrixStab);
    ListFacets:=[];
    ListOrigins:=[];
    ListMatrGens:=List(GeneratorsOfGroup(TheMatrixStab), CongrMap);
    CongrGRP:=PersoGroupMatrix(ListMatrGens, n);
    for iOrbAdj in [1..Length(OrbitwiseTesselation[iOrbitOld].ListAdj)]
    do
      eAdj:=OrbitwiseTesselation[iOrbitOld].ListAdj[iOrbAdj];
      TheOrb:=Orbit(CongrGRP, eAdj.eFac, OnPoints);
      Append(ListFacets, TheOrb);
      Append(ListOrigins, ListWithIdenticalEntries(Length(TheOrb), iOrbAdj));
    od;
    ListPermGens:=[];
    for eGen in ListMatrGens
    do
      eList:=List(ListFacets, x->Position(ListFacets, x*eGen));
      Add(ListPermGens, PermList(eList));
    od;
    PermGRP:=PersoGroupPerm(ListPermGens);
    phi:=GroupHomomorphismByImagesNC(PermGRP, CongrGRP, ListPermGens, ListMatrGens);
    for iOrbAdj in [1..nbOrbitFacet]
    do
      eFac:=OrbitwiseTesselation[iOrbitOld].ListAdj[iOrbAdj].eFac;
      jOrbitAdj:=OrbitwiseTesselation[iOrbitOld].ListAdj[iOrbAdj].iRecord;
      eMat1:=OrbitwiseTesselation[iOrbitOld].ListAdj[iOrbAdj].eEquiv;
      posFac:=Position(ListFacets, eFac);
      TheStabPerm:=Stabilizer(PermGRP, posFac, OnPoints);
      TheStabCongr:=Image(phi, TheStabPerm);
      TheStab:=PersoGroupMatrix(List(GeneratorsOfGroup(TheStabCongr), CongrMap),n);
      ListAdj:=[];
      if Position(ListOrbitSplitted, jOrbitAdj)=fail then
        pos:=Position(ListOrbitNames, [jOrbitAdj, 0]);
        eAdj:=rec(iRecord:=pos, eEquiv:=eMat1, eFac:=eFac);
      else
        eFacINFO:=GetFacetInfos(OrbitwiseTesselation[jOrbitAdj], eMat1);
        eCall:=eFacINFO.FindElement(-eFac);
        pos:=Position(ListOrbitNames, [jOrbitAdj, eCall.TheOrigin]);
        eAdj:=rec(iRecord:=pos, eEquiv:=eMat1*eCall.eRepr, eFac:=eFac);
      fi;
      Add(ListAdj, eAdj);
      O:=Orbits(TheStabPerm, Difference([1..Length(ListFacets)], [posFac]), OnPoints);
      eFacInvVect:=GetSpaceInteriorPoint([eFac], Difference(Set(ListFacets), [eFac]), TheStab);
      for eO in O
      do
        test:=TestAdjacency(ListFacets[posFac], ListFacets[eO[1]], ListFacets, []);
        if test=true then
          TheRelOrigin:=ListOrigins[eO[1]];
          TheRelAdj:=OrbitwiseTesselation[iOrbitOld].ListAdj[TheRelOrigin];
          pos:=Position(ListFacets, TheRelAdj.eFac);
          ePerm:=RepresentativeAction(PermGRP, pos, eO[1], OnPoints);
          eMatr:=Image(phi, ePerm);
          NSP1:=NullspaceMat(TransposedMat([ListFacets[posFac], ListFacets[eO[1]]]));
          NSP2:=Concatenation(ShallowCopy(NSP1), [TheInvariantVector]);
          NSP3:=NullspaceMat(TransposedMat(NSP2));
          if Length(NSP3)<>1 then
            Error("We have inconsistency here");
          fi;
          eFacSought:=RemoveFraction(NSP3[1]);
          if eFacSought*eFacInvVect > 0 then
            eFacSought2:=ShallowCopy(eFacSought);
          elif eFacSought*eFacInvVect < 0 then
            eFacSought2:=ShallowCopy(-eFacSought);
          else
            Error("We have inconsistency, please panic");
          fi;
          pos2:=Position(ListOrbitNames, [iOrbitOld, TheRelOrigin]);
          eAdj:=rec(iRecord:=pos2, eEquiv:=CongrMap(eMatr), eFac:=eFacSought2);
          Add(ListAdj, eAdj);
        fi;
      od;
      eRecord:=rec(MatrixStab:=TheStab, ListAdj:=ListAdj, iOrbitSplit:=iOrbitOld, iOrbAdj:=iOrbAdj);
      Add(NewTesselation, eRecord);
    od;
  od;
  return NewTesselation;
end;



GetListListAll:=function(OrbitwiseTesselation)
  local n, ListListFacets, ListListOrigin, ListPermStab, ListListRepr, ListPhi, iOrbitOld, TheRecord, ListMatrGens, TheCongrStab, ListFacets, ListOrigin, nbAdj, ListRepr, iAdj, eFac, TheO, iRepr, ListPermGens, eGen, eList, GRPperm, phi, ListListSizes, ListSizes, ListInvariantVect, eInvVect, ListRepFacets;
  n:=Length(OrbitwiseTesselation[1].ListAdj[1].eFac);
  ListListFacets:=[];
  ListListOrigin:=[];
  ListPermStab:=[];
  ListListRepr:=[];
  ListListSizes:=[];
  ListInvariantVect:=[];
  ListPhi:=[];
  for TheRecord in OrbitwiseTesselation
  do
    ListMatrGens:=GeneratorsOfGroup(TheRecord.MatrixStab);
    TheCongrStab:=PersoGroupMatrix(List(ListMatrGens, CongrMap), n);
    ListRepFacets:=List(TheRecord.ListAdj, x->x.eFac);
    eInvVect:=GetSpaceInteriorPoint([], ListRepFacets, TheRecord.MatrixStab);
    Add(ListInvariantVect, eInvVect);
    ListFacets:=[];
    ListOrigin:=[];
    nbAdj:=Length(TheRecord.ListAdj);
    ListRepr:=[];
    ListSizes:=[];
    for iAdj in [1..nbAdj]
    do
      eFac:=TheRecord.ListAdj[iAdj].eFac;
      TheO:=Orbit(TheCongrStab, eFac, OnPoints);
      Add(ListSizes, Length(TheO));
      Append(ListFacets, TheO);
      Append(ListOrigin, ListWithIdenticalEntries(Length(TheO), iAdj));
      iRepr:=Position(ListFacets, eFac);
      Add(ListRepr, iRepr);
    od;
    Add(ListListFacets, ListFacets);
    Add(ListListRepr, ListRepr);
    Add(ListListOrigin, ListOrigin);
    Add(ListListSizes, ListSizes);
    ListPermGens:=[];
    for eGen in GeneratorsOfGroup(TheCongrStab)
    do
      eList:=List(ListFacets, x->Position(ListFacets, x*eGen));
      Add(ListPermGens, PermList(eList));
    od;
    GRPperm:=PersoGroupPerm(ListPermGens);
    Add(ListPermStab, GRPperm);
    phi:=GroupHomomorphismByImagesNC(GRPperm, TheRecord.MatrixStab, ListPermGens, ListMatrGens);
    Add(ListPhi, phi);
  od;
  return rec(n:=n,
             ListListFacets:=ListListFacets,
             ListListOrigin:=ListListOrigin,
             ListPermStab:=ListPermStab,
             ListListRepr:=ListListRepr,
             ListListSizes:=ListListSizes,
             ListPhi:=ListPhi,
             ListInvariantVect:=ListInvariantVect);
end;



CheckTilingFaceToFace:=function(PolyhedralTesselation)
  local AllInfo, nbOrb, ListEXT, iOrb, EXT, nbAdj, iAdj, eAdj, eFac, ListIncidentI, ImgListFacet, ImgEXT, ListIncidentJ, pos, jAdj, TheResult;
  AllInfo:=GetListListAll(PolyhedralTesselation);
  nbOrb:=Length(PolyhedralTesselation);
  ListEXT:=[];
  for iOrb in [1..nbOrb]
  do
    EXT:=DualDescription(AllInfo.ListListFacets[iOrb]);
    Add(ListEXT, EXT);
  od;
  TheResult:=true;
  for iOrb in [1..nbOrb]
  do
    nbAdj:=Length(PolyhedralTesselation[iOrb].ListAdj);
    for iAdj in [1..nbAdj]
    do
      eAdj:=PolyhedralTesselation[iOrb].ListAdj[iAdj];
      eFac:=eAdj.eFac;
      ListIncidentI:=Filtered(ListEXT[iOrb], x->x*eFac=0);
      ImgListFacet:=AllInfo.ListListFacets[eAdj.iRecord]*CongrMap(eAdj.eEquiv);
      ImgEXT:=ListEXT[eAdj.iRecord]*eAdj.eEquiv;
      ListIncidentJ:=Filtered(ImgEXT, x->x*eFac=0);
      if First(ImgEXT, x->x*eFac>0)<>fail then
        Error("Find an inside vertex, that is thorougly illegal");
      fi;
      pos:=Position(ImgListFacet, -eFac);
      jAdj:=AllInfo.ListListOrigin[eAdj.iRecord][pos];
      if Set(ListIncidentI)<>Set(ListIncidentJ) then
        Print("Not face to face for (", iOrb, ",", iAdj, ") <--> (", eAdj.iRecord, ",", jAdj, ")\n");
        TheResult:=false;
      fi;
    od;
  od;
  return TheResult;
end;

#
# the vector TheIRep is the number of one orbit of face
# for which we do the Splitting operation.
# TheFaceInteriorVector is a vector contained in the representative.
# the corresponding face of the splitting HAS to be completely
# invariant under the stabilizer of the face.
DomainSplittingGeneralized:=function(OrbitwiseTesselation, TheIRep, TheFaceInteriorVector)
  local nbOrbitOld, n, NewOrbitwiseTesselation, ListAdj, TheRecord, iRecordSought, TheRelOrigin, TheRelOrigin2, NewListOrbitNames, eNewAdj, eInfo, eFacSought, eOldAdj, eMatr, eMatr2, jFac, jFacCan, PermGRP2, ListPhi, ListPermStab, ListListRepr, ListIncident, ListListFacets, ListListOrigin, eEquivSought, nbNewOrbit, ePerm2, NSP1, jRepr, eFacInvVect, phi2, nbFac, ImgListFacetsJ, nbFacJ, eFacSought2, NSP2, NSP3, ListOrbitContaining, ListFacets, iRepr, PermGRP, ListRepr, ePerm, jReprCan, ListOrigin, test, eDiffSet, eO, O, posCan, pos, phi, eEquiv, eRelFac, eFac, iRecordOld, eAdj, iAdj, iRep, iRecordNew, ListIRep, eInteriorPt, ImgMatrStab, eStab, eOrbit, iOrbitNew, nbAdj, iOrbitCont, NewIRep, NewEquiv, IsFinished, eRec, hSet, ImgListFacets, FuncInsertOrbit, eMatrix, FindElement, idx, iOrbit, nbOrbCont, GRPperm, ListMatrGens, ListPermGens, TheCongrStab, eGen, TheO, eList, NewListAdj, posI, iFac, LINC;
  nbOrbitOld:=Length(OrbitwiseTesselation);
  n:=Length(OrbitwiseTesselation[1].ListAdj[1].eFac);
  ListListFacets:=[];
  ListListOrigin:=[];
  ListPermStab:=[];
  ListListRepr:=[];
  ListPhi:=[];
  for TheRecord in OrbitwiseTesselation
  do
    ListMatrGens:=GeneratorsOfGroup(TheRecord.MatrixStab);
    TheCongrStab:=PersoGroupMatrix(List(ListMatrGens, CongrMap), n);
    ListFacets:=[];
    ListOrigin:=[];
    nbAdj:=Length(TheRecord.ListAdj);
    ListRepr:=[];
    for iAdj in [1..nbAdj]
    do
      eFac:=TheRecord.ListAdj[iAdj].eFac;
      TheO:=Orbit(TheCongrStab, eFac, OnPoints);
      Append(ListFacets, TheO);
      Append(ListOrigin, ListWithIdenticalEntries(Length(TheO), iAdj));
      iRepr:=Position(ListFacets, eFac);
      Add(ListRepr, iRepr);
    od;
    Add(ListListFacets, ListFacets);
    Add(ListListRepr, ListRepr);
    Add(ListListOrigin, ListOrigin);
    ListPermGens:=[];
    for eGen in GeneratorsOfGroup(TheCongrStab)
    do
      eList:=List(ListFacets, x->Position(ListFacets, x*eGen));
      Add(ListPermGens, PermList(eList));
    od;
    GRPperm:=PersoGroupPerm(ListPermGens);
    Add(ListPermStab, GRPperm);
    phi:=GroupHomomorphismByImagesNC(GRPperm, TheRecord.MatrixStab, ListPermGens, ListMatrGens);
    Add(ListPhi, phi);
  od;
  FindElement:=function(eFac, iOrbitOld)
    local pos, TheRelOrigin, posCan, ePerm, eMatr;
    pos:=Position(ListListFacets[iOrbitOld], eFac);
    TheRelOrigin:=ListListOrigin[iOrbitOld][pos];
    posCan:=ListListRepr[iOrbitOld][TheRelOrigin];
    ePerm:=RepresentativeAction(ListPermStab[iOrbitOld], posCan, pos, OnPoints);
    eMatr:=Image(ListPhi[iOrbitOld], ePerm);
    return rec(iAdj:=TheRelOrigin, eRepr:=eMatr);
  end;
  ListOrbitContaining:=[];
  FuncInsertOrbit:=function(iRep, eMatrix)
    local ListFacetsImg, eSet, iOrbit, eEquiv, ePermStab, eInteriorPt, eGen, ListFacets, nbFacet;
    ListFacets:=ListListFacets[iRep];
    ListFacetsImg:=ListListFacets[iRep]*CongrMap(eMatrix);
    nbFacet:=Length(ListFacets);
    eSet:=Filtered([1..Length(ListFacetsImg)], x->ListFacetsImg[x]*TheFaceInteriorVector=0);
    for eGen in GeneratorsOfGroup(ListPermStab[iRep])
    do
      if OnSets(eSet, eGen)<>eSet then
        Print("Error in DomainSplittingGeneralized\n");
        Print("The face is not completely invariant, under the stabilizer\n");
        Print("You have to make another choice\n");
        Print("Please keep in mind that if a face is totally invariant\n");
        Print("for one top-dimensional cell, it may not be for other\n");
        Print("top dimensional cells\n");
        Print("Here iRep=", iRep, "\n");
        Print("|Stab|=", Order(ListPermStab[iRep]), "\n");
        Print("|O|=", Length(Orbit(ListPermStab[iRep], eSet, OnSets)), "\n");
        Error("Please correct");
      fi;
    od;
    for iOrbit in [1..Length(ListOrbitContaining)]
    do
      if iRep=ListOrbitContaining[iOrbit].iRep then
        eEquiv:=RepresentativeAction(ListPermStab[iRep], eSet, ListOrbitContaining[iOrbit].eSet, OnSets);
        if eEquiv=fail then
          Print("The face is represented several times, in the same\n");
          Print("orbit. This is not allowed\n");
          Error("Please correct");
        fi;
        return;
      fi;
    od;
    eInteriorPt:=GetSpaceInteriorPoint(ListFacets{eSet}, ListFacets{Difference([1..nbFacet], eSet)}, OrbitwiseTesselation[iRep].MatrixStab)*eMatrix;
    ePermStab:=ListPermStab[iRep];
    Add(ListOrbitContaining, rec(Status:="NO", eSet:=eSet, iRep:=iRep, eMatrix:=eMatrix, ePermStab:=ePermStab, eInteriorPt:=eInteriorPt));
  end;
  FuncInsertOrbit(TheIRep, IdentityMat(n));
  while(true)
  do
    IsFinished:=true;
    nbOrbCont:=Length(ListOrbitContaining);
    for iOrbit in [1..nbOrbCont]
    do
      if ListOrbitContaining[iOrbit].Status="NO" then
        IsFinished:=false;
        ListOrbitContaining[iOrbit].Status:="YES";
        iRep:=ListOrbitContaining[iOrbit].iRep;
        eMatrix:=ListOrbitContaining[iOrbit].eMatrix;
        nbFac:=Length(ListListFacets[iRep]);
        O:=Orbits(ListOrbitContaining[iOrbit].ePermStab, ListOrbitContaining[iOrbit].eSet, OnPoints);
        for eO in O
        do
          idx:=eO[1];
          eFac:=ListListFacets[iRep][idx];
          eRec:=FindElement(eFac, iRep);
          iAdj:=eRec.iAdj;
          NewEquiv:=OrbitwiseTesselation[iRep].ListAdj[iAdj].eEquiv*eRec.eRepr*eMatrix;
          NewIRep:=OrbitwiseTesselation[iRep].ListAdj[iAdj].iRecord;
          FuncInsertOrbit(NewIRep, NewEquiv);
        od;
      fi;
    od;
    if IsFinished=true then
      break;
    fi;
  od;
#  Print("ListOrbitContaining=", ListOrbitContaining, "\n");
  # conformity checks
  ListIRep:=List(ListOrbitContaining, x->x.iRep);
  #
  NewListOrbitNames:=[];
  for iRep in [1..nbOrbitOld]
  do
    if Position(ListIRep, iRep)=fail then
      Add(NewListOrbitNames, rec(Status:="old", OldIRep:=iRep, MatrixStab:=OrbitwiseTesselation[iRep].MatrixStab));
    fi;
  od;
  for iOrbitCont in [1..Length(ListOrbitContaining)]
  do
    eOrbit:=ListOrbitContaining[iOrbitCont];
    iRep:=eOrbit.iRep;
    nbFac:=Length(ListListFacets[iRep]);
    phi:=ListPhi[iRep];
    nbAdj:=Length(OrbitwiseTesselation[iRep].ListAdj);
    ImgListFacets:=ListListFacets[iRep]*CongrMap(eOrbit.eMatrix);
    eInteriorPt:=eOrbit.eInteriorPt*Inverse(eOrbit.eMatrix);
    for iAdj in [1..nbAdj]
    do
      iRepr:=ListListRepr[iRep][iAdj];
      if Position(eOrbit.eSet, iRepr)=fail then
        eStab:=Stabilizer(eOrbit.ePermStab, iRepr, OnPoints);
        ImgMatrStab:=PersoGroupMatrix(GeneratorsOfGroup(Image(phi, eStab)), n);
        Add(NewListOrbitNames, rec(Status:="new", OldIRep:=iRep, MatrixStab:=ImgMatrStab, iAdj:=iAdj, iOrbitCont:=iOrbitCont, ePermStab:=eStab, eInteriorPt:=eInteriorPt));
      fi;
    od;
  od;
  nbNewOrbit:=Length(NewListOrbitNames);
  NewOrbitwiseTesselation:=[];
  for iOrbitNew in [1..nbNewOrbit]
  do
    eInfo:=NewListOrbitNames[iOrbitNew];
    NewListAdj:=[];
    if eInfo.Status="old" then
      for eAdj in OrbitwiseTesselation[eInfo.OldIRep].ListAdj
      do
        eFac:=eAdj.eFac;
        eEquiv:=eAdj.eEquiv;
        iRecordOld:=eAdj.iRecord;
        if Position(ListIRep, iRecordOld)=fail then
          iRecordNew:=First([1..nbNewOrbit], x->NewListOrbitNames[x].Status="old" and NewListOrbitNames[x].OldIRep=iRecordOld);
          if iRecordNew=fail then
            Error("Debug from here 1");
          fi;
          eNewAdj:=rec(eFac:=eFac, iRecord:=iRecordNew, eEquiv:=eEquiv, type:="type 0");
        else
          eRelFac:=-eFac*CongrMap(Inverse(eEquiv));
          pos:=Position(ListListFacets[iRecordOld], eRelFac);
          TheRelOrigin:=ListListOrigin[iRecordOld][pos];
          posCan:=ListListRepr[iRecordOld][TheRelOrigin];
          ePerm:=RepresentativeAction(ListPermStab[iRecordOld], posCan, pos, OnPoints);
          eMatr:=Image(ListPhi[iRecordOld], ePerm);
          iRecordSought:=First([1..nbNewOrbit], x->NewListOrbitNames[x].Status="new" and NewListOrbitNames[x].OldIRep=iRecordOld and NewListOrbitNames[x].iAdj=TheRelOrigin);
          eEquivSought:=eMatr*eEquiv;
          if iRecordSought=fail then
            Error("Debug from here 2");
          fi;
          eNewAdj:=rec(eFac:=eFac, eEquiv:=eEquivSought, iRecord:=iRecordSought, type:="type 1");
        fi;
        Add(NewListAdj, eNewAdj);
      od;
    else
      # the main facet of adjacency,
      iAdj:=eInfo.iAdj;
      eAdj:=OrbitwiseTesselation[eInfo.OldIRep].ListAdj[iAdj];
      eEquiv:=eAdj.eEquiv;
      eFac:=eAdj.eFac;
      iRecordOld:=eAdj.iRecord;
      if Position(ListIRep, iRecordOld)=fail then
        iRecordNew:=First([1..nbNewOrbit], x->NewListOrbitNames[x].Status="old" and NewListOrbitNames[x].OldIRep=iRecordOld);
        if iRecordNew=fail then
          Error("Debug from here 6");
        fi;
        eNewAdj:=rec(eFac:=eFac, iRecord:=iRecordNew, eEquiv:=eEquiv, type:="type 3");
      else
        eRelFac:=-eFac*CongrMap(Inverse(eEquiv));
        pos:=Position(ListListFacets[iRecordOld], eRelFac);
        TheRelOrigin:=ListListOrigin[iRecordOld][pos];
        posCan:=ListListRepr[iRecordOld][TheRelOrigin];
        ePerm:=RepresentativeAction(ListPermStab[iRecordOld], posCan, pos, OnPoints);
        eMatr:=Image(ListPhi[iRecordOld], ePerm);
        iRecordSought:=First([1..nbNewOrbit], x->NewListOrbitNames[x].Status="new" and NewListOrbitNames[x].OldIRep=iRecordOld and NewListOrbitNames[x].iAdj=TheRelOrigin);
        eEquivSought:=eMatr*eEquiv;
        if iRecordSought=fail then
          Error("Debug from here 3");
        fi;
        eNewAdj:=rec(eFac:=eFac, eEquiv:=eEquivSought, iRecord:=iRecordSought, type:="type 4");
      fi;
      Add(NewListAdj, eNewAdj);
      #the other facets inside the cone.
      ListFacets:=ListListFacets[eInfo.OldIRep];
      ListOrigin:=ListListOrigin[eInfo.OldIRep];
      ListRepr:=ListListRepr[eInfo.OldIRep];
      PermGRP:=ListPermStab[eInfo.OldIRep];
      phi:=ListPhi[eInfo.OldIRep];
      iRepr:=ListListRepr[eInfo.OldIRep][iAdj];
      eDiffSet:=Difference([1..Length(ListFacets)], [iRepr]);
      O:=Orbits(eInfo.ePermStab, eDiffSet, OnPoints);
      eFacInvVect:=GetSpaceInteriorPoint([ListFacets[iRepr]], ListFacets{eDiffSet}, eInfo.MatrixStab);
      for eO in O
      do
        jRepr:=eO[1];
        test:=TestAdjacency(ListFacets[iRepr],ListFacets[jRepr],ListFacets,[]);
        if test=true then
          TheRelOrigin:=ListOrigin[jRepr];
          jReprCan:=ListRepr[TheRelOrigin];
          ePerm:=RepresentativeAction(PermGRP, jReprCan, jRepr, OnPoints);
          eMatr:=Image(phi, ePerm);
          NSP1:=NullspaceMat(TransposedMat([ListFacets[iRepr], ListFacets[jRepr]]));
          if Position(ListOrbitContaining[eInfo.iOrbitCont].eSet, jRepr)=fail then
            NSP2:=Concatenation(ShallowCopy(NSP1), [eInfo.eInteriorPt]);
            NSP3:=NullspaceMat(TransposedMat(NSP2));
            if Length(NSP3)<>1 then
              Error("We have inconsistency here");
            fi;
            eFacSought:=RemoveFraction(NSP3[1]);
            if eFacSought*eFacInvVect > 0 then
              eFacSought2:=ShallowCopy(eFacSought);
            elif eFacSought*eFacInvVect < 0 then
              eFacSought2:=ShallowCopy(-eFacSought);
            else
              Error("We have inconsistency, please panic");
            fi;
            iRecordSought:=First([1..nbNewOrbit], x->NewListOrbitNames[x].Status="new" and NewListOrbitNames[x].OldIRep=eInfo.OldIRep and NewListOrbitNames[x].iAdj=TheRelOrigin);
            if iRecordSought=fail then
              Error("Debug from here 4");
            fi;
            eNewAdj:=rec(iRecord:=iRecordSought, eEquiv:=eMatr, eFac:=eFacSought2, type:="type 5");
          else
            eFacSought:=ListFacets[jRepr];
            eOldAdj:=OrbitwiseTesselation[eInfo.OldIRep].ListAdj[TheRelOrigin];
            ImgListFacetsJ:=ListListFacets[eOldAdj.iRecord]*CongrMap(eOldAdj.eEquiv*eMatr);
            posI:=Position(ImgListFacetsJ, -eFacSought);
            if posI=fail then
              Error("Deep inconsistency in polyhedral input");
            fi;
            nbFacJ:=Length(ImgListFacetsJ);
            LINC:=[];
            for iFac in [1..nbFacJ]
            do
              if First(NSP1, y->ImgListFacetsJ[iFac]*y<>0)=fail then
                Add(LINC, iFac);
              fi;
            od;
            ListIncident:=Filtered([1..nbFacJ], x->ImgListFacetsJ[x]*eInfo.eInteriorPt<>0 and First(NSP1, y->y*ImgListFacetsJ[x]<>0)=fail);
            if Length(ListIncident)<>1 then
              Error("Polyhedral inconsistency in your input");
            fi;
            jFac:=ListIncident[1];
            TheRelOrigin2:=ListListOrigin[eOldAdj.iRecord][jFac];
            jFacCan:=ListListRepr[eOldAdj.iRecord][TheRelOrigin2];
            PermGRP2:=ListPermStab[eOldAdj.iRecord];
            phi2:=ListPhi[eOldAdj.iRecord];
            ePerm2:=RepresentativeAction(PermGRP2, jFacCan, jFac, OnPoints);
            eMatr2:=Image(phi2, ePerm2);
            eEquivSought:=eMatr2*eOldAdj.eEquiv*eMatr;
            iRecordSought:=First([1..nbNewOrbit], x->NewListOrbitNames[x].Status="new" and NewListOrbitNames[x].OldIRep=eOldAdj.iRecord and NewListOrbitNames[x].iAdj=TheRelOrigin2);
            if iRecordSought=fail then
              Error("Debug from here 5");
            fi;
            eNewAdj:=rec(eEquiv:=eEquivSought, iRecord:=iRecordSought, eFac:=eFacSought, type:="type 6");
          fi;
          Add(NewListAdj, eNewAdj);
        fi;
      od;
    fi;
    TheRecord:=rec(MatrixStab:=eInfo.MatrixStab, ListAdj:=NewListAdj);
    Add(NewOrbitwiseTesselation, TheRecord);
  od;
  return NewOrbitwiseTesselation;
end;


GetTotalInvariantRay:=function(TheTessel, TheOrbIdx)
  local n, ListCongrGens, TheCongrGRP, ListFacets, eAdj, TheOrb, EXT, TheSumRay, eEXT, TheSumCritFacet;
  n:=Length(TheTessel[1].ListAdj[1].eFac);
  ListCongrGens:=List(GeneratorsOfGroup(TheTessel[TheOrbIdx].MatrixStab), CongrMap);
  TheCongrGRP:=Group(ListCongrGens);
  ListFacets:=[];
  TheSumCritFacet:=ListWithIdenticalEntries(n, 0);
  for eAdj in TheTessel[TheOrbIdx].ListAdj
  do
    TheOrb:=Orbit(TheCongrGRP, eAdj.eFac, OnPoints);
    Append(ListFacets, TheOrb);
    if Length(TheOrb)=1 then
      TheSumCritFacet:=TheSumCritFacet + eAdj.eFac;
    fi;
  od;
  EXT:=DualDescription(ListFacets);
  TheSumRay:=ListWithIdenticalEntries(n, 0);
  for eEXT in EXT
  do
    if eEXT*TheSumCritFacet=0 then
      TheSumRay:=TheSumRay + eEXT;
    fi;
  od;
  return TheSumRay;
end;


Face_GetFaceFromIOrbit:=function(TheTessel, iOrbit)
  local n, eStab, ListEqua, ListCongrGens, TheCongrGRP, eAdj, ListFacets, TheOrb, TheInteriorPt;
  n:=Length(TheTessel[1].ListAdj[1].eFac);
  eStab:=TheTessel[iOrbit].MatrixStab;
  ListEqua:=[];
  ListCongrGens:=List(GeneratorsOfGroup(eStab), CongrMap);
  TheCongrGRP:=Group(ListCongrGens);
  ListFacets:=[];
  for eAdj in TheTessel[iOrbit].ListAdj
  do
    TheOrb:=Orbit(TheCongrGRP, eAdj.eFac, OnPoints);
    Append(ListFacets, TheOrb);
  od;
  TheInteriorPt:=GetSpaceInteriorPoint(ListEqua, ListFacets, eStab);
  return rec(ListIOrbit:=[iOrbit], 
             ListSets:=[ [] ],
             ListMats:=[IdentityMat(n)],
             ListStabs:=[eStab],
             ListOrbSizes:=[1],
             TheSpa:=IdentityMat(n),
             TheSpaDual:=[],
             TheStab:=eStab,
             TheStabSpa:=eStab, 
             InteriorPt:=TheInteriorPt);
end;



Face_GetAllTotalInvariantRays:=function(TheTessel, eFace)
  local eRecAll, n, ListEquations, nbOrb, iOrb, iOrbit, eMat, eSet, ListEqua, eEqua, eSol, eGen, DiffMat, NSP, ListInequalities, ListInequalitiesExpand, nbFace, eSetDiff, ListIneq, eIneq, eIneqExpand, SetIneq, EXT, EXTpossible, EXTpossibleMapped, FAC, FACsel, ListRank, rnk, eEXT;
  eRecAll:=GetListListAll(TheTessel);
  n:=eRecAll.n;
  ListEquations:=[];
  nbOrb:=Length(eFace.ListIOrbit);
  for iOrb in [1..nbOrb]
  do
    iOrbit:=eFace.ListIOrbit[iOrb];
    eMat:=eFace.ListMats[iOrb];
    eSet:=eFace.ListSets[iOrb];
    if Length(eSet)>0 then
      ListEqua:=eRecAll.ListListFacets[iOrbit]{eSet}*CongrMap(eMat);
    else
      ListEqua:=[];
    fi;
    if iOrb=1 then
      Append(ListEquations, ListEqua);
    else
      for eEqua in ListEqua
      do
        eSol:=SolutionMat(ListEquations, eEqua);
        if eSol=fail then
          Error("Inconsistency in the input Face, PANIC");
        fi;
      od;
    fi;
  od;
  for eGen in GeneratorsOfGroup(eFace.TheStab)
  do
    DiffMat:=TransposedMat(eGen)-IdentityMat(n);
    Append(ListEquations, DiffMat);
  od;
  NSP:=NullspaceMat(TransposedMat(ListEquations));
  ListInequalities:=[];
  ListInequalitiesExpand:=[];
  for iOrb in [1..nbOrb]
  do
    iOrbit:=eFace.ListIOrbit[iOrb];
    eMat:=eFace.ListMats[iOrb];
    eSet:=eFace.ListSets[iOrb];
    nbFace:=Length(eRecAll.ListListFacets[iOrbit]);
    eSetDiff:=Difference([1..nbFace], eSet);
    ListIneq:=eRecAll.ListListFacets[iOrbit]{eSetDiff}*CongrMap(eMat);
    Append(ListInequalities, ListIneq);
    for eIneq in ListIneq
    do
      eIneqExpand:=List(NSP, x->eIneq*x);
      Add(ListInequalitiesExpand, eIneqExpand);
    od;
  od;
  SetIneq:=Set(ListInequalitiesExpand);
  EXT:=DualDescription(SetIneq);
  EXTpossible:=List(EXT, x->RemoveFraction(x*NSP));
  ListRank:=[];
  iOrb:=1;
  iOrbit:=eFace.ListIOrbit[iOrb];
  eMat:=eFace.ListMats[iOrb];
  FAC:=eRecAll.ListListFacets[iOrbit]*CongrMap(eMat);
  for eEXT in EXTpossible
  do
    FACsel:=Filtered(FAC, x->x*eEXT=0);
    rnk:=RankMat(FACsel);
    Add(ListRank, rnk);
  od;
  EXTpossibleMapped:=EXTpossible*Inverse(eFace.ListMats[1]);
  return rec(EXTpossible:=EXTpossible,
             iOrbit:=eFace.ListIOrbit[1], 
             ListRank:=ListRank, 
             EXTpossibleMapped:=EXTpossibleMapped);
end;






Generic_BoundaryOperatorsFromPolyhedralTesselation:=function(OrbitwiseTesselation, kSought, FuncDoRetraction, FuncCheckCorrectness, eRecIAI, RecOption)
  local ListOrbitByRank, iRank, TheComputedList, FuncInsert, iFace, eFace, NewListOrbit, eOrbit, ListVectsM2, ListOccuringCoefficients, idx, eOrbitSmall, TheBoundary, eElt, iBound, pos, ListSign, TheRetOrbit, ListIFace, ListElt, TheReturnBoundary, iFaceSelect, IdxSel, eMulSign, eAddElt, ListElementM2, nbBound, iOrbitAsk, iFaceM1, eSign, eEltM2, ListOrbVertices, TheRec, eO, O, iOrbit, TheSpann, eSpann, eSet, TheStab, FuncSignatureDet, eVectChar, eCaseSpann, eSetSpann, eMatChosen, iOrbitChosen, SpannFace_FAC, SpannFace_EXT, ListEXT, ListPermGroupsFAC, ListPermGroupsEXT, ListListFacets, ListListOrigins, TheStabChosen, eSetChosen, RepresentativeEquivalenceTesselation_FAC, RepresentativeEquivalenceTesselation_EXT, ListPhiFAC, ListPhiEXT, hMat, ListStabGens, ListPermGensFAC, ListPermGensEXT, PermGRP, phiEXT, phiFAC, eGen, ListFacets, eList, CongrGRP, ListOrigins, iOrbAdj, eAdj, TheOrb, ListStabGensCongr, TheDim, TheInteriorPt, ListInteriorPt, nbFace, GetResolution, iOrbitSmall, ListOriginCells, FuncDeterminant, iOrbitFound, ListUncorrectFaces, TheTest, eRotSubgroup, ListSignGens, GRPsym, eStab, eDet, ListMatrGens, nbOrb, iOrb, HaveEXT, HaveIAI, eInfo, IsOrientable;
  TheDim:=Length(OrbitwiseTesselation[1].ListAdj[1].eFac);
  if IsBound(OrbitwiseTesselation[1].EXT) then
    HaveEXT:=true;
  else
    HaveEXT:=false;
  fi;
  if eRecIAI<>"unset" and HaveEXT=true then
    HaveIAI:=true;
  else
    HaveIAI:=false;
  fi;
#  HaveEXT:=false;
#  HaveIAI:=false;
  Print("HaveEXT=", HaveEXT, "\n");
  Print("HaveIAI=", HaveIAI, "\n");
  Print("DoBound=", RecOption.DoBound, "\n");
  Print("DoSign=", RecOption.DoSign, "\n");
  Print("DoMat=", RecOption.DoMat, "\n");
  Print("DoElt=", RecOption.DoElt, "\n");
  Print("DoRotationSubgroup=", RecOption.DoRotationSubgroup, "\n");
  ListListFacets:=[];
  ListListOrigins:=[];
  ListPermGroupsFAC:=[];
  ListInteriorPt:=[];
  ListPhiFAC:=[];
  if HaveEXT then
    ListPhiEXT:=[];
    ListEXT:=[];
    ListPermGroupsEXT:=[];
  fi;
  for eOrbit in OrbitwiseTesselation
  do
    ListStabGens:=GeneratorsOfGroup(eOrbit.MatrixStab);
    ListStabGensCongr:=List(ListStabGens, CongrMap);
    CongrGRP:=PersoGroupMatrix(ListStabGensCongr, TheDim);
    ListFacets:=[];
    ListOrigins:=[];
    for iOrbAdj in [1..Length(eOrbit.ListAdj)]
    do
      eAdj:=eOrbit.ListAdj[iOrbAdj];
      TheOrb:=Orbit(CongrGRP, eAdj.eFac, OnPoints);
      Append(ListFacets, TheOrb);
      Append(ListOrigins, ListWithIdenticalEntries(Length(TheOrb), iOrbAdj));
    od;
    Add(ListListFacets, ListFacets);
    Add(ListListOrigins, ListOrigins);
    ListPermGensFAC:=[];
    for eGen in GeneratorsOfGroup(CongrGRP)
    do
      eList:=List(ListFacets, x->Position(ListFacets, x*eGen));
      Add(ListPermGensFAC, PermList(eList));
    od;
    PermGRP:=PersoGroupPerm(ListPermGensFAC);
    phiFAC:=GroupHomomorphismByImagesNC(PermGRP, eOrbit.MatrixStab, ListPermGensFAC, ListStabGens);
    Add(ListPermGroupsFAC, PermGRP);
    Add(ListPhiFAC, phiFAC);
    Print("|ListFacets|=", Length(ListFacets), " |PermGRP|=", Order(PermGRP), "\n");
    if HaveEXT then
      Add(ListEXT, eOrbit.EXT);
      ListPermGensEXT:=[];
      for eGen in GeneratorsOfGroup(eOrbit.MatrixStab)
      do
        eList:=List(eOrbit.EXT, x->Position(eOrbit.EXT, x*eGen));
        Add(ListPermGensEXT, PermList(eList));
      od;
      PermGRP:=PersoGroupPerm(ListPermGensEXT);
      phiEXT:=GroupHomomorphismByImagesNC(PermGRP, eOrbit.MatrixStab, ListPermGensEXT, ListStabGens);
      Add(ListPermGroupsEXT, PermGRP);
      Add(ListPhiEXT, phiEXT);
    fi;
    if HaveEXT then
      TheInteriorPt:=Sum(eOrbit.EXT);
    else
      TheInteriorPt:=GetSpaceInteriorPoint([], ListFacets, eOrbit.MatrixStab);
    fi;
    Add(ListInteriorPt, TheInteriorPt);
  od;
  FuncSignatureDet:=function(iRank, iFace, eElt)
    local NewMat, eVect, TheSpa;
    NewMat:=[];
    TheSpa:=ListOrbitByRank[iRank+2][iFace].TheSpa;
    for eVect in TheSpa
    do
      Add(NewMat, SolutionMat(TheSpa, eVect*eElt));
    od;
    return DeterminantMat(NewMat)*DeterminantMat(eElt);
  end;
  FuncDeterminant:=function(eElt)
    return DeterminantMat(eElt);
  end;
  SpannFace_EXT:=function(eInfo, eSetINP)
    local iOrbit, FACsel, EXTsel, TheInteriorPt, TheStab, TheSpa, testRetract, eInfoRet, eInv1, eInv2, eInv, TheLimit;
    iOrbit:=eInfo.iOrbitChosen;
    FACsel:=ListListFacets[iOrbit]{eSetINP};
    EXTsel:=Filtered(ListEXT[iOrbit], x->First(FACsel, y->y*x<>0)=fail);
    TheInteriorPt:=Sum(EXTsel);
    TheSpa:=RowReduction(EXTsel).EXT;
    testRetract:=FuncDoRetraction(eInfo, EXTsel, TheInteriorPt);
    if testRetract=false then
      TheStab:=eRecIAI.FuncAutomorphism(TheInteriorPt);
      eInv1:=eRecIAI.FuncInvariant(TheInteriorPt);
      TheLimit:=500;
      eInv2:=__VectorConfiguration_Invariant(EXTsel, TheLimit);
      eInv:=GetMd5sumObj([eInv1, eInv2]);
    else
      TheStab:="unset, if you want generators, use SpannFace_FAC";
      eInv:="unset";
    fi;
    TheStabChosen:=Stabilizer(ListPermGroupsFAC[iOrbit], eSetINP, OnSets);
    eInfoRet:=rec(iOrbitChosen:=iOrbit, eSetChosen:=eSetINP, TheStabChosen:=TheStabChosen, eMatChosen:=eInfo.eMatChosen);
    return rec(InteriorPt:=TheInteriorPt,
               eInfo:=eInfoRet,
               eInv:=eInv,
               TheSpa:=TheSpa,
               testRetract:=testRetract,
               TheStab:=TheStab);
  end;
  SpannFace_FAC:=function(eInfo, eSetINP)
    local iOrbitINP, eMatINP, ListStatus, ListRecord, TestEquivalenceRecord, FuncInsertConf, TheStab, eRecord, TheSpaRef, TheSpaDualRef, IsOKfacet, IsFinished, nbOrb, iOrbit, eSet, O, eO, iFacet, TheRelOrigin, iRelFacet, eAdj, hPerm, hMatr, gMat, ImgListFacets, eSetFacNew, TheStabNew, TotalStab, ListStabs, ListMats, ListSets, ListIOrbit, ListIneq, EquaStd, TheInteriorPt, iCase, iOrb, ListTotalStabGens, TheDiff, GetRecord, eNewGen, eVect, ListOrbSizes, NewListGens, FuncInsertGenerator, TotalStabSpa, ListMatrGensSpa, eMatrRed, hSetFac, nbFac, ePreRecord, eSetFac, testRetract, eInfoRet;
    iOrbitINP:=eInfo.iOrbitChosen;
    eMatINP:=eInfo.eMatChosen;
    ListStatus:=[];
    ListRecord:=[];
    ListTotalStabGens:=[];
    TestEquivalenceRecord:=function(eRecord1, eRecord2)
      local gMat, eList, ePerm, eTestPerm, RetMat;
      if eRecord1.iOrbit<>eRecord2.iOrbit then
        return false;
      fi;
      eTestPerm:=RepresentativeAction(ListPermGroupsFAC[eRecord1.iOrbit], eRecord1.eSetFac, eRecord2.eSetFac, OnSets);
      if eTestPerm=fail then
        return false;
      else
        hMat:=Image(ListPhiFAC[eRecord1.iOrbit], eTestPerm);
        RetMat:=Inverse(eRecord1.eMat)*hMat*eRecord2.eMat;
        if eRecord1.InteriorPt*RetMat<>eRecord2.InteriorPt then
          Error("We reach inconsistency here, TestEquivalenceRecord");
        fi;
        return RetMat;
      fi;
    end;
    GetRecord:=function(ePreRecord)
      local iOrbit, eSetFac, eMat, TheStab, EquaStdRel, ListFacetsRel, TheStabRel, TheInteriorPt, TheSpa, eSetFacDiff, TheInteriorPt1, TheInteriorPt2, eSetExt;
      iOrbit:=ePreRecord.iOrbit;
      eSetFac:=ePreRecord.eSetFac;
      eMat:=ePreRecord.eMat;
      TheStab:=Stabilizer(ListPermGroupsFAC[iOrbit], eSetFac, OnSets);
      EquaStdRel:=ListListFacets[iOrbit]{eSetFac}*CongrMap(eMat);
      if HaveEXT then
        eSetExt:=Filtered([1..Length(ListEXT[iOrbit])], x->First(ListListFacets[iOrbit]{eSetFac}, y->ListEXT[iOrbit][x]*y<>0)=fail);
      else
        eSetExt:="void";
      fi;
      eSetFacDiff:=Difference([1..Length(ListListFacets[iOrbit])], eSetFac);
      if Length(eSetFacDiff)=0 then
        Error("We think that you may have pushed the program too far");
      fi;
      ListFacetsRel:=ListListFacets[iOrbit]{eSetFacDiff}*CongrMap(eMat);
      TheSpa:=NullspaceMat(TransposedMat(EquaStdRel));
      ListStabGens:=List(GeneratorsOfGroup(Image(ListPhiFAC[iOrbit], TheStab)), x->Inverse(eMat)*x*eMat);
      TheStabRel:=PersoGroupMatrix(ListStabGens, TheDim);
      TheInteriorPt1:=GetSpaceInteriorPoint(EquaStdRel, ListFacetsRel, TheStabRel);
      TheInteriorPt2:=ListInteriorPt[iOrbit]*eMat;
      TheInteriorPt:=TheInteriorPt1+TheInteriorPt2;
      return rec(iOrbit:=iOrbit,
                 eMat:=eMat,
                 TheStab:=TheStab,
                 eSetFac:=eSetFac,
                 eSetExt:=eSetExt,
                 InteriorPt:=TheInteriorPt,
                 TheSpa:=TheSpa,
                 TheSpaDual:=RowReduction(EquaStdRel).EXT);
    end;
    FuncInsertConf:=function(eRecord)
      local nbOrb, iOrb, test, eGen;
      nbOrb:=Length(ListRecord);
      for iOrb in [1..Length(ListRecord)]
      do
        test:=TestEquivalenceRecord(eRecord, ListRecord[iOrb]);
        if test<>false then
          Add(ListTotalStabGens, test);
          return;
        fi;
      od;
      for eGen in GeneratorsOfGroup(eRecord.TheStab)
      do
        Add(ListTotalStabGens, Inverse(eRecord.eMat)*Image(ListPhiFAC[eRecord.iOrbit], eGen)*eRecord.eMat);
      od;
      if IsBound(TheSpaRef)=false then
        TheSpaRef:=eRecord.TheSpa;
        TheSpaDualRef:=eRecord.TheSpaDual;
      else
        if IsEqualVectorSpace(rec(n:=TheDim, ListVect:=TheSpaRef), rec(n:=TheDim, ListVect:=eRecord.TheSpa))=false then
          Error("Subspace, not equal, debug from here 1");
        fi;
        if IsEqualVectorSpace(rec(n:=TheDim, ListVect:=TheSpaDualRef), rec(n:=TheDim, ListVect:=eRecord.TheSpaDual))=false then
          Error("Subspace, not equal, debug from here 2");
        fi;
      fi;
      Add(ListRecord, eRecord);
      Add(ListStatus, "NO");
    end;
    ePreRecord:=rec(iOrbit:=iOrbitINP, eSetFac:=eSetINP, eMat:=eMatINP);
    eRecord:=GetRecord(ePreRecord);
    FuncInsertConf(eRecord);
    IsOKfacet:=function(eFac)
      local eVect;
      for eVect in TheSpaRef
      do
        if eVect*eFac<>0 then
          return false;
        fi;
      od;
      return true;
    end;
    while(true)
    do
      IsFinished:=true;
      nbOrb:=Length(ListStatus);
      for iOrb in [1..nbOrb]
      do 
        if ListStatus[iOrb]="NO" then
          ListStatus[iOrb]:="YES";
          iOrbit:=ListRecord[iOrb].iOrbit;
          eSetFac:=ListRecord[iOrb].eSetFac;
          IsFinished:=false;
          O:=Orbits(ListRecord[iOrb].TheStab, eSetFac, OnPoints);
          for eO in O
          do
            iFacet:=eO[1];
            TheRelOrigin:=ListListOrigins[iOrbit][iFacet];
            eAdj:=OrbitwiseTesselation[iOrbit].ListAdj[TheRelOrigin];
            iRelFacet:=Position(ListListFacets[iOrbit], eAdj.eFac);
            hPerm:=RepresentativeAction(ListPermGroupsFAC[iOrbit], iRelFacet, iFacet, OnPoints);
            hMatr:=Image(ListPhiFAC[iOrbit], hPerm);
            gMat:=eAdj.eEquiv*hMatr*ListRecord[iOrb].eMat;
            ImgListFacets:=ListListFacets[eAdj.iRecord]*CongrMap(gMat);
            eSetFacNew:=Filtered([1..Length(ImgListFacets)], x->IsOKfacet(ImgListFacets[x])=true);
            if Length(eSetFacNew)=0 then
              Error("Please debug from here");
            fi;
            ePreRecord:=rec(iOrbit:=eAdj.iRecord, eSetFac:=eSetFacNew, eMat:=gMat);
            eRecord:=GetRecord(ePreRecord);
            FuncInsertConf(eRecord);
          od;
        fi;
      od;
      if IsFinished=true then
        break;
      fi;
    od;
    TotalStab:=PersoGroupMatrix(ListTotalStabGens, TheDim);
    ListIOrbit:=List(ListRecord, x->x.iOrbit);
    ListSets:=List(ListRecord, x->x.eSetFac);
    ListStabs:=List(ListRecord, x->x.TheStab);
    ListMats:=List(ListRecord, x->x.eMat);
    eInfoRet:=rec(iOrbitChosen:=ListIOrbit[1], eSetChosen:=ListSets[1], TheStabChosen:=ListStabs[1], eMatChosen:=ListMats[1]);
    if HaveEXT then
      TheInteriorPt:=(Sum(ListEXT[ListIOrbit[1]]{ListRecord[1].eSetExt}))*ListMats[1];
    else
      EquaStd:=List(ListListFacets[ListIOrbit[1]]{ListSets[1]}, x->x*CongrMap(ListMats[1]));
      ListIneq:=[];
      for iCase in [1..Length(ListIOrbit)]
      do
        iOrbit:=ListIOrbit[iCase];
        eSetFac:=ListSets[iCase];
        nbFac:=Length(ListListFacets[iOrbit]);
        hSetFac:=Difference([1..nbFac], eSetFac);
        TheDiff:=ListListFacets[iOrbit]{hSetFac};
        Append(ListIneq, List(TheDiff, x->x*CongrMap(ListMats[iCase])));
      od;
      TheInteriorPt:=GetSpaceInteriorPoint(EquaStd, ListIneq, TotalStab);
    fi;
    testRetract:=FuncDoRetraction(TheInteriorPt);
    if testRetract=false then
      ListOrbSizes:=[];
      for eRecord in ListRecord
      do
        Add(ListOrbSizes, Length(Orbit(TotalStab, eRecord.InteriorPt, OnPoints)));
      od;
      NewListGens:=[];
      TotalStab:=PersoGroupMatrix(NewListGens, TheDim);
      FuncInsertGenerator:=function(eGen)
        if eGen in TotalStab then
          return;
        fi;
        Add(NewListGens, eGen);
        TotalStab:=PersoGroupMatrix(NewListGens, TheDim);
      end;
      for eGen in ListTotalStabGens
      do
        FuncInsertGenerator(eGen);
      od;
      ListMatrGensSpa:=[];
      for eGen in GeneratorsOfGroup(TotalStab)
      do
        eMatrRed:=List(TheSpaRef, x->SolutionMat(TheSpaRef, x*eGen));
        Add(ListMatrGensSpa, eMatrRed);
      od;
      TotalStabSpa:=Group(ListMatrGensSpa);
      SetSize(TotalStabSpa, Order(TotalStabSpa));
    else
      ListOrbSizes:="irrelevant";
      TotalStabSpa:="irrelevant";
    fi;
    return rec(ListIOrbit:=ListIOrbit,
               ListSets:=ListSets,
               ListMats:=ListMats,
               ListStabs:=ListStabs,
               ListOrbSizes:=ListOrbSizes,
               eInfo:=eInfoRet,
               eInv:="unset",
               testRetract:=testRetract, 
               TheSpa:=TheSpaRef,
               TheSpaDual:=TheSpaDualRef,
               TheStab:=TotalStab,
               TheStabSpa:=TotalStabSpa,
               InteriorPt:=TheInteriorPt);
  end;
  RepresentativeEquivalenceTesselation_FAC:=function(TheFace1, TheFace2)
    local iOrbit1, eMat1, eSetFac1, len2, iCase, gMat, eList, ePerm, eTestPerm, RetMat, eDiscInfo;
    eDiscInfo:=TheFace2.eDiscInfo;
    iOrbit1:=TheFace1.ListIOrbit[1];
    eMat1:=TheFace1.ListMats[1];
    eSetFac1:=TheFace1.ListSets[1];
    len2:=Length(eDiscInfo.ListIOrbit);
    for iCase in [1..len2]
    do
      if eDiscInfo.ListIOrbit[iCase]=iOrbit1 then
        eTestPerm:=RepresentativeAction(ListPermGroupsFAC[iOrbit1], eSetFac1, eDiscInfo.ListSets[iCase], OnSets);
        if eTestPerm<>fail then
          hMat:=Image(ListPhiFAC[iOrbit1], eTestPerm);
          RetMat:=Inverse(eMat1)*hMat*eDiscInfo.ListMats[iCase];
          if TheFace1.InteriorPt*RetMat<>TheFace2.InteriorPt then
            Error("We have inconsistency in RepresentativeEquivalence");
          fi;
          return RetMat;
        fi;
      fi;
    od;
    return fail;
  end;
  RepresentativeEquivalenceTesselation_EXT:=function(eFace1, eFace2)
    if eFace1.eInv<>eFace2.eInv then
      return fail;
    fi;
    return eRecIAI.FuncIsomorphism(eFace1.InteriorPt, eFace2.InteriorPt);
  end;
  ListOrbitByRank:=[];
  ListOrbitByRank[1]:=[rec(eFace:=[], BoundaryImage:="irrelevant")];
  ListOrbVertices:=[];
  for iOrbit in [1..Length(OrbitwiseTesselation)]
  do
    eOrbit:=OrbitwiseTesselation[iOrbit];
    TheInteriorPt:=GetSpaceInteriorPoint([], ListListFacets[iOrbit], eOrbit.MatrixStab);
    eInfo:=rec(iOrbitChosen:=iOrbit, eSetChosen:=[], TheStabChosen:=ListPermGroupsFAC[iOrbit], eMatChosen:=IdentityMat(TheDim));
    if RecOption.DoBound then
      TheReturnBoundary:=rec(ListIFace:=[1], ListSign:=[1], ListElt:=[IdentityMat(TheDim)]);
    else
      TheReturnBoundary:="irrelevant";
    fi;
    TheRec:=rec(eInfo:=eInfo, InteriorPt:=TheInteriorPt, TheSpa:=IdentityMat(TheDim), TheStab:=eOrbit.MatrixStab, BoundaryImage:=TheReturnBoundary);
    Add(ListOrbVertices, TheRec);
  od;
  Add(ListOrbitByRank, ListOrbVertices);
  for iRank in [1..kSought+1]
  do
    Print("iRank=", iRank, "/", kSought, "\n");
    TheComputedList:=[];
    ListUncorrectFaces:=[];
    FuncInsert:=function(eInteriorPtSmall, iFace, eFaceSpanned, eSetChosenB, eSetSpann)
      local iOrbit2, eEquiv, TheOrbSmall, NewListElement, eOrbit1, eInteriorSmallImg, SetInterior, eCase, eInfo, iOrbitChosen, eSetChosen, TheStabChosen, eMatChosen, eDiscInfo;
      for iOrbit2 in [1..Length(TheComputedList)]
      do
        if HaveIAI=false then
          eEquiv:=RepresentativeEquivalenceTesselation_FAC(eFaceSpanned, TheComputedList[iOrbit2]);
        else
          eEquiv:=RepresentativeEquivalenceTesselation_EXT(eFaceSpanned, TheComputedList[iOrbit2]);
        fi;
        if eEquiv<>fail then
          eInteriorSmallImg:=eInteriorPtSmall*eEquiv;
          TheOrbSmall:=OrbitWithAction(TheComputedList[iOrbit2].TheStab, eInteriorSmallImg, OnPoints);
          SetInterior:=Set(TheOrbSmall.ListCoset);
          for eCase in TheComputedList[iOrbit2].ListOrbitSmall
          do
            if eCase.SetInterior=SetInterior then
              return iOrbit2;
            fi;
          od;
          NewListElement:=List(TheOrbSmall.ListElement, x->eEquiv*x);
          Add(TheComputedList[iOrbit2].ListOrbitSmall, rec(iFace:=iFace, SetInterior:=SetInterior, eSetChosen:=eSetChosenB, eSetSpann:=eSetSpann, ListElement:=NewListElement));
          return iOrbit2;
        fi;
      od;
      TheOrbSmall:=OrbitWithAction(eFaceSpanned.TheStab, eInteriorPtSmall, OnPoints);
      SetInterior:=Set(TheOrbSmall.ListCoset);
      if HaveIAI then
        eDiscInfo:="unset";
      else
        eDiscInfo:=rec(ListIOrbit:=eFaceSpanned.ListIOrbit, ListSets:=eFaceSpanned.ListSets, ListMats:=eFaceSpanned.ListMats);
      fi;
      eOrbit1:=rec(TheSpa:=eFaceSpanned.TheSpa,
        InteriorPt:=eFaceSpanned.InteriorPt, TheStab:=eFaceSpanned.TheStab,
        eInfo:=eFaceSpanned.eInfo, eInv:=eFaceSpanned.eInv,
        eDiscInfo:=eDiscInfo,
        ListOrbitSmall:=[rec(iFace:=iFace, SetInterior:=SetInterior, eSetSpann:=eSetSpann, ListElement:=TheOrbSmall.ListElement)]);
      Add(TheComputedList, eOrbit1);
      return Length(TheComputedList);
    end;
    Print("Computing faces of dimension ", iRank, "\n");
    nbFace:=Length(ListOrbitByRank[iRank+1]);
    for iFace in [1..nbFace]
    do
      eInfo:=ListOrbitByRank[iRank+1][iFace].eInfo;
      TheInteriorPt:=ListOrbitByRank[iRank+1][iFace].InteriorPt;
      if HaveEXT then
        TheSpann:=SPAN_face_ExtremeRay(eInfo.eSetChosen, eInfo.TheStabChosen, ListListFacets[eInfo.iOrbitChosen], ListEXT[eInfo.iOrbitChosen]);
      else
        TheSpann:=SPAN_face_LinearProgramming(eInfo.eSetChosen, eInfo.TheStabChosen, ListListFacets[eInfo.iOrbitChosen], ListPermGroupsFAC[eInfo.iOrbitChosen], []);
      fi;
      Print("iFace=", iFace, "/", nbFace, " |Stab|=", Order(ListOrbitByRank[iRank+1][iFace].TheStab),  " eSet=", eInfo.eSetChosen, " |TheSpann|=", Length(TheSpann), "\n");
      for eSetSpann in TheSpann
      do
        if HaveEXT then
          eCaseSpann:=SpannFace_EXT(eInfo, eSetSpann);
        else
          eCaseSpann:=SpannFace_FAC(eInfo, eSetSpann);
        fi;
        if eCaseSpann.testRetract=false then
          iOrbitFound:=FuncInsert(TheInteriorPt, iFace, eCaseSpann, eInfo.eSetChosen, eSetSpann);
          TheTest:=FuncCheckCorrectness(eCaseSpann);
          if TheTest.TheReply=false then
            Add(ListUncorrectFaces, rec(iOrbit:=iOrbitFound, ActionRefinement:=TheTest.ActionRefinement, eFace:=eCaseSpann));
          fi;
        fi;
      od;
    od;
    if Length(ListUncorrectFaces)>0 then
      Print("We found some incorrect faces and leave it\n");
      Print("to you to correct the problem\n");
      return rec(IsCorrect:=false, ListUncorrectFaces:=ListUncorrectFaces);
    fi;
    Print("Now computing boundary operators\n");
    Print("number of orbits=", Length(TheComputedList), "\n");
    NewListOrbit:=[];
    for eOrbit in TheComputedList
    do
      if RecOption.DoBound then
        ListVectsM2:=[];
        ListElementM2:=[];
        ListIFace:=[];
        if RecOption.DoElt then
          ListElt:=[];
        fi;
        ListOriginCells:=[];
        ListOccuringCoefficients:=[];
        idx:=0;
        for iOrbitSmall in [1..Length(eOrbit.ListOrbitSmall)]
        do
          eOrbitSmall:=eOrbit.ListOrbitSmall[iOrbitSmall];
          iFaceM1:=eOrbitSmall.iFace;
          TheBoundary:=ListOrbitByRank[iRank+1][iFaceM1].BoundaryImage;
          for eElt in eOrbitSmall.ListElement
          do
            idx:=idx+1;
            Add(ListIFace, iFaceM1);
            Add(ListOriginCells, iOrbitSmall);
            if RecOption.DoElt then
              Add(ListElt, eElt);
            fi;
            if RecOption.DoSign then
              nbBound:=Length(TheBoundary.ListIFace);
              for iBound in [1..nbBound]
              do
                eSign:=TheBoundary.ListSign[iBound];
                eEltM2:=TheBoundary.ListElt[iBound];
                eAddElt:=eEltM2*eElt;
                if iRank=1 then
                  eVectChar:="bckl";
                else
                  eVectChar:=ListOrbitByRank[iRank][TheBoundary.ListIFace[iBound]].InteriorPt*eAddElt;
                fi;
                pos:=Position(ListVectsM2, eVectChar);
                if pos=fail then
                  Add(ListVectsM2, eVectChar);
                  Add(ListElementM2, eAddElt);
                  Add(ListOccuringCoefficients, [rec(Sign:=eSign, idx:=idx)]);
                else
                  if iRank<=2 then
                    eMulSign:=1;
                  else
                    iOrbitAsk:=TheBoundary.ListIFace[iBound];
                    eMulSign:=FuncSignatureDet(iRank-2, iOrbitAsk, ListElementM2[pos]*eAddElt^(-1));
                  fi;
                  Add(ListOccuringCoefficients[pos], rec(Sign:=eMulSign*eSign, idx:=idx));
                fi;
              od;
            fi;
          od;
        od;
        TheReturnBoundary:=rec(ListIFace:=ListIFace, ListOriginCells:=ListOriginCells);
        if RecOption.DoSign then
          ListSign:=UntangleAllSigns(ListOccuringCoefficients, idx);
          TheReturnBoundary.ListSign:=ListSign;
        fi;
        if RecOption.DoElt then
          TheReturnBoundary.ListElt:=ListElt;
        fi;
      else
        TheReturnBoundary:="irrelevant";
      fi;
      TheRetOrbit:=rec(eInfo:=eOrbit.eInfo, TheSpa:=eOrbit.TheSpa, InteriorPt:=eOrbit.InteriorPt, TheStab:=eOrbit.TheStab, BoundaryImage:=TheReturnBoundary);
      Add(NewListOrbit, TheRetOrbit);
    od;
    #
    Add(ListOrbitByRank, NewListOrbit);
  od;
  if RecOption.DoRotationSubgroup then
    Print("Now computing the rotation subgroups\n");
    for iRank in [0..kSought+1]
    do
      nbOrb:=Length(ListOrbitByRank[iRank+2]);
      for iOrb in [1..nbOrb]
      do
        eStab:=ListOrbitByRank[iRank+2][iOrb].TheStab;
        ListMatrGens:=GeneratorsOfGroup(eStab);
        ListSignGens:=[];
        IsOrientable:=true;
        for eGen in ListMatrGens
        do
          eDet:=FuncSignatureDet(iRank, iOrb, eGen);
          if eDet=-1 then
            Add(ListSignGens, (1,2));
            IsOrientable:=false;
          else
            Add(ListSignGens, ());
          fi;
        od;
        GRPsym:=Group([(1,2)]);
        eRotSubgroup:=GetKernelOfMapping(eStab, GRPsym, ListMatrGens, ListSignGens);
        ListOrbitByRank[iRank+2][iOrb].RotationSubgroup:=eRotSubgroup;
        ListOrbitByRank[iRank+2][iOrb].IsOrientable:=IsOrientable;
      od;
    od;
  fi;
  GetResolution:=function(GRP, kLevel)
    return ResolutionComingFromHAP(GRP, kLevel);
  end;
  return rec(IsCorrect:=true, 
             ListOrbitByRank:=ListOrbitByRank,
             FuncSignatureDet:=FuncSignatureDet,
             FuncDeterminant:=FuncDeterminant, 
             IdentityElt:=IdentityMat(TheDim), 
             GetResolution:=GetResolution);
end;



SignFunction:=function(eVal)
  if eVal=0 then
    return 0;
  fi;
  if eVal > 0 then
    return 1;
  fi;
  return -1;
end;


#
# Here we use a determination method for the signs 
# It is explained in Elbaz-Vincent et al paper Perfect forms
# and the cohomology of the modular group.
GetBoundaryDual_CohomologySequenceStyle:=function(OrbitwiseTesselation, FuncDoRetraction, eRecIAI, RecOptionDual)
  local TheDim, eOrbit, ListStabGens, ListPermGensEXT, eGen, eList, PermGRP, phiEXT, FuncSignatureDet, nbOrbit, TheBound, pos, GetResolution, ListPhiEXT, ListEXT, ListOrbitByRank, iOrbitMain, ListOrbDomains, ListPermGroupsEXT, FuncDeterminant, RepresentativeEquivalenceTesselation_EXT, iOrbit, TheSpa, iRank, TheBoundary, i2, len2, ListOccuringCoefficients, eMulSign, ListSign, iOrb, nbOrb, TheRec, TheInteriorPt, FuncInsert, eInteriorPt, NewListOrbit, EXT, ListPermGens, eMatrGen, eIns, IsOrientable, eRotSubgroup, GRPsym, ListSignGens, len, eStab, eDet, ListMatrGens, eAddElt, eSign2, ListElementM2, eVect2img, ListVectsM2, eElt, eElt2, ListOrb, eSetMain1, TheOrbSmall, eOrb, eSetMain, i, iFace, iFace2, eVect2, testRetract, TheSpaF, TheSpaImg, TheTot, eMatRed, eSign, eVect, TheStab;
  TheDim:=Length(OrbitwiseTesselation[1].ListAdj[1].eFac);
  ListEXT:=[];
  ListPermGroupsEXT:=[];
  ListPhiEXT:=[];
  Print("DoRetracted=", RecOptionDual.DoRetracted, "\n");
  for eOrbit in OrbitwiseTesselation
  do
    ListStabGens:=GeneratorsOfGroup(eOrbit.MatrixStab);
    Add(ListEXT, eOrbit.EXT);
    ListPermGensEXT:=[];
    for eGen in GeneratorsOfGroup(eOrbit.MatrixStab)
    do
      eList:=List(eOrbit.EXT, x->Position(eOrbit.EXT, x*eGen));
      Add(ListPermGensEXT, PermList(eList));
    od;
    PermGRP:=PersoGroupPerm(ListPermGensEXT);
    phiEXT:=GroupHomomorphismByImagesNC(PermGRP, eOrbit.MatrixStab, ListPermGensEXT, ListStabGens);
    Add(ListPermGroupsEXT, PermGRP);
    Add(ListPhiEXT, phiEXT);
  od;
  FuncSignatureDet:=function(iRank, iFace, eElt)
    local NewMat, TheSpa;
    TheSpa:=ListOrbitByRank[iRank][iFace].TheSpa;
    NewMat:=List(TheSpa, x->SolutionMat(TheSpa, x*eElt));
    return DeterminantMat(NewMat);
  end;
  FuncDeterminant:=function(eElt)
    return DeterminantMat(eElt);
  end;
  RepresentativeEquivalenceTesselation_EXT:=function(eFace1, eFace2)
    local eSet1, eSet2, test, iOrbitMain, GRPperm, eMatr;
    if eFace1.eInv<>eFace2.eInv then
      return fail;
    fi;
    if eFace1.testRetract<>eFace2.testRetract then
      return fail;
    fi;
    if eFace1.testRetract then
      if eFace1.iOrbitMain<>eFace2.iOrbitMain then
        return fail;
      fi;
      iOrbitMain:=eFace1.iOrbitMain;
      GRPperm:=ListPermGroupsEXT[iOrbitMain];
      eSet1:=eFace1.eSetMain;
      eSet2:=eFace2.eSetMain;
      test:=RepresentativeAction(GRPperm, eSet1, eSet2, OnSets);
      if test=fail then
        return fail;
      fi;
      eMatr:=Image(ListPhiEXT[iOrbitMain], test);
      return eMatr;
    fi;
    eMatr:=eRecIAI.FuncIsomorphism(eFace1.InteriorPt, eFace2.InteriorPt);
    if eMatr=fail then
      return fail;
    fi;
    if First(eFace1.EXT, x->Position(eFace2.EXT, x*eMatr)=fail)<>fail then
      Error("Some bug here");
    fi;
    return eMatr;
  end;
  ListOrbitByRank:=[];
  ListOrbDomains:=[];
  for iOrbit in [1..Length(OrbitwiseTesselation)]
  do
    eOrbit:=OrbitwiseTesselation[iOrbit];
    TheInteriorPt:=Sum(eOrbit.EXT);
    TheSpa:=RowReduction(eOrbit.EXT).EXT;
    TheRec:=rec(iOrbitMain:=iOrbit, eSetMain:=[1..Length(eOrbit.EXT)], TheStab:=eOrbit.MatrixStab, InteriorPt:=TheInteriorPt, EXT:=eOrbit.EXT, TheSpa:=TheSpa, TheStab:=eOrbit.MatrixStab);
    Add(ListOrbDomains, TheRec);
  od;
  Add(ListOrbitByRank, ListOrbDomains);
  for iRank in [2..TheDim]
  do
    Print("iRank=", iRank, "/", TheDim, "\n");
    NewListOrbit:=[];
    FuncInsert:=function(iOrbitMain, eSetMain)
      local EXT, eInteriorPt, eFace1, iOrbit, eEquiv, TheSpa, eInv;
      EXT:=ListEXT[iOrbitMain]{eSetMain};
      eInteriorPt:=Sum(EXT);
      TheSpa:=RowReduction(EXT).EXT;
      testRetract:=FuncDoRetraction(eInteriorPt);
      eInv:=rec(eInvShort:=LinPolytope_Invariant(EXT), 
                eInvIAI:=eRecIAI.FuncInvariant(eInteriorPt));
      eFace1:=rec(iOrbitMain:=iOrbitMain, eSetMain:=eSetMain, EXT:=EXT, InteriorPt:=eInteriorPt, TheSpa:=TheSpa, eInv:=eInv, testRetract:=testRetract);
      for iOrbit in [1..Length(NewListOrbit)]
      do
        eEquiv:=RepresentativeEquivalenceTesselation_EXT(NewListOrbit[iOrbit], eFace1);
        if eEquiv<>fail then
          return rec(iOrbit:=iOrbit, eEquiv:=eEquiv);
        fi;
      od;
      eFace1.TheStab:=eRecIAI.FuncAutomorphism(eInteriorPt);
      Add(NewListOrbit, eFace1);
      return rec(iOrbit:=Length(NewListOrbit), eEquiv:=IdentityMat(TheDim));
    end;
    nbOrbit:=Length(ListOrbitByRank[iRank-1]);
    for iOrbit in [1..nbOrbit]
    do
      EXT:=ListOrbitByRank[iRank-1][iOrbit].EXT;
      TheSpa:=ListOrbitByRank[iRank-1][iOrbit].TheSpa;
      iOrbitMain:=ListOrbitByRank[iRank-1][iOrbit].iOrbitMain;
      eSetMain1:=ListOrbitByRank[iRank-1][iOrbit].eSetMain;
      TheStab:=ListOrbitByRank[iRank-1][iOrbit].TheStab;
      ListMatrGens:=GeneratorsOfGroup(TheStab);
      ListPermGens:=[];
      for eMatrGen in ListMatrGens
      do
        eList:=List(EXT, x->Position(EXT, x*eMatrGen));
        Add(ListPermGens, PermList(eList));
      od;
      PermGRP:=Group(ListPermGens);
      ListOrb:=DualDescriptionStandard(EXT, PermGRP);
      #
      TheBound:=rec(ListIFace:=[], ListElt:=[], ListSign:=[]);
      eVect:=Sum(EXT);
      for eOrb in ListOrb
      do
        eSetMain:=eSetMain1{eOrb};
        eInteriorPt:=Sum(EXT{eOrb});
        testRetract:=FuncDoRetraction(eInteriorPt);
        if RecOptionDual.DoRetracted=true or testRetract=false then
          eIns:=FuncInsert(iOrbitMain, eSetMain);
          TheOrbSmall:=OrbitWithAction(TheStab, eInteriorPt, OnPoints);
          Append(TheBound.ListIFace, ListWithIdenticalEntries(Length(TheOrbSmall.ListElement), eIns.iOrbit));
          TheSpaF:=NewListOrbit[eIns.iOrbit].TheSpa;
          for eElt in TheOrbSmall.ListElement
          do
            eAddElt:=eIns.eEquiv*eElt;
            Add(TheBound.ListElt, eAddElt);
            TheSpaImg:=TheSpaF*eAddElt;
#            eVect:=First(TheSpa, x->SolutionMat(TheSpaImg, x)=fail);
            TheTot:=Concatenation(TheSpaImg, [eVect]);
            eMatRed:=List(TheTot, x->SolutionMat(TheSpa, x));
            eSign:=SignFunction(DeterminantMat(eMatRed));
            Add(TheBound.ListSign, eSign);
          od;
        fi;
      od;
      ListOrbitByRank[iRank-1][iOrbit].BoundaryImage:=TheBound;
    od;
    Add(ListOrbitByRank, NewListOrbit);
    Print("    |NewListOrbit|=", Length(NewListOrbit), "\n");
  od;
  nbOrbit:=Length(ListOrbitByRank[TheDim]);
  TheBound:=rec(ListIFace:=[1], ListElt:=[IdentityMat(TheDim)]);
  for iOrbit in [1..nbOrbit]
  do
    ListOrbitByRank[TheDim][iOrbit].BoundaryImage:=TheBound;
  od;
  Print("Now computing the rotation subgroups\n");
  for iRank in [1..TheDim]
  do
    nbOrb:=Length(ListOrbitByRank[iRank]);
    for iOrb in [1..nbOrb]
    do
      eStab:=ListOrbitByRank[iRank][iOrb].TheStab;
      ListMatrGens:=GeneratorsOfGroup(eStab);
      ListSignGens:=[];
      IsOrientable:=true;
      for eGen in ListMatrGens
      do
        eDet:=FuncSignatureDet(iRank, iOrb, eGen);
        if eDet=-1 then
          Add(ListSignGens, (1,2));
          IsOrientable:=false;
        else
          Add(ListSignGens, ());
        fi;
      od;
      GRPsym:=Group([(1,2)]);
      eRotSubgroup:=GetKernelOfMapping(eStab, GRPsym, ListMatrGens, ListSignGens);
      ListOrbitByRank[iRank][iOrb].RotationSubgroup:=eRotSubgroup;
      ListOrbitByRank[iRank][iOrb].IsOrientable:=IsOrientable;
    od;
  od;
  GetResolution:=function(GRP, kLevel)
    return ResolutionComingFromHAP(GRP, kLevel);
  end;
  return rec(IsCorrect:=true, 
             ListOrbitByRank:=ListOrbitByRank,
             FuncSignatureDet:=FuncSignatureDet,
             FuncDeterminant:=FuncDeterminant, 
             IdentityElt:=IdentityMat(TheDim), 
             GetResolution:=GetResolution);
end;





BoundaryOperatorsFromPolyhedralTesselation:=function(OrbitwiseTesselation, kSought, FuncDoRetraction, eRecIAI, RecOption)
  local FuncCheckCorrectness;
  FuncCheckCorrectness:=function(eFace)
    return rec(TheReply:=true, ActionRefinement:="irrelevant");
  end;
  return Generic_BoundaryOperatorsFromPolyhedralTesselation(OrbitwiseTesselation, kSought, FuncDoRetraction, FuncCheckCorrectness, eRecIAI, RecOption);
end;




Bredon_BoundaryOperatorsFromPolyhedralTesselation:=function(OrbitwiseTesselation, kSought, FuncDoRetraction, eRecIAI)
  local FuncCheckCorrectness;
  FuncCheckCorrectness:=function(eFace)
    local eGen, eVect, eInteriorPt;
    for eGen in GeneratorsOfGroup(eFace.TheStab)
    do
      for eVect in eFace.TheSpa
      do
        if eVect<>eVect*eGen then
          eInteriorPt:=eFace.InteriorPt*Inverse(eFace.ListMats[1]);
          return rec(TheReply:=false, ActionRefinement:=rec(iOrbit:=eFace.ListIOrbit[1], eRay:=eInteriorPt));
        fi;
      od;
    od;
    return rec(TheReply:=true, ActionRefinement:="irrelevant");
  end;
  return Generic_BoundaryOperatorsFromPolyhedralTesselation(OrbitwiseTesselation, kSought, FuncDoRetraction, FuncCheckCorrectness, eRecIAI);
end;

ContractingHomotopyPolyhedralTesselation:=function(OrbitwiseTesselation, TheBoundary, TheCycle, iDimension)
  local GetContainingTopDimensional, n, AllInfo, ListFullDimCells, FuncInsertCell, nbOrbitMax, SpannListFaces, ListReprFacesSource, ListReprFacesTarget, ListFacesSource, ListFacesSourceInteriorPt, ListFacesTarget, ListFacesTargetInteriorPt, iOrbit, eElt, TheRec, GetOrbitsCells, DoInflationSpecific, DoInflation, eVectSource, TheLine, ListEqua, eVectTarget, eRec, eSol, nbFaceTarget, nbFaceSource, iFaceSource, nbOrbitSource, eVal, eEltFace, iOrbitFace, GetPositioning, eValFace, LenBound, iBound, TheLen, i;
  nbOrbitMax:=Length(OrbitwiseTesselation);
  GetContainingTopDimensional:=function(iComp, eElt)
    local iRank, ReturnElt, iCompSearch, i, IsFound, nbOrbit, iOrbit, pos, fElt;
    iRank:=iDimension;
    ReturnElt:=eElt;
    iCompSearch:=iComp;
    for i in [1..iDimension]
    do
      IsFound:=false;
      nbOrbit:=Length(TheBoundary.ListOrbitByRank[iRank]);
      for iOrbit in [1..nbOrbit]
      do
        if IsFound=false then
          pos:=Position(TheBoundary.ListOrbitByRank[iRank][iOrbit].ListIFace, iCompSearch);
          if pos<>fail then
            IsFound:=true;
            fElt:=TheBoundary.ListOrbitByRank[iRank][iOrbit].ListElt[pos];
            ReturnElt:=Inverse(fElt)*ReturnElt;
            iCompSearch:=iComp;
          fi;          
        fi;
      od;
      if IsFound=false then
        Error("Not found, please panic very loudly");
      fi;
      iRank:=iRank-1;
    od;
    return rec(iComp:=iCompSearch, eElt:=ReturnElt);
  end;
  AllInfo:=GetListListAll(OrbitwiseTesselation);
  n:=AllInfo.n;
  ListFullDimCells:=[];
  FuncInsertCell:=function(iComp, eElt)
    local eRec, jComp, fElt, eQuot;
    for eRec in ListFullDimCells
    do
      jComp:=eRec.iComp;
      fElt:=eRec.eElt;
      if iComp=jComp then
        eQuot:=eElt*Inverse(fElt);
        if eQuot in OrbitwiseTesselation[iComp].MatrixStab then
          return;
        fi;
      fi;
    od;
    Add(ListFullDimCells, rec(iComp:=iComp, eElt:=eElt, Status:=1));
  end;
  for iOrbit in [1..Length(TheCycle)]
  do
    for eElt in TheCycle[iOrbit].ListElt
    do
      TheRec:=GetContainingTopDimensional(iOrbit, eElt);
      FuncInsertCell(TheRec);
    od;
  od;
  GetOrbitsCells:=function(iOrbit, iRank)
    local ListOrbit, NewListOrbit, TheMatrixStab, jRank, FuncInsert, eOrbit, i, len, ListReturn, TheRec, TheNewRec;
    TheMatrixStab:=OrbitwiseTesselation[iRank+2][iOrbit].TheMatrixStab;
    ListOrbit:=[rec(iOrbit:=iOrbit, iRank:=0, eElt:=IdentityMat(n))];
    for jRank in [0..iRank]
    do
      NewListOrbit:=[];
      FuncInsert:=function(iOrbitNew, eEltNew)
        local eInteriorPt, eNewOrbit, OinteriorPt, eRec;
        eInteriorPt:=TheBoundary[iRank+2][iOrbit].InteriorPt;
        for eNewOrbit in NewListOrbit.O
        do
          if Position(eNewOrbit.ListInteriorPt, eInteriorPt)<>fail then
            return;
          fi;
        od;
        OinteriorPt:=Orbit(TheMatrixStab, eInteriorPt, OnPoints);
        eRec:=rec(OinteriorPt:=OinteriorPt, iOrbit:=iOrbitNew, eElt:=eEltNew);
        Add(NewListOrbit, eRec);
      end;
      for eOrbit in ListOrbit
      do
        len:=Length(TheBoundary[jRank+2][eOrbit.iOrbit].BoundaryImage.ListIFace);
        for i in [1..len]
        do
          FuncInsert(TheBoundary[jRank+2][eOrbit.iOrbit].BoundaryImage.ListIFace[i], TheBoundary[jRank+2][eOrbit.iOrbit].BoundaryImage.ListElt[i]*eOrbit.eElt);
        od;
      od;
      ListOrbit:=ShallowCopy(NewListOrbit);
    od;
    ListReturn:=[];
    for eOrbit in ListOrbit
    do
      TheRec:=OrbitWithAction(TheMatrixStab, eOrbit.OinteriorPt[1], OnPoints);
      len:=Length(TheRec.ListElement);
      for i in [1..len]
      do
        TheNewRec:=rec(iOrbit:=eOrbit.iOrbit, eInteriorPt:=eOrbit.OinteriorPt[1]*TheRec.ListElement[i], eElt:=eOrbit.eElt*TheRec.ListElement[i]);
        Add(ListReturn, TheNewRec);
      od;
    od;
    return ListReturn;
  end;
  ListReprFacesSource:=List([1..nbOrbitMax], x->GetOrbitsCells(x, iDimension+1));
  ListReprFacesTarget:=List([1..nbOrbitMax], x->GetOrbitsCells(x, iDimension));
  SpannListFaces:=function()
    local eFullDimFace, iComp, eElt, eRec, eNewElt, eInteriorPt, pos;
    ListFacesSource:=[];
    ListFacesSourceInteriorPt:=[];
    ListFacesTarget:=[];
    ListFacesTargetInteriorPt:=[];
    for eFullDimFace in ListFullDimCells
    do
      iComp:=eFullDimFace.iComp;
      eElt:=eFullDimFace.eElt;
      for eRec in ListReprFacesSource[iComp]
      do
        eNewElt:=eRec.eElt*eElt;
        eInteriorPt:=eRec.eInteriorPt*eElt;
        pos:=Position(ListFacesSourceInteriorPt, eInteriorPt);
        if pos=fail then
          Add(ListFacesSourceInteriorPt, eInteriorPt);
          Add(ListFacesSource, rec(iOrbit:=iComp, eElt:=eNewElt));
        fi;
      od;
      for eRec in ListReprFacesTarget[iComp]
      do
        eNewElt:=eRec.eElt*eElt;
        eInteriorPt:=eRec.eInteriorPt*eElt;
        pos:=Position(ListFacesTargetInteriorPt, eInteriorPt);
        if pos=fail then
          Add(ListFacesTargetInteriorPt, eInteriorPt);
          Add(ListFacesTarget, rec(iOrbit:=iComp, eElt:=eNewElt));
        fi;
      od;
    od;
  end;
  DoInflationSpecific:=function(TheCall)
    local iComp, eElt, nbFac, iFac, iOrigin, iRepr, eRepr, eMat, eNewElt, iCompNew;
    iComp:=ListFullDimCells[TheCall].iComp;
    eElt:=ListFullDimCells[TheCall].eElt;
    nbFac:=Length(AllInfo.ListListFacets[iComp]);
    for iFac in [1..nbFac]
    do
      iOrigin:=AllInfo.ListListOrigin[iFac];
      iRepr:=AllInfo.ListListRepr[iOrigin];
      eRepr:=RepresentativeAction(AllInfo.ListPermStab[iOrigin], iRepr, iFac, OnPoints);
      eMat:=Image(AllInfo.ListPhiFAC[iComp], eRepr);
      eNewElt:=OrbitwiseTesselation[iComp].ListAdj[iOrigin].eEquiv*eMat*eElt;
      iCompNew:=OrbitwiseTesselation[iComp].ListAdj[iOrigin].iRecord;
      FuncInsertCell(iCompNew, eNewElt);
    od;
  end;
  DoInflation:=function()
    local TheNb, iNb;
    TheNb:=Length(ListFullDimCells);
    for iNb in [1..TheNb]
    do
      if ListFullDimCells[iNb].Status=1 then
        ListFullDimCells[iNb].Status:=0;
        DoInflationSpecific(iNb);
      fi;
    od;
  end;
  GetPositioning:=function(iRank, iOrbit, eElt)
    local iFaceTarget, eEltTarget, eQuot, eSign;
    for iFaceTarget in [1..nbFaceTarget]
    do
      if ListFacesTarget[iFaceTarget].iOrbit=iOrbit then
        eEltTarget:=ListFacesTarget[iFaceTarget].eElt;
        eQuot:=eEltTarget*Inverse(eElt);
        if eQuot in TheBoundary[iRank+2][iOrbit].MatrixStab then
          eSign:=TheBoundary.FuncSignatureDet(iRank, iOrbit, eQuot);
          return rec(eSign:=eSign, iFaceTarget:=iFaceTarget);
        fi;
      fi;
    od;
    Error("That is utterly unlogical");
  end;
  while(true)
  do
    nbFaceTarget:=Length(ListFacesTarget);
    eVectTarget:=ListWithIdenticalEntries(nbFaceTarget, 0);
    for iOrbit in [1..Length(TheCycle)]
    do
      TheLen:=Length(TheCycle[iOrbit].ListVal);
      for i in [1..TheLen]
      do
        eVal:=TheCycle[iOrbit].ListVal[i];
        eElt:=TheCycle[iOrbit].ListElt[i];
        eRec:=GetPositioning(iDimension, iOrbit, eElt);
        eVectTarget[eRec.iFaceTarget]:=eVal*eRec.eSign;
      od;
    od;
    ListEqua:=[];
    nbFaceSource:=Length(ListFacesSource);
    for iFaceSource in [1..nbFaceSource]
    do
      TheLine:=ListWithIdenticalEntries(nbFaceTarget, 0);
      eRec:=ListFacesSource[iFaceSource];
      LenBound:=Length(TheBoundary[iDimension+3][eRec.iOrbit].ListIFace);
      for iBound in [1..LenBound]
      do
        iOrbitFace:=TheBoundary[iDimension+3][eRec.iOrbit].ListIFace[iBound];
        eValFace:=TheBoundary[iDimension+3][eRec.iOrbit].ListVal[iBound];
        eEltFace:=TheBoundary[iDimension+3][eRec.iOrbit].ListElt[iBound];
        eRec:=GetPositioning(iDimension, iOrbitFace, eEltFace*eRec.eElt);
        eVectTarget[eRec.iFaceTarget]:=eVal*eRec.eSign;
      od;
      Add(ListEqua, TheLine);
    od;
    eSol:=SolutionIntMat(ListEqua, eVectTarget);
    if eSol<>fail then
      nbOrbitSource:=Length(TheBoundary.ListOrbitByRank[iDimension+3]);
      eVectSource:=GMOD_GetZeroVector(nbOrbitSource);
      for iFaceSource in [1..nbFaceSource]
      do
        if eSol[iFaceSource]<>0 then
          eRec:=ListFacesSource[iFaceSource];
          Add(eVectSource[eRec.iOrbit].ListVal, eSol[iFaceSource]);
          Add(eVectSource[eRec.iOrbit].ListElt, eRec.eElt);
        fi;
      od;
      return eVectSource;
    fi;
    DoInflation();
  od;
end;


ComputeMossStyleDeformation:=function(PolyComplex, pInteger)
  local ListMatricesOrbitSplitting, TheDim, iRank, nbOrbit, iOrbit, eOrbit, SetMatricesOrbitSplitting, ListLattice, i, n, eMat;
  ListMatricesOrbitSplitting:=[];
  TheDim:=Length(PolyComplex.ListOrbitByRank);
  for iRank in [2..TheDim]
  do
    nbOrbit:=Length(PolyComplex.ListOrbitByRank[iRank]);
    for iOrbit in [1..nbOrbit]
    do
      eOrbit:=PolyComplex.ListOrbitByRank[iRank][iOrbit];
      Append(ListMatricesOrbitSplitting, GeneratorsOfGroup(eOrbit.TheStab));
      Append(ListMatricesOrbitSplitting, eOrbit.BoundaryImage.ListElt);
    od;
  od;
  SetMatricesOrbitSplitting:=Set(ListMatricesOrbitSplitting);
  n:=Length(SetMatricesOrbitSplitting[1]);
  ListLattice:=[];
  for i in [1..n]
  do
    eMat:=IdentityMat(n);
    Add(ListLattice, ShallowCopy(eMat));
    eMat[i][i]:=1/pInteger;
  od;
  #
end;



DetermineInformationForOrderComplex:=function(OrbitwiseTesselation)
  local n, ListListFacets, ListCongrGRP, ListPermGRP, nbOrbitCell, iOrbit, eOrbit, ListStabGens, ListStabGensCongr, CongrGRP, ListFacets, ListOrigins, iOrbAdj, eAdj, TheOrb, ePerm1, ePerm2, ListPermGens, eGen, ePermGen, eMat, GRPpermFAC, EXT, LorbFlag;
  n:=Length(OrbitwiseTesselation[1].ListAdj[1].eFac);
  ListListFacets:=[];
  ListCongrGRP:=[];
  ListPermGRP:=[];
  nbOrbitCell:=Length(OrbitwiseTesselation);
  for iOrbit in [1..nbOrbitCell]
  do
    eOrbit:=OrbitwiseTesselation[iOrbit];
    ListStabGens:=GeneratorsOfGroup(eOrbit.MatrixStab);
    ListStabGensCongr:=List(ListStabGens, CongrMap);
    CongrGRP:=PersoGroupMatrix(ListStabGensCongr, n);
    ListFacets:=[];
    for iOrbAdj in [1..Length(eOrbit.ListAdj)]
    do
      eAdj:=eOrbit.ListAdj[iOrbAdj];
      TheOrb:=Orbit(CongrGRP, eAdj.eFac, OnPoints);
      if Length(Intersection(Set(ListFacets), Set(TheOrb))) > 0 then
        Error("That is not correct");
      fi;
      Append(ListFacets, TheOrb);
    od;
    ePerm1:=SortingPerm(ListFacets);
    ListPermGens:=[];
    for eGen in GeneratorsOfGroup(CongrGRP)
    do
      ePerm2:=SortingPerm(ListFacets*eGen);
      ePermGen:=ePerm2*Inverse(ePerm1);
      eMat:=FindTransformation(ListFacets, ListFacets, ePermGen);
      if eMat<>eGen then
        Error("We have an apparent inconsistency");
      fi;
      Add(ListPermGens, ePermGen);
    od;
    GRPpermFAC:=PersoGroupPerm(ListPermGens);
    EXT:=DualDescription(ListFacets);
    Print("iOrbit=", iOrbit, " |stab|=", Order(GRPpermFAC), " |EXT|=", Length(EXT), " |FAC|=", Length(ListFacets), "\n");
    LorbFlag:=ListFlagOrbit(GRPpermFAC, ListFacets, EXT);
    Print("|LorbFlag|=", Length(LorbFlag), "\n");
  od;
end;






PrintOrbitwiseTesselationInformation:=function(OrbitwiseTesselation)
  local n, ListListFacets, ListListOrigins, eOrbit, ListStabGens, ListStabGensCongr, CongrGRP, ListFacets, ListOrigins, iOrbAdj, eAdj, TheOrb, iOrbit, nbOrbFac, ImgListFacets, pos, TheOrigin, iAdj, StabSiz, ListCongrGRP, iPair, jPair, kPair, ListPairAdjacency, ListPairCorresp;
  n:=Length(OrbitwiseTesselation[1].ListAdj[1].eFac);
  ListListFacets:=[];
  ListListOrigins:=[];
  ListCongrGRP:=[];
  ListPairAdjacency:=[];
  for iOrbit in [1..Length(OrbitwiseTesselation)]
  do
    eOrbit:=OrbitwiseTesselation[iOrbit];
    ListStabGens:=GeneratorsOfGroup(eOrbit.MatrixStab);
    ListStabGensCongr:=List(ListStabGens, CongrMap);
    CongrGRP:=PersoGroupMatrix(ListStabGensCongr, n);
    Add(ListCongrGRP, CongrGRP);
    ListFacets:=[];
    ListOrigins:=[];
    for iOrbAdj in [1..Length(eOrbit.ListAdj)]
    do
      eAdj:=eOrbit.ListAdj[iOrbAdj];
      TheOrb:=Orbit(CongrGRP, eAdj.eFac, OnPoints);
      if Length(Intersection(Set(ListFacets), Set(TheOrb))) > 0 then
        Error("That is not correct");
      fi;
      Append(ListFacets, TheOrb);
      Append(ListOrigins, ListWithIdenticalEntries(Length(TheOrb), iOrbAdj));
      Add(ListPairAdjacency, [iOrbit, iOrbAdj]);
    od;
    Add(ListListFacets, ListFacets);
    Add(ListListOrigins, ListOrigins);
  od;
  ListPairCorresp:=[];
  for iOrbit in [1..Length(OrbitwiseTesselation)]
  do
    eOrbit:=OrbitwiseTesselation[iOrbit];
    nbOrbFac:=Length(eOrbit.ListAdj);
    Print("O", iOrbit, " |Stab|=", Order(eOrbit.MatrixStab), " nbOrbFac=", nbOrbFac, " |FAC|=", Length(ListListFacets[iOrbit]), "\n");
    CongrGRP:=ListCongrGRP[iOrbit];
    for iAdj in [1..nbOrbFac]
    do
      eAdj:=eOrbit.ListAdj[iAdj];
      TheOrb:=Orbit(CongrGRP, eAdj.eFac, OnPoints);
      StabSiz:=Order(CongrGRP)/Length(TheOrb);
      ImgListFacets:=ListListFacets[eAdj.iRecord]*CongrMap(eAdj.eEquiv);
      pos:=Position(ImgListFacets, -eAdj.eFac);
      TheOrigin:=ListListOrigins[eAdj.iRecord][pos];
      Print("  Adj", iAdj, " size=", Length(TheOrb), " |Stab|=", StabSiz, " matching : (", eAdj.iRecord, ",", TheOrigin, ")\n");
      Add(ListPairCorresp, Position(ListPairAdjacency, [eAdj.iRecord, TheOrigin]));
    od;
  od;
  for iPair in [1..Length(ListPairCorresp)]
  do
    if ListPairCorresp[iPair]=iPair then
      for jPair in [1..Length(ListPairCorresp)]
      do
        if iPair<>jPair and ListPairCorresp[jPair]=iPair then
          Error("Adjacency inconsistency 1");
        fi;
      od;
    else
      kPair:=ListPairCorresp[iPair];
      if ListPairCorresp[kPair]<>iPair then
        Error("Adjacency inconsistency 2");
      fi;
      for jPair in [1..Length(ListPairCorresp)]
      do
        if jPair<>iPair and jPair<>kPair then
          if ListPairCorresp[jPair]=iPair then
            Error("Adjacency inconsistency 3");
          fi;
          if ListPairCorresp[jPair]=kPair then
            Error("Adjacency inconsistency 4");
          fi;
        fi;
      od;
    fi;
  od;
end;




MergeFacetsOrbitwiseTesselation:=function(OrbitwiseTesselation, ListFusion)
  local TheDim, eOrbit, ListStabGens, ListStabGensCongr, ListFacets, ListOrigins, iOrbAdj, TheOrb, nbOrbOld, GRA, iOrbit, eFus1, eFus2, NewTesselation, eRecord, ListAdj, eInfo, eNewAdj, eEquiv, eMat, eAdj, eRecSought, iBlockOrbitAdj, iOrbitAdj, ListInformations, VectConnected, eRep, TheKeyInfo, MatrixStab, ListAdjacencyInfo, ListRecord, eConnRep, ListRepNewFacets, GRArep, ListConnRep, TheCall, TotalListRep, TotalListFacets, TheConstraint, ListInputVect, test, ListPos, ListStrictPos, ImgListFacets, eO, SetListFacets, SetPermGRPfacet, O, ListPermGens, eList, eNewGen, eGen, ListFAC, FuncInsert, ListListFacets, iRep1, iRep2, SetPermGRP, eListRep, i, eSetRep, MatrixStabCongr, eImgFac, iRep, eFac, nbRep, eFus, iAdj, IsFinished, iOrb, nbOrb, eConn, ListConn, iConn, TheOrigin, pos, ListListOrigins, CongrGRP, nbOrbFac, FuncInsertGenerator;
  # building standard data
  TheDim:=Length(OrbitwiseTesselation[1].ListAdj[1].eFac);
  ListListFacets:=[];
  ListListOrigins:=[];
  for eOrbit in OrbitwiseTesselation
  do
    ListStabGens:=GeneratorsOfGroup(eOrbit.MatrixStab);
    ListStabGensCongr:=List(ListStabGens, CongrMap);
    CongrGRP:=PersoGroupMatrix(ListStabGensCongr, TheDim);
    ListFacets:=[];
    ListOrigins:=[];
    for iOrbAdj in [1..Length(eOrbit.ListAdj)]
    do
      eAdj:=eOrbit.ListAdj[iOrbAdj];
      TheOrb:=Orbit(CongrGRP, eAdj.eFac, OnPoints);
      Append(ListFacets, TheOrb);
      Append(ListOrigins, ListWithIdenticalEntries(Length(TheOrb), iOrbAdj));
    od;
    Add(ListListFacets, ListFacets);
    Add(ListListOrigins, ListOrigins);
  od;
  # checking coherency of input Fusion
  nbOrbOld:=Length(OrbitwiseTesselation);
  GRA:=NullGraph(Group(()), nbOrbOld);
  for iOrbit in [1..nbOrbOld]
  do
    eOrbit:=OrbitwiseTesselation[iOrbit];
    nbOrbFac:=Length(eOrbit.ListAdj);
#    Print("O", iOrbit, " |Stab|=", Order(eOrbit.MatrixStab), " nbOrbFac=", nbOrbFac, "\n");
    ListStabGensCongr:=List(GeneratorsOfGroup(eOrbit.MatrixStab), CongrMap);
    CongrGRP:=PersoGroupMatrix(ListStabGensCongr, TheDim);
    for iAdj in [1..nbOrbFac]
    do
      eFus1:=[iOrbit, iAdj];
      eAdj:=eOrbit.ListAdj[iAdj];
      TheOrb:=Orbit(CongrGRP, eAdj.eFac, OnPoints);
      ImgListFacets:=List(ListListFacets[eAdj.iRecord], x->x*CongrMap(eAdj.eEquiv));
      pos:=Position(ImgListFacets, -eAdj.eFac);
      TheOrigin:=ListListOrigins[eAdj.iRecord][pos];
      eFus2:=[eAdj.iRecord, TheOrigin];
      if Position(ListFusion, eFus1)<>fail then
        if Position(ListFusion, eFus2)=fail then
          Print("Incoherence in Fusion data\n");
          Print("We have eFus1=", eFus1, "\n");
          Print("  but eFus2=", eFus2, " is missing\n");
          Error("Please correct");
        fi;
      fi;
      if Position(ListFusion, eFus1)<>fail then
        if eFus1[1]<>eFus2[1] then
          AddEdgeOrbit(GRA, [eFus1[1], eFus2[1]]);
          AddEdgeOrbit(GRA, [eFus2[1], eFus1[1]]);
        fi;
      fi;
    od;
  od;
  ListConn:=ConnectedComponents(GRA);
  VectConnected:=ListWithIdenticalEntries(nbOrbOld, 0);
  # TheMerging of domains is to be done
  ListInformations:=[];
  for iConn in [1..Length(ListConn)]
  do
    eConn:=ListConn[iConn];
    VectConnected{eConn}:=ListWithIdenticalEntries(Length(eConn), iConn);
    ListStabGens:=[];
    MatrixStab:=PersoGroupMatrix(ListStabGens, TheDim);
    FuncInsertGenerator:=function(eGen)
      if eGen in MatrixStab then
        return;
      fi;
      Add(ListStabGens, eGen);
      MatrixStab:=PersoGroupMatrix(ListStabGens, TheDim);
    end;
    ListRepNewFacets:=[];
    ListRecord:=[];
    FuncInsert:=function(iOrbitOld, eMat)
      local eRecord;
      for eRecord in ListRecord
      do
        if eRecord.iOrbit=iOrbitOld then
          eNewGen:=Inverse(eRecord.eMat)*eMat;
          FuncInsertGenerator(eNewGen);
          return;
        fi;
      od;
      for eGen in GeneratorsOfGroup(OrbitwiseTesselation[iOrbitOld].MatrixStab)
      do
        eNewGen:=Inverse(eMat)*eGen*eMat;
        FuncInsertGenerator(eNewGen);
      od;
      eRecord:=rec(iOrbit:=iOrbitOld, eMat:=eMat, Status:="NO");
      Add(ListRecord, eRecord);
    end;
    FuncInsert(eConn[1], IdentityMat(TheDim));
    while(true)
    do
      nbOrb:=Length(ListRecord);
      IsFinished:=true;
      for iOrb in [1..nbOrb]
      do
        if ListRecord[iOrb].Status="NO" then
          ListRecord[iOrb].Status:="YES";
          IsFinished:=false;
          iOrbit:=ListRecord[iOrb].iOrbit;
          eMat:=ListRecord[iOrb].eMat;
          ListAdj:=OrbitwiseTesselation[iOrbit].ListAdj;
          for iAdj in [1..Length(ListAdj)]
          do
            eAdj:=ListAdj[iAdj];
            eFus:=[iOrbit, iAdj];
            if Position(ListFusion, eFus)<>fail then
              FuncInsert(eAdj.iRecord, eAdj.eEquiv*eMat);
            else
              Add(ListRepNewFacets, rec(iOrb:=iOrb, eAdj:=eAdj));
            fi;
          od;
        fi;
      od;
      if IsFinished=true then
        break;
      fi;
    od;
    ListStabGensCongr:=List(ListStabGens, CongrMap);
    MatrixStabCongr:=PersoGroupMatrix(ListStabGensCongr, TheDim);
    TotalListFacets:=[];
    TotalListRep:=[];
    nbRep:=Length(ListRepNewFacets);
    GRArep:=NullGraph(Group(()), nbRep);
    for iRep in [1..nbRep]
    do
      eRep:=ListRepNewFacets[iRep];
      eFac:=eRep.eAdj.eFac;
      eImgFac:=eFac*CongrMap(ListRecord[eRep.iOrb].eMat);
      TheOrb:=Orbit(MatrixStabCongr, eImgFac, OnPoints);
#      Print("iRep=", iRep, " |TheOrb|=", Length(TheOrb), "\n");
      Append(TotalListFacets, TheOrb);
      Append(TotalListRep, ListWithIdenticalEntries(Length(TheOrb), iRep));
    od;
    TheCall:=SetSelect(TotalListFacets);
    SetListFacets:=TheCall.TheSet;
    ListPermGens:=[];
    for eGen in ListStabGensCongr
    do
      eList:=List(SetListFacets, x->Position(SetListFacets, x*eGen));
      Add(ListPermGens, PermList(eList));
    od;
    SetPermGRP:=PersoGroupPerm(ListPermGens);
    O:=Orbits(SetPermGRP, [1..Length(SetListFacets)], OnPoints);
    for eO in O
    do
      eSetRep:=TheCall.TheListSets[eO[1]];
      eListRep:=TotalListRep{eSetRep};
      iRep1:=eListRep[1];
      for i in [2..Length(eListRep)]
      do
        iRep2:=eListRep[i];
        if iRep1<>iRep2 then
          AddEdgeOrbit(GRArep, [iRep1, iRep2]);
          AddEdgeOrbit(GRArep, [iRep2, iRep1]);
        fi;
      od;
    od;
    # now checking whther all facets are really facets
    ListFAC:=DetermineFacetsAmongList(SetListFacets, SetPermGRP);
    if Length(ListFAC)<>Length(SetListFacets) then
      Print("We re sorry, but the union of the domains is not a convex\n");
      Print("domain, henceforth, we cannot guarantee that it is homotopic\n");
      Print("to a sphere.\n");
      Error("Please correct");
    fi;
    for iOrb in [1..Length(ListRecord)]
    do
      iOrbit:=ListRecord[iOrb].iOrbit;
      eMat:=ListRecord[iOrb].eMat;
      ImgListFacets:=List(ListListFacets[iOrbit], x->x*CongrMap(eMat));
      ListPermGens:=[];
      for eGen in GeneratorsOfGroup(OrbitwiseTesselation[iOrbit].MatrixStab)
      do
        eNewGen:=Inverse(eMat)*eGen*eMat;
        eList:=List(SetListFacets, x->Position(SetListFacets, x*CongrMap(eNewGen)));
        Add(ListPermGens, PermList(eList));
      od;
      SetPermGRPfacet:=PersoGroupPerm(ListPermGens);
      O:=Orbits(SetPermGRPfacet, [1..Length(SetListFacets)], OnPoints);
      for eO in O
      do
        ListInputVect:=Concatenation(ImgListFacets, [-SetListFacets[eO[1]]]);
        ListPos:=[1..Length(ImgListFacets)];
        ListStrictPos:=[1+Length(ImgListFacets)];
        TheConstraint:=rec(ListStrictlyPositive:=ListStrictPos, ListPositive:=ListPos, ListSetStrictPositive:=[]);
        test:=SearchPositiveRelation(ListInputVect, TheConstraint);
        if test=false then
          Print("We are sorry, but adding the new inequality, means\n");
          Print("that we are not fusionning domains, but shrinking them\n");
          Error("Please correct");
        fi;
      od;
    od;
    ListAdjacencyInfo:=[];
    ListConnRep:=ConnectedComponents(GRArep);
    for eConnRep in ListConnRep
    do
      Add(ListAdjacencyInfo, ListRepNewFacets[eConnRep[1]]);
    od;
    TheKeyInfo:=rec(ListRecord:=ListRecord, ListAdjacencyInfo:=ListAdjacencyInfo, MatrixStab:=MatrixStab);
    Add(ListInformations, TheKeyInfo);
  od;
  NewTesselation:=[];
  for eInfo in ListInformations
  do
    ListAdj:=[];
    for eRep in eInfo.ListAdjacencyInfo
    do
      iOrb:=eRep.iOrb;
      eAdj:=eRep.eAdj;
      iOrbit:=eInfo.ListRecord[iOrb].iOrbit;
      eMat:=eInfo.ListRecord[iOrb].eMat;
      iOrbitAdj:=eAdj.iRecord;
      iBlockOrbitAdj:=VectConnected[iOrbitAdj];
      eRecSought:=First(ListInformations[iBlockOrbitAdj].ListRecord, x->x.iOrbit=iOrbitAdj);
      eEquiv:=Inverse(eRecSought.eMat)*eAdj.eEquiv*eMat;
      eNewAdj:=rec(iRecord:=iBlockOrbitAdj, eFac:=eAdj.eFac*CongrMap(eMat), eEquiv:=eEquiv);
      Add(ListAdj, eNewAdj);
    od;
    eRecord:=rec(MatrixStab:=eInfo.MatrixStab, ListAdj:=ListAdj);
    Add(NewTesselation, eRecord);
  od;
  return NewTesselation;
end;




#
#
# 
MappingToSubgroupPolyhedralTesselation:=function(OrbitwiseTesselation, SplittingInfo)
  local n, ListInvariantVect, eOrbit, ListRepFacets, eInvVect, eIdent, GetSubgroup, nbOrbitOld, NewListOrbit, IsEquivalent, ListReducedStab, ListSymbol, iOrbit, TheStab, TheStabRed, ListDBL, nbSymbol, FuncFindSymbol, NewOrbitwiseTesselation, eSymbol, iSymbol, eCos, eCosInv, NewListGens, NewListAdj, eNewFac, eEquiv, eInfo, TheMatrixStab, eNewRec, eAdj, eNewAdj, FindTheDoubleCosets, eDCS, eMatr, TheMatrixStabSma, phi, ThePermStabBig, ThePermStabSma, TheStabFac, pos, NewListPermGensSma, NewListPermGensBig, ListFacets, TheMatrixStabBig, NewListMatrGensBig, NewListMatrGensSma, AllInfo;
  AllInfo:=GetListListAll(OrbitwiseTesselation);
  Print("We have AllInfo\n");
  n:=AllInfo.n;
  eIdent:=IdentityMat(n);
  GetSubgroup:=function(TheGRP)
    local NewListGens, TheGroup, eElt, FuncInsert;
    NewListGens:=[];
    TheGroup:=Group([eIdent]);
    FuncInsert:=function(eElt)
      if eElt in TheGroup then
        return;
      fi;
      Add(NewListGens, eElt);
      TheGroup:=Group(NewListGens);
    end;
    for eElt in TheGRP
    do
      if SplittingInfo.IsInSmallGroup(eElt)=true then
        FuncInsert(eElt);
      fi;
    od;
    return TheGroup;
  end;
  # find an element h in the SmallGroup, an element s in the
  # stabilizer so that    s g1 = g2 h if it exists.
  # That is G g1 = G g2 h
  IsEquivalent:=function(TheBigStab, eElt1, eElt2)
    local eEltInv2, eElt, eProd;
    eEltInv2:=eElt2^(-1);
    for eElt in TheBigStab
    do
      eProd:=eEltInv2*eElt*eElt1;
      if SplittingInfo.IsInSmallGroup(eProd)=true then
        return rec(eElt:=eElt, hElt:=eProd);
      fi;
    od;
    return false;
  end;
  FindTheDoubleCosets:=function(TheBigStab)
    local ListDoubleCosets, ListStatus, FuncInsert, IsFinished, nbOrb, iOrb, eGen;
    ListDoubleCosets:=[];
    ListStatus:=[];
    FuncInsert:=function(eNewElt)
      local iCos, eCos;
      for iCos in [1..Length(ListDoubleCosets)]
      do
        eCos:=ListDoubleCosets[iCos];
        if IsEquivalent(TheBigStab, eCos, eNewElt)<>false then
          return;
        fi;
      od;
      Add(ListDoubleCosets, eNewElt);
      Add(ListStatus, "NO");
    end;
    FuncInsert(eIdent);
    while(true)
    do
      IsFinished:=true;
      nbOrb:=Length(ListStatus);
      for iOrb in [1..nbOrb]
      do
        if ListStatus[iOrb]="NO" then
          ListStatus[iOrb]:="YES";
          IsFinished:=false;
          for eGen in GeneratorsOfGroup(SplittingInfo.TheBigGroup)
          do
            FuncInsert(ListDoubleCosets[iOrb]*eGen);
          od;
        fi;
      od;
      if IsFinished=true then
        break;
      fi;
    od;
    return ListDoubleCosets;
  end;
  nbOrbitOld:=Length(OrbitwiseTesselation);
  ListReducedStab:=[];
  ListSymbol:=[];
  for iOrbit in [1..nbOrbitOld]
  do
    TheStab:=OrbitwiseTesselation[iOrbit].MatrixStab;
    TheStabRed:=GetSubgroup(TheStab);
    Add(ListReducedStab, TheStabRed);
    ListDBL:=FindTheDoubleCosets(TheStab);
    for eCos in ListDBL
    do
      Add(ListSymbol, rec(iOrbit:=iOrbit, eCos:=eCos));
    od;
  od;
  nbSymbol:=Length(ListSymbol);
#  Print("nbSymbol=", nbSymbol, "\n");
  FuncFindSymbol:=function(iOrbit, eMat)
    local iSymbol, eInfo;
    for iSymbol in [1..nbSymbol]
    do
      if ListSymbol[iSymbol].iOrbit=iOrbit then
        eInfo:=IsEquivalent(OrbitwiseTesselation[iOrbit].MatrixStab, eMat, ListSymbol[iSymbol].eCos);
        if eInfo<>false then
          return rec(iSymbol:=iSymbol, hElt:=eInfo.hElt);
        fi;
      fi;
    od;
  end;
  NewOrbitwiseTesselation:=[];
  for iSymbol in [1..nbSymbol]
  do
    eSymbol:=ListSymbol[iSymbol];
    iOrbit:=eSymbol.iOrbit;
    eCos:=eSymbol.eCos;
    eCosInv:=eCos^(-1);
    NewListMatrGensSma:=List(GeneratorsOfGroup(ListReducedStab[iOrbit]), x->eCos^(-1)*x*eCos);
    TheMatrixStabSma:=PersoGroupMatrix(NewListMatrGensSma, n);
    NewListMatrGensBig:=List(GeneratorsOfGroup(OrbitwiseTesselation[iOrbit].MatrixStab), x->eCos^(-1)*x*eCos);
    TheMatrixStabBig:=PersoGroupMatrix(NewListMatrGensBig, n);
    ListFacets:=AllInfo.ListListFacets[iOrbit]*CongrMap(eCos);
    NewListPermGensSma:=List(NewListMatrGensSma, x->PermList(List(ListFacets, y->Position(ListFacets, y*CongrMap(x)))));
    NewListPermGensBig:=List(NewListMatrGensBig, x->PermList(List(ListFacets, y->Position(ListFacets, y*CongrMap(x)))));
    ThePermStabSma:=Group(NewListPermGensSma);
    ThePermStabBig:=Group(NewListPermGensBig);
    phi:=GroupHomomorphismByImagesNC(ThePermStabBig, TheMatrixStabBig, NewListPermGensBig, NewListMatrGensBig);
    NewListAdj:=[];
    for eAdj in OrbitwiseTesselation[iOrbit].ListAdj
    do
      eNewFac:=eAdj.eFac*CongrMap(eCos);
      pos:=Position(ListFacets, eNewFac);
      TheStabFac:=Stabilizer(ThePermStabBig, pos, OnPoints);
      Print("|ThePermStabBig|=", Order(ThePermStabBig), " |ThePermStabSma|=", Order(ThePermStabSma), "\n");
      for eDCS in DoubleCosets(ThePermStabBig, TheStabFac, ThePermStabSma)
      do
        eMatr:=Image(phi, Representative(eDCS));
        eEquiv:=eAdj.eEquiv*eCos*eMatr;
        eInfo:=FuncFindSymbol(eAdj.iRecord, eEquiv);
        eNewAdj:=rec(iRecord:=eInfo.iSymbol, eFac:=eNewFac*CongrMap(eMatr), eEquiv:=eInfo.hElt);
        Add(NewListAdj, eNewAdj);
      od;
    od;
    eNewRec:=rec(MatrixStab:=TheMatrixStabSma, ListAdj:=NewListAdj);
    Add(NewOrbitwiseTesselation, eNewRec);
  od;
  return NewOrbitwiseTesselation;
end;


MapPolyhedralTesselationByMapping:=function(eRecordTessel, TheFCT)
  local len, NewListOrbitByRank, nbOrbit, NewList, iOrbit, eRec, fRec, i, EXT, EXTimage, jOrbit, eBound, eElt, lenBound, iBound, iP, MapGroup, MapBoundary;
  len:=Length(eRecordTessel.ListOrbitByRank);
  NewListOrbitByRank:=[eRecordTessel.ListOrbitByRank[1]];
  nbOrbit:=Length(eRecordTessel.ListOrbitByRank[2]);
  NewList:=[];
  MapGroup:=function(TheGRP)
    local ListGens, NewListGens;
    ListGens:=GeneratorsOfGroup(TheGRP);
    NewListGens:=List(ListGens, TheFCT);
    return Group(NewListGens);
  end;
  MapBoundary:=function(eBound)
    if IsBound(eBound.ListSign) then
      return rec(ListIFace:=eBound.ListIFace, 
                 ListSign:=eBound.ListSign, 
                 ListElt:=List(eBound.ListElt, TheFCT));
    else
      return rec(ListIFace:=eBound.ListIFace, 
                 ListElt:=List(eBound.ListElt, TheFCT));
    fi;
  end;
  for iOrbit in [1..nbOrbit]
  do
    eRec:=eRecordTessel.ListOrbitByRank[2][iOrbit];
    fRec:=rec(TheStab:=MapGroup(eRec.TheStab), 
              BoundaryImage:=MapBoundary(eRec.BoundaryImage));
    if IsBound(eRec.RotationSubgroup) then
      fRec.RotationSubgroup:=MapGroup(eRec.RotationSubgroup);
    fi;
    Add(NewList, fRec);
  od;
  Add(NewListOrbitByRank, NewList);
  for iP in [3..len]
  do
    nbOrbit:=Length(eRecordTessel.ListOrbitByRank[iP]);
    NewList:=[];
    for iOrbit in [1..nbOrbit]
    do
      eRec:=eRecordTessel.ListOrbitByRank[iP][iOrbit];
      fRec:=rec(TheStab:=MapGroup(eRec.TheStab), 
                BoundaryImage:=MapBoundary(eRec.BoundaryImage));
      if IsBound(eRec.RotationSubgroup) then
        fRec.RotationSubgroup:=MapGroup(eRec.RotationSubgroup);
      fi;
      Add(NewList, fRec);
    od;
    Add(NewListOrbitByRank, NewList);
  od;
  return rec(ListOrbitByRank:=NewListOrbitByRank, 
             IdentityElt:=eRecordTessel.IdentityElt);
end;


FromCoveringToPuzzleTiling:=function(ListEXT)
  local eRec, ListEXTred, ListFACred, rnk, IsFinished, nbPoly, iPolySelect, iPoly, jPoly, ListEXTint, ListFACint, EXTint, FACint, eSet, FACtot, test, NewListEXT_1, NewListEXT_2, rnkint;
  eRec:=ColumnReductionExten(ListEXT[1]);
  ListEXTred:=List(ListEXT, x->Set(List(x, y->RemoveFraction(y{eRec.Select}))));
  ListFACred:=List(ListEXTred, DualDescription);
  rnk:=Length(eRec.Select);
  Print("rnk=", rnk, "\n");
  while(true)
  do
    IsFinished:=true;
    nbPoly:=Length(ListEXTred);
    iPolySelect:=-1;
    for iPoly in [1..nbPoly]
    do
      Print("iPoly=", iPoly, "\n");
      if iPolySelect=-1 then
        ListEXTint:=[];
        ListFACint:=[];
        for jPoly in Difference([1..nbPoly],[iPoly])
        do
          FACtot:=Concatenation(ListFACred[iPoly],ListFACred[jPoly]);
          EXTint:=Set(DualDescription(FACtot));
          rnkint:=RankMat(EXTint);
          Print("  jPoly=", jPoly, " rnkint=", rnkint, "\n");
          if rnkint=rnk then
            test:=First(ListFACred[jPoly], x->First(ListEXTred[iPoly], y->y*x<0)<>fail);
            Print("test=", test, "\n");
            if test<>fail then
              FACint:=DualDescription(EXTint);
              Add(ListEXTint, EXTint);
              Add(ListFACint, FACint);
              iPolySelect:=iPoly;
            fi;
          fi;
        od;
        Print("   iPolySelect=", iPolySelect, "\n");
        if iPolySelect<>-1 then
          IsFinished:=false;
          eSet:=Difference([1..nbPoly], [iPolySelect]);
          ListEXTred:=Concatenation(ListEXTred{eSet}, ListEXTint);
          ListFACred:=Concatenation(ListFACred{eSet}, ListFACint);
        fi;
      fi;
    od;
    if IsFinished=true then
      break;
    fi;
  od;
  NewListEXT_1:=List(Set(ListEXTred), x->x*eRec.eMatBack);
  NewListEXT_2:=List(NewListEXT_1, x->List(x, y->y/y[1]));
  return NewListEXT_2;
end;



CheckCellularDecomposition:=function(EXTmain, TheStab, ListEXT)
  local TheActionFace, eRepr, SetEXT, O, ListPermGens, eGen, eList, EXT, pos, eSelect, rnk, ListEXTproj, ListFAC, FAC1, FAC2, TheVol, TheVolParts, TheVolTotal, EXTprojPoly, eRecPoly, EXTmainPoly, EXTmainProj, eFAC, FACmain, EXTproj, eEXT, FACint, EXTint, nbEXT, eOrb, ListOrb, FAC, GRPperm, EXTvol;
  TheActionFace:=function(x, g)
    return Set(x*g);
  end;
  ListPermGens:=[];
  for eGen in GeneratorsOfGroup(TheStab)
  do
    eList:=[];
    for EXT in ListEXT
    do
      pos:=Position(ListEXT, TheActionFace(EXT, eGen));
      Add(eList, pos);
    od;
    Add(ListPermGens, PermList(eList));
  od;
  #
  eSelect:=ColumnReduction(EXTmain).Select;
  rnk:=Length(eSelect);
  ListEXTproj:=[];
  ListFAC:=[];
  for EXT in ListEXT
  do
    EXTproj:=List(EXT, x->x{eSelect});
    FAC:=DualDescription(EXTproj);
    Add(ListEXTproj, EXTproj);
    Add(ListFAC, FAC);
  od;
  #
  nbEXT:=Length(ListEXT);
  GRPperm:=PersoGroupPerm(ListPermGens);
  ListOrb:=__RepresentativeOrbitTwoSet(GRPperm, [1..nbEXT]);
  for eOrb in ListOrb
  do
    FAC1:=ListFAC[eOrb[1]];
    FAC2:=ListFAC[eOrb[2]];
    FACint:=Concatenation(FAC1, FAC2);
    EXTint:=DualDescription(FACint);
    if RankMat(EXTint)=rnk then
      Print("The dimension of the intersection is not correct\n");
      Print("rnk=", rnk, "\n");
      Error("Please correct");
    fi;
  od;
  EXTmainProj:=List(EXTmain, x->x{eSelect});
  FACmain:=DualDescription(EXTmainProj);
  for EXTproj in ListEXTproj
  do
    for eEXT in EXTproj
    do
      for eFAC in FACmain
      do
        if eEXT*eFAC<0 then
          Error("One cell is not contained in the bigger one");
        fi;
      od;
    od;
  od;
  eRecPoly:=GetPolytopizationInfo(EXTmainProj);
  EXTvol:=RemoveRedundancyByDualDescription(EXTmainProj);
  EXTmainPoly:=DoPolytopization(eRecPoly, EXTvol);
#  EXTmainPoly:=DoPolytopization(eRecPoly, EXTmainProj);
  TheVolTotal:=VolumeComputationPolytope(EXTmainPoly);
  TheVolParts:=0;
  for EXTproj in ListEXTproj
  do
    EXTvol:=RemoveRedundancyByDualDescription(EXTproj);
    EXTprojPoly:=DoPolytopization(eRecPoly, EXTvol);
#    EXTprojPoly:=DoPolytopization(eRecPoly, EXTproj);
    TheVol:=VolumeComputationPolytope(EXTprojPoly);
#    Print("TheVol=", TheVol, "\n");
    TheVolParts:=TheVolParts+TheVol;
  od;
  if TheVolParts<>TheVolTotal then
    Print("TheVolParts=", TheVolParts, "\n");
    Print("TheVolTotal=", TheVolTotal, "\n");
    Print("We have a volume pb\n");
    Error("Please correct");
  fi;
end;


GetCollectionSubfaces:=function(eRecordTessel, iRank, iOrbit)
  local ListListColl, EXT, nbV, eRecTop, ePermStab, j, TheNewList, FuncInsertFace, eOrbit, jOrbit, eElt, eBound, iBound, iFace, eProd, EXTface, eSet, eSetConv, NSP, EXTimage, nbBound, eList, ListPermGens, eGen, TheStab, eRecIns;
  ListListColl:=[];
  EXT:=eRecordTessel.ListOrbitByRank[iRank+2][iOrbit].EXT;
  nbV:=Length(EXT);
  eRecTop:=rec(iOrbit:=iOrbit, eSet:=[1..nbV], eSetConv:=[1..nbV], eElt:=eRecordTessel.IdentityElt);
  ListListColl[iRank+1]:=[eRecTop];
  TheStab:=eRecordTessel.ListOrbitByRank[iRank+2][iOrbit].TheStab;
  ListPermGens:=[];
  for eGen in GeneratorsOfGroup(TheStab)
  do
    eList:=List(EXT, x->Position(EXT, x*eGen));
    Add(ListPermGens, PermList(eList));
  od;
  ePermStab:=PersoGroupPerm(ListPermGens);
  for j in Reversed([0..iRank-1])
  do
    TheNewList:=[];
    FuncInsertFace:=function(eRec)
      local fRec, test;
      for fRec in TheNewList
      do
        if fRec.iOrbit=eRec.iOrbit then
          test:=RepresentativeAction(ePermStab, eRec.eSet, fRec.eSet, OnSets);
          if test<>fail then
            return;
          fi;
        fi;
      od;
      Add(TheNewList, eRec);
    end;
    for eOrbit in ListListColl[j+2]
    do
      jOrbit:=eOrbit.iOrbit;
      eElt:=eOrbit.eElt;
      eBound:=eRecordTessel.ListOrbitByRank[j+3][jOrbit].BoundaryImage;
      nbBound:=Length(eBound.ListIFace);
      for iBound in [1..nbBound]
      do
        iFace:=eBound.ListIFace[iBound];
        eProd:=eBound.ListElt[iBound]*eElt;
        EXTface:=eRecordTessel.ListOrbitByRank[j+2][iFace].EXT;
        EXTimage:=EXTface*eProd;
        eList:=List(EXTimage, x->Position(EXT, x));
        if Position(eList, fail)<>fail then
          Error("Please dbug from here");
        fi;
        eSet:=Set(eList);
        NSP:=NullspaceMat(TransposedMat(EXTimage));
        eSetConv:=Filtered([1..nbV], x->First(NSP, y->y*EXT[x]<>0)=fail);
        eRecIns:=rec(iOrbit:=iFace, eSet:=eSet, eSetConv:=eSetConv, eElt:=eProd);
        FuncInsertFace(eRecIns);
      od;
    od;
    ListListColl[j+1]:=TheNewList;
  od;
  return ListListColl;
end;



CheckDecomposition:=function(eRecordTessel, eCase)
  local iRank, iOrbit, EXTmain, TheStab, ListEXT, eRepr, SetEXT, O, TheActionFace, eReply, TheConstraint;
  TheActionFace:=function(x, g)
    return Set(x*g);
  end;
  iRank:=eCase.iRank;
  iOrbit:=eCase.iOrbit;
  EXTmain:=eRecordTessel.ListOrbitByRank[iRank+2][iOrbit].EXT;
  TheStab:=eRecordTessel.ListOrbitByRank[iRank+2][iOrbit].TheStab;
  ListEXT:=[];
  for eRepr in eCase.ListRepresentent
  do
    SetEXT:=Set(eRepr.EXT);
    # now testing that dual 
    if Length(SetEXT)<>Length(eRepr.EXT) then
      Error("Repetition in eCase.ListRepresentent");
    fi;
    TheConstraint:=rec(ListStrictlyPositive:=[  ],
                       ListPositive:=[1..Length(eRepr.EXT)],
                       ListSetStrictPositive:=[[1..Length(eRepr.EXT)]]);
    eReply:=SearchPositiveRelation(eRepr.EXT, TheConstraint);
    if eReply<>false then
      Print("The vertices do not define a polytope\n");
      Error("Please correct this major error\n");
    fi;
    O:=Orbit(TheStab, SetEXT, TheActionFace);
    Append(ListEXT, O);
  od;
  CheckCellularDecomposition(EXTmain, TheStab, ListEXT);
end;


CheckFacenessOfDecomposition:=function(eRecordTessel, eCase)
  local iRank, iOrbit, ListListColl, fElt, fSet, kOrbit, jOrbit, eRec, EXT, TheStab, ListPermGens, ListMatrGens, eGen, eList, FACproj, EXTfsetProj, eSelect, EXTcontained, EXTcontainedProj, NSP, eRepr, len, Orecord, eStabPerm, i, eSet, jRank, ListViolator, eRecViolator, FACfsetProj, TheLin;
  iRank:=eCase.iRank;
  iOrbit:=eCase.iOrbit;
  ListListColl:=GetCollectionSubfaces(eRecordTessel, iRank, iOrbit);
  EXT:=eRecordTessel.ListOrbitByRank[iRank+2][iOrbit].EXT;
  TheStab:=eRecordTessel.ListOrbitByRank[iRank+2][iOrbit].TheStab;
  ListPermGens:=[];
  ListMatrGens:=GeneratorsOfGroup(TheStab);
  for eGen in ListMatrGens
  do
    eList:=List(EXT, x->Position(EXT, x*eGen));
    Add(ListPermGens, PermList(eList));
  od;
  eStabPerm:=Group(ListPermGens);
  ListViolator:=[];
  for jRank in [1..iRank-1]
  do
    for jOrbit in [1..Length(ListListColl[jRank+1])]
    do
      eRec:=ListListColl[jRank+1][jOrbit];
      eSet:=eRec.eSet;
      kOrbit:=eRec.iOrbit;
      Orecord:=OrbitWithAction(eStabPerm, eSet, OnSets);
      len:=Length(Orecord.ListCoset);
      for i in [1..len]
      do
        fSet:=Orecord.ListCoset[i];
        fElt:=Orecord.ListElement[i];
        NSP:=NullspaceMat(TransposedMat(EXT{fSet}));
        for eRepr in eCase.ListRepresentent
        do
          EXTcontained:=Filtered(eRepr.EXT, x->First(NSP, y->y*x<>0)=fail);
          if Length(EXTcontained)>=2 then
            if RankMat(EXTcontained)=jRank+1 then
              eSelect:=ColumnReduction(EXTcontained).Select;
              EXTcontainedProj:=List(EXTcontained, x->x{eSelect});
              FACproj:=DualDescription(EXTcontainedProj);
              EXTfsetProj:=List(EXT{fSet}, x->x{eSelect});
              FACfsetProj:=DualDescription(EXTfsetProj);
              TheLin:=LinearDeterminedByInequalities(Concatenation(FACproj, FACfsetProj));
              if Length(TheLin)=jRank+1 then
                if First(EXTfsetProj, x->First(FACproj, y->y*x<0)<>fail)<>fail then
                  Print("SplitFace iRank=", iRank, " iOrbit=", kOrbit, "\n");
                  eRecViolator:=rec(iRank:=jRank,
                                    iOrbit:=kOrbit,
                                    eSet:=eSet,
                                    EXTcontained:=EXTcontained,
                                    fSet:=fSet);
                  Add(ListViolator, eRecViolator);
                fi;
              fi;
            fi;
          fi;
        od;
      od;
    od;
  od;
  return rec(ListViolator:=ListViolator, 
             ListListColl:=ListListColl);
end;




GetCompleteAndTotalDecomposition:=function(EXT, eStabPerm, FunctionFaceDecomposition, eRecordTessel)
  local rnk, NewListOrbitByRank, FuncInsertSpecifiedRank, NewListSign, iOrbit, iRank, lenBound, iBound, eSign, eAddElt, ListOccuringCoefficients, pos, eMulSign, ListElementM2, FuncSignatureDet, iFaceM2, iL, eSetF, ListSetsM2, eEltM1, TheBoundary, iBoundB, eEltM2, lenBoundB, iFaceM1, NewListElt, NewListIFace, eRecord, len, nbOrbit, eRecIns, NewBound, eRec, GetBoundaryIrredNew, eRecFace, TheList, eNewElt, iFaceB, eSetB, EXTtile, EXTtileB, eBound, eEltB, iB, lenB, ListSetsM1, eSetM1, ListSetsM1red, eSetM1red, EXTred, LSet, LSetExp, LIneqLSet, LIneqListSetsM1, EXTreo, ListLenBoundB, ListListBound, LBound, eSetRM;
  rnk:=RankMat(EXT)-1;
  NewListOrbitByRank:=[rec(EXT:=[], TheStab:="irrelevant", BoundaryImage:="irrelevant", TheDel:="irrelevant")];
  for iRank in [0..rnk-1]
  do
    Add(NewListOrbitByRank, []);
  od;
  Print("GetCompleteAndTotalDecomposition, |eStabPerm|=", Order(eStabPerm), "\n");
  Add(NewListOrbitByRank, [rec(EXT:=EXT, 
        TheStab:=eStabPerm,
        eSet:=[1..Length(EXT)],
        ePermElt:=(), 
        Nature:="new",
        eKey:="irrel")]);
  FuncInsertSpecifiedRank:=function(iRankTarget, eNewFace)
    local iOrbitIter, testPerm, nbOrbit, TheStab;
    nbOrbit:=Length(NewListOrbitByRank[iRankTarget+2]);
    for iOrbitIter in [1..nbOrbit]
    do
      testPerm:=RepresentativeAction(eStabPerm, NewListOrbitByRank[iRankTarget+2][iOrbitIter].eSet, eNewFace.eSet, OnSets);
      if testPerm<>fail then
        return rec(iOrbit:=iOrbitIter, ePerm:=testPerm);
      fi;
    od;
    Add(NewListOrbitByRank[iRankTarget+2], eNewFace);
    TheStab:=Stabilizer(eStabPerm, eNewFace.eSet, OnSets);
    NewListOrbitByRank[iRankTarget+2][nbOrbit+1].TheStab:=TheStab;
    return rec(iOrbit:=nbOrbit+1, ePerm:=());
  end;
  GetBoundaryIrredNew:=function(iRank, iOrbit)
    local eKey, eSet, EXTf, EXTirred, eSetIrred, eRecBound, eBound, eSet1, ListRec, len, iL, iFace, eElt, NSP, EXTface, EXTfaceTotal, TheNewList, lenB, iLB, eSetFace, iRankSave, iOrbitSave, eSetC, eSetBig, eNewElt, eEltC, SecondGRP;
    eKey:=NewListOrbitByRank[iRank+2][iOrbit].eKey;
    if eKey="irrel" then
      eSet:=NewListOrbitByRank[iRank+2][iOrbit].eSet;
      EXTf:=EXT{eSet};
      EXTirred:=RemoveRedundancyByDualDescription(EXTf);
      eSetIrred:=List(EXTirred, x->Position(EXT, x));
      if Length(Set(eSetIrred))<>Length(eSetIrred) then
        Error("1: Incorrection in the code");
      fi;
      Print("1: eSetIrred=", eSetIrred, " eStabPerm=", eStabPerm, "\n");
      SecondGRP:=SecondReduceGroupAction(eStabPerm, eSetIrred);
      eRecBound:=BoundaryOperatorsCellularDecompositionPolytope(SecondGRP, EXTirred, iRank-1);
      NewListOrbitByRank[iRank+2][iOrbit].eSetIrred:=eSetIrred;
      NewListOrbitByRank[iRank+2][iOrbit].eRecBound:=eRecBound;
      eKey:=rec(iRank:=iRank, iOrbit:=iOrbit, jOrbit:=1);
    fi;
    eRecBound:=NewListOrbitByRank[eKey.iRank+2][eKey.iOrbit].eRecBound;
    eSetBig:=NewListOrbitByRank[eKey.iRank+2][eKey.iOrbit].eSet;
    eSetIrred:=NewListOrbitByRank[eKey.iRank+2][eKey.iOrbit].eSetIrred;
    eBound:=eRecBound.ListOrbitByRank[iRank+2][eKey.jOrbit].BoundaryImage;
    eEltC:=NewListOrbitByRank[iRank+2][iOrbit].ePermElt;
    eSetC:=OnSets(eRecBound.ListOrbitByRank[iRank+2][eKey.jOrbit].eSet,eEltC);
    eSet1:=NewListOrbitByRank[iRank+2][iOrbit].eSet;
    if IsSubset(eSet1, eSetIrred{eSetC})=false then
      Error("Clear error");
    fi;
    iRankSave:=eKey.iRank;
    iOrbitSave:=eKey.iOrbit;
    len:=Length(eBound.ListIFace);
    ListRec:=[];
    for iL in [1..len]
    do
      Print("iL=", iL, "/", len, "\n");
      iFace:=eBound.ListIFace[iL];
      eElt:=eBound.ListElt[iL];
      eNewElt:=eElt*eEltC;
      eSet:=OnSets(eRecBound.ListOrbitByRank[iRank+1][iFace].eSet,eNewElt);
      EXTface:=EXT{eSetIrred{eSet}};
      NSP:=NullspaceMat(TransposedMat(EXTface));
      EXTfaceTotal:=Filtered(EXT{eSet1}, x->First(NSP, y->y*x<>0)=fail);
      if IsSubset(Set(EXTfaceTotal), Set(EXT{eSetIrred{eSet}}))=false then
        Error("Please debug from here");
      fi;
      Print("|EXTface|=", Length(EXTface), " |EXTfaceTotal|=", Length(EXTfaceTotal), "\n");
      if Length(EXTfaceTotal)=0 then
        Error("Debug horrors from here");
      fi;
      TheNewList:=FunctionFaceDecomposition(EXTfaceTotal);
      lenB:=Length(TheNewList.ListEXT);
      if lenB=1 then
        eKey:=rec(iRank:=iRankSave, iOrbit:=iOrbitSave, jOrbit:=iFace);
      else
        eKey:="irrel";
      fi;
      Print("   lenB=", lenB, "\n");
      for iLB in [1..lenB]
      do
        eSetFace:=Set(List(TheNewList.ListEXT[iLB], x->Position(EXT,x)));
        EXTreo:=EXT{eSetFace};
        Print("BB |EXT|=", Length(EXT), " eSetFace=", eSetFace, "\n");
        if IsSubset(NewListOrbitByRank[iRank+2][iOrbit].eSet, eSetFace)=false then
          Error("Bookkeeping error 1");
        fi;
        if lenB=1 and IsSubset(eSetFace, eSetIrred{eSet})=false then
          Error("Error in the run");
        fi;
        if Position(eSetFace, fail)<>fail then
          Error("Please debug from here eSetFace");
        fi;
        eRec:=rec(eKey:=eKey, EXT:=EXTreo, 
                  ePermElt:=eNewElt, 
                  eSet:=eSetFace, 
                  Nature:=TheNewList.ListNature[iLB],
                  iOrbitOld:=TheNewList.ListIOrbitOld[iLB],
                  eElt:=TheNewList.ListElt[iLB]);
        Add(ListRec, eRec);
      od;
    od;
    return ListRec;
  end;
  for iRank in Reversed([1..rnk])
  do
    nbOrbit:=Length(NewListOrbitByRank[iRank+2]);
    for iOrbit in [1..nbOrbit]
    do
      eRecord:=NewListOrbitByRank[iRank+2][iOrbit];
      NewListIFace:=[];
      NewListElt:=[];
      if eRecord.Nature="old" then
        eBound:=eRecordTessel.ListOrbitByRank[iRank+2][eRecord.iOrbitOld].BoundaryImage;
        lenB:=Length(eBound.ListIFace);
        for iB in [1..lenB]
        do
          iFaceB:=eBound.ListIFace[iB];
          eEltB:=eBound.ListElt[iB];
          eNewElt:=eEltB*eRecord.eElt;
          EXTtile:=eRecordTessel.ListOrbitByRank[iRank+1][iFaceB].EXT*eNewElt;
          eSetB:=Set(List(EXTtile, x->Position(EXT, x)));
          EXTtileB:=EXT{eSetB};
          Print("AA |EXT|=", Length(EXT), " eSetB=", eSetB, "\n");
          if Position(eSetB, fail)<>fail then
            Error("Please debug from here eSetB");
          fi;
          if IsSubset(eRecord.eSet, eSetB)=false then
            Error("Bookkeeping error 2");
          fi;
          eRecFace:=rec(EXT:=EXTtileB,
                        eSet:=eSetB, 
                        iOrbitOld:=iFaceB,
                        eElt:=eNewElt, 
                        Nature:="old");
          eRecIns:=FuncInsertSpecifiedRank(iRank-1, eRecFace);
          Add(NewListIFace, eRecIns.iOrbit);
          Add(NewListElt, eRecIns.ePerm);
        od;
      fi;
      if eRecord.Nature="new" then
        TheList:=GetBoundaryIrredNew(iRank, iOrbit);
        for eRec in TheList
        do
          eRecIns:=FuncInsertSpecifiedRank(iRank-1, eRec);
          Add(NewListIFace, eRecIns.iOrbit);
          Add(NewListElt, eRecIns.ePerm);
        od;
      fi;
      NewBound:=rec(ListIFace:=NewListIFace, ListElt:=NewListElt);
      NewListOrbitByRank[iRank+2][iOrbit].BoundaryImage:=NewBound;
    od;
  od;
  nbOrbit:=Length(NewListOrbitByRank[2]);
  for iOrbit in [1..nbOrbit]
  do
    NewListOrbitByRank[2][iOrbit].BoundaryImage:=rec(ListIFace:=[1], ListElt:=[()]);
  od;
  FuncSignatureDet:=function(iRank, iOrbit, eElt)
    local eSet, TheRed, TheBasis, eMat, iExt;
    if not(eElt in NewListOrbitByRank[iRank+2][iOrbit].TheStab) then
      Error("The element is not in the stabilizer, please panic");
    fi;
    eSet:=NewListOrbitByRank[iRank+2][iOrbit].eSet;
    TheRed:=RowReduction(EXT{eSet});
    TheBasis:=TheRed.EXT;
    eMat:=[];
    for iExt in TheRed.Select
    do
      Add(eMat, SolutionMat(TheBasis, EXT[OnPoints(eSet[iExt],eElt)]));
    od;
    return DeterminantMat(eMat);
  end;
  Print("Building differentials in CompleteAndTotal\n");
  for iRank in [0..rnk]
  do
    Print("iRank=", iRank, "/", rnk, "\n");
    nbOrbit:=Length(NewListOrbitByRank[iRank+2]);
    for iOrbit in [1..nbOrbit]
    do
      Print("  iOrbit=", iOrbit, "/", nbOrbit, "\n");
      eRecord:=NewListOrbitByRank[iRank+2][iOrbit];
      if iRank=0 then
        NewListSign:=[1];
      else
        NewListIFace:=eRecord.BoundaryImage.ListIFace;
        NewListElt:=eRecord.BoundaryImage.ListElt;
        len:=Length(NewListIFace);
        for iL in [1..len]
        do
          if IsSubset(Set(EXT{eRecord.eSet}), Set(EXT{OnSets(NewListOrbitByRank[iRank+1][NewListIFace[iL]].eSet, NewListElt[iL])}))=false then
            Error("bookkeeping error 3");
          fi;
        od;
        if iRank=1 then
          if Length(NewListIFace)<>2 then
            Error("Deep inconsistency apparently");
          fi;
          NewListSign:=[1,-1];
        else
          ListSetsM2:=[];
          ListElementM2:=[];
          ListOccuringCoefficients:=[];
          lenBound:=Length(NewListIFace);
          ListSetsM1:=[];
          ListSetsM1red:=[];
          ListLenBoundB:=[];
          ListListBound:=[];
          eSetRM:=NewListOrbitByRank[iRank+2][iOrbit].eSet;
          for iL in [1..lenBound]
          do
            iFaceM1:=NewListIFace[iL];
            eEltM1:=NewListElt[iL];
            TheBoundary:=NewListOrbitByRank[iRank+1][iFaceM1].BoundaryImage;
            eSetM1:=OnSets(NewListOrbitByRank[iRank+1][iFaceM1].eSet, eEltM1);
            Add(ListSetsM1, eSetM1);
            eSetM1red:=List(eSetM1, x->Position(eSetRM, x));
            Add(ListSetsM1red, eSetM1red);
            lenBoundB:=Length(TheBoundary.ListIFace);
            Add(ListLenBoundB, lenBoundB);
            LBound:=[];
            for iBoundB in [1..lenBoundB]
            do
              iFaceM2:=TheBoundary.ListIFace[iBoundB];
              eSign:=TheBoundary.ListSign[iBoundB];
              eEltM2:=TheBoundary.ListElt[iBoundB];
              eAddElt:=eEltM2*eEltM1;
              eSetF:=OnSets(NewListOrbitByRank[iRank][iFaceM2].eSet, eAddElt);
              Add(LBound, eSetF);
              pos:=Position(ListSetsM2, eSetF);
              if pos=fail then
                Add(ListSetsM2, eSetF);
                Add(ListElementM2, eAddElt);
                Add(ListOccuringCoefficients, [rec(Sign:=eSign, idx:=iL)]);
              else
                eMulSign:=FuncSignatureDet(iRank-2, iFaceM2, ListElementM2[pos]*eAddElt^(-1));
                Add(ListOccuringCoefficients[pos], rec(Sign:=eMulSign*eSign, idx:=iL));
              fi;
            od;
            Add(ListListBound, LBound);
          od;
          EXTred:=ColumnReduction(NewListOrbitByRank[iRank+2][iOrbit].EXT).EXT;
          LSet:=DualDescriptionSets(EXTred);
          LSetExp:=List(LSet, x->eSetRM{x});
# ListSetsM2[11] is a problematic face. It is contained only
# in one of ListSetsM1. Is it in LSetExp? No contained two times, 
# in 2 and 4 (of [1..5])
# 2 corresponds to 5 and 6.
# 4 corresponds to 4.
# The other merging is obtained via 5 corresponds to 1 and 2.
          LIneqLSet:=List(LSet, x->__FindFacetInequality(EXTred, x));
          LIneqListSetsM1:=List(ListSetsM1red, x->__FindFacetInequality(EXTred, x));
          NewListSign:=UntangleAllSigns(ListOccuringCoefficients, lenBound);
        fi;
      fi;
      NewListOrbitByRank[iRank+2][iOrbit].BoundaryImage.ListSign:=NewListSign;
    od;
  od;
  return rec(ListOrbitByRank:=NewListOrbitByRank, rnk:=rnk);
end;




DoClotureOperation:=function(TheBound, eCase)
  local iRank, iOrbit, TheStab, EXT, rnk, EXTmain, eRepr, eEXT, ListPermGens, eList, eStabPerm, IsInListSetConv, ListReturn, NewListRepr, ListRecConv, GetFaceDecomposition, EXTface, EXTfaceTotal, eSetConvB, IsNewFace, eSetConv, test, rnkFace, NSP, jRank, EXTirred, nbOrbit, eRecBound, jOrbit, SecondGRP, eSetIrred, ListSets, O, eStabPermMain, eSet, eGen, ListListConv, eNewElt, FuncInsert, EXTf, eAtt, iFace, eElt, TheBoundary, len, iL, nbAtt, iAtt, phi, ListMatrGens, eStabCell, nbRepr, iRepr, EXTrenorm, eReprEXTrenorm, eRecConvIns;
  if Length(eCase.ListRepresentent)=0 then
    Error("What exactly did you imagined?");
  fi;
  Print("Beginning DoClotureOperation\n");
  iRank:=eCase.iRank;
  iOrbit:=eCase.iOrbit;
  EXT:=TheBound.ListOrbitByRank[iRank+2][iOrbit].EXT;
  TheStab:=TheBound.ListOrbitByRank[iRank+2][iOrbit].TheStab;
  ListPermGens:=[];
  ListMatrGens:=GeneratorsOfGroup(TheStab);
  for eGen in ListMatrGens
  do
    eList:=List(EXT, x->Position(EXT, x*eGen));
    Add(ListPermGens, PermList(eList));
  od;
  eStabPerm:=Group(ListPermGens);
  Print("|EXT|=", Length(EXT), " |eStabPerm|=", Order(eStabPerm), "\n");
  phi:=GroupHomomorphismByImagesNC(TheStab, eStabPerm, ListMatrGens, ListPermGens);
  Print("We have phi\n");
  ListListConv:=[];
  ListListConv[iRank+1]:=[rec(eSetConv:=[1..Length(EXT)],
       ListAtt:=[rec(iOrbit:=iOrbit, eMat:=TheBound.IdentityElt)])];
  for jRank in Reversed([0..iRank-1])
  do
    Print("jRank=", jRank, " iRank=", iRank, "\n");
    ListListConv[jRank+1]:=[];
    FuncInsert:=function(eSetConv, eRec)
      local iRecConv, eRecConv, ePerm, lenConv;
      lenConv:=Length(ListListConv[jRank+1]);
      for iRecConv in [1..lenConv]
      do
        eRecConv:=ListListConv[jRank+1][iRecConv];
        ePerm:=RepresentativeAction(eStabPerm, eSetConv, eRecConv.eSetConv, OnSets);
        if ePerm<>fail then
          Add(ListListConv[jRank+1][iRecConv].ListAtt, rec(iOrbit:=eRec.iOrbit, eMat:=eRec.eMat*PreImagesRepresentative(phi, ePerm)));
          return;          
        fi;
      od;
      Add(ListListConv[jRank+1], rec(eSetConv:=eSetConv, ListAtt:=[eRec]));
    end;
    nbOrbit:=Length(ListListConv[jRank+2]);
    Print("nbOrbit=", nbOrbit, "\n");
    for iOrbit in [1..nbOrbit]
    do
      nbAtt:=Length(ListListConv[jRank+2][iOrbit].ListAtt);
      Print("iOrbit=", iOrbit, "/", nbOrbit, " nbAtt=", nbAtt, "\n");
      for iAtt in [1..nbAtt]
      do
        eAtt:=ListListConv[jRank+2][iOrbit].ListAtt[iAtt];
        TheBoundary:=TheBound.ListOrbitByRank[jRank+3][eAtt.iOrbit].BoundaryImage;
        len:=Length(TheBoundary.ListIFace);
        Print("jRank=", jRank, "/", iRank, " iOrbit=", iOrbit, "/", nbOrbit, " iAtt=", iAtt, "/", nbAtt, " len=", len, "\n");
        for iL in [1..len]
        do
          iFace:=TheBoundary.ListIFace[iL];
          eElt:=TheBoundary.ListElt[iL];
          eNewElt:=eElt*eAtt.eMat;
          EXTf:=TheBound.ListOrbitByRank[jRank+2][iFace].EXT*eNewElt;
          NSP:=NullspaceMat(TransposedMat(EXTf));
          EXTface:=Filtered(EXT, x->First(NSP, y->y*x<>0)=fail);
          eSetConv:=Set(List(EXTface, x->Position(EXT, x)));
          FuncInsert(eSetConv, rec(iOrbit:=iFace, eMat:=eNewElt));
        od;
      od;
    od;
  od;
  Print("The set ListListConv has been created\n");
  IsInListSetConv:=function(iRank, eSetConv)
    local eOrbit, ePerm;
    for eOrbit in ListListConv[iRank+1]
    do
      ePerm:=RepresentativeAction(eStabPerm, eOrbit.eSetConv, eSetConv, OnSets);
      if ePerm<>fail then
        return true;
      fi;
    od;
    return false;
  end;
  rnk:=RankMat(EXT)-1;
  EXTmain:=[];
  for eRepr in eCase.ListRepresentent
  do
    for eEXT in eRepr.EXT
    do
      if Position(EXTmain, eEXT)=fail then
        Append(EXTmain, Orbit(TheStab, eEXT, OnPoints));
      fi;
    od;
  od;
  Print("DoCloture, EXTmain created |EXTmain|=", Length(EXTmain), "\n");
  if IsSubset(Set(EXTmain), Set(EXT))=false then
    Error("We fail the inclusion test");
  fi;
  ListPermGens:=[];
  for eGen in GeneratorsOfGroup(TheStab)
  do
    eList:=List(EXTmain, x->Position(EXTmain, x*eGen));
    Add(ListPermGens, PermList(eList));
  od;
  eStabPermMain:=Group(ListPermGens);
  Print("DoCloture, eStabPermMain created\n");
  ListSets:=[];
  for eRepr in eCase.ListRepresentent
  do
    eSet:=Set(List(eRepr.EXT, x->Position(EXTmain, x)));
    O:=Orbit(eStabPermMain, eSet, OnSets);
    Append(ListSets, O);
  od;
  GetFaceDecomposition:=function(EXTface, EXTref)
    local rnkFace, eSetFace, ListCand, NewListCand, ListReturn, NewListReturn, eCand, IsOK, eSetB, eSet, eSetInt;
    rnkFace:=RankMat(EXTface);
    eSetFace:=Set(List(EXTface, x->Position(EXTmain, x)));
    ListCand:=[eSetFace];
    ListReturn:=[];
    while(true)
    do
      NewListCand:=[];
      for eCand in ListCand
      do
        IsOK:=true;
        for eSet in ListSets
        do
          eSetInt:=Intersection(eCand, eSet);
# deadly approximation. Why did we wrote that?
# It has to be related to our problems.
          if Length(eSetInt) < Length(eCand) and Length(eSetInt)>0 then
            if RankMat(EXTmain{eSetInt})=rnkFace then
              IsOK:=false;
              AddSet(NewListCand, eSetInt);
            fi;
          fi;
        od;
        if IsOK=true then
          Add(ListReturn, eCand);
        fi;
      od;
      if Length(NewListCand)=0 then
        break;
      fi;
      ListCand:=ShallowCopy(NewListCand);
    od;
    NewListReturn:=[];
    for eSet in ListReturn
    do
      eSetB:=Set(List(eSet, x->Position(EXTref, EXTmain[x])));
      Add(NewListReturn, eSetB);
    od;
    return NewListReturn;
  end;
  NewListRepr:=[];
  nbRepr:=Length(eCase.ListRepresentent);
  for iRepr in [1..nbRepr]
  do
    Print("DoCloture iRepr=", iRepr, "/", nbRepr, "\n");
    eRepr:=eCase.ListRepresentent[iRepr];
    if TestForRepetition(eRepr.EXT)=true then
      Print("The array eRepr.EXT has some repetition\n");
      Print("and this is not allowed in DoClotureOperation\n");
      Error("Please correct");
    fi;
    EXTirred:=RemoveRedundancyByDualDescription(eRepr.EXT);
    eSetIrred:=List(EXTirred, x->Position(EXTmain, x));
    if Position(eSetIrred, fail)<>fail then
      Error("Please debug from that point");
    fi;
    eStabCell:=Stabilizer(eStabPermMain, Set(eSetIrred), OnSets);
    if Length(Set(eSetIrred))<>Length(eSetIrred) then
      Error("2: Incorrection in the code");
    fi;
    SecondGRP:=SecondReduceGroupAction(eStabCell, eSetIrred);
    eRecBound:=BoundaryOperatorsCellularDecompositionPolytope(SecondGRP, EXTirred, iRank-1);
    ListRecConv:=[];
    for jRank in [1..iRank]
    do
      Print("jRank=", jRank, "/", iRank, "\n");
      nbOrbit:=Length(eRecBound.ListOrbitByRank[jRank+2]);
      for jOrbit in [1..nbOrbit]
      do
        EXTface:=EXTirred{eRecBound.ListOrbitByRank[jRank+2][jOrbit].eSet};
        NSP:=NullspaceMat(TransposedMat(EXTface));
        EXTfaceTotal:=Filtered(eRepr.EXT, x->First(NSP, y->y*x<>0)=fail);
        rnkFace:=RankMat(EXTfaceTotal)-1;
        if IsSubset(Set(EXT), Set(EXTfaceTotal))=false then
          IsNewFace:=true;
        else
          eSetConv:=Set(List(EXTfaceTotal, x->Position(EXT, x)));
          test:=IsInListSetConv(rnkFace, eSetConv);
          if test=true then
            IsNewFace:=false;
          else
            IsNewFace:=true;
          fi;
        fi;
        if IsNewFace=true then
          eSetConvB:=Set(List(EXTfaceTotal, x->Position(eRepr.EXT, x)));
          ListReturn:=GetFaceDecomposition(EXTfaceTotal, eRepr.EXT);
          if Length(ListReturn)>1 then
            eRecConvIns:=rec(eSetConv:=eSetConvB, ListSets:=ListReturn);
            Add(ListRecConv, eRecConvIns);
          fi;
        fi;
      od;
    od;
    Add(NewListRepr, rec(EXT:=eRepr.EXT, ListRecConv:=ListRecConv));
  od;
  Print("DoCloture finished\n");
  return rec(iRank:=eCase.iRank, iOrbit:=eCase.iOrbit, ListRepresentent:=NewListRepr);
end;




DoClotureOperation_NextGeneration:=function(TheBound, eCase)
  local iRank, iOrbit, TheStab, EXT, rnk, EXTmain, eRepr, eEXT, ListPermGens, eList, eStabPerm, IsInListSetConv, ListReturn, NewListRepr, ListRecConv, GetFaceDecomposition, EXTface, EXTfaceTotal, eSetConvB, IsNewFace, eSetConv, test, rnkFace, NSP, jRank, EXTirred, nbOrbit, eRecBound, jOrbit, SecondGRP, eSetIrred, ListSets, O, eStabPermMain, eSet, eGen, ListListConv, eNewElt, FuncInsert, EXTf, eAtt, iFace, eElt, TheBoundary, len, iL, nbAtt, iAtt, phi, ListMatrGens, eStabCell, nbRepr, iRepr, EXTrenorm, eReprEXTrenorm, ComputeIntersection, FuncInsertBlockVertices, VertexCompletion, eRecInt, NewListRecConv, NewEXT, ListSetFace, eSetFace, PreListRepr, ListReturnEXT, eRecConv, eRecConvIns, eSelect, eVol1, eVol2, EXTtotal;
  if Length(eCase.ListRepresentent)=0 then
    Error("We need a non-zero number of representent");
  fi;
  Print("Beginning DoCloture operation\n");
  iRank:=eCase.iRank;
  iOrbit:=eCase.iOrbit;
  EXTtotal:=TheBound.ListOrbitByRank[iRank+2][iOrbit].EXT;
  eSelect:=ColumnReduction(EXTtotal).Select;
  rnk:=RankMat(EXTtotal)-1;
  EXTmain:=[];
  TheStab:=TheBound.ListOrbitByRank[iRank+2][iOrbit].TheStab;
  FuncInsertBlockVertices:=function(EXTblock)
    local DoUpdate, EXTall, eEXT, ListPermGens, ListMatrGens, eGen, eList;
    DoUpdate:=false;
    EXTall:=[];
    for eEXT in EXTblock
    do
      if Position(EXTall, eEXT)=fail then
        Append(EXTall, Orbit(TheStab, eEXT, OnPoints));
      fi;
    od;
    for eEXT in EXTall
    do
      if Position(EXTmain, eEXT)=fail then
        Add(EXTmain, eEXT);
      fi;
    od;
    ListPermGens:=[];
    ListMatrGens:=GeneratorsOfGroup(TheStab);
    for eGen in ListMatrGens
    do
      eList:=List(EXTmain, x->Position(EXTmain, x*eGen));
      Add(ListPermGens, PermList(eList));
    od;
    eStabPermMain:=Group(ListPermGens);
    phi:=GroupHomomorphismByImagesNC(TheStab, eStabPermMain, ListMatrGens, ListPermGens);
  end;
  FuncInsertBlockVertices(EXTtotal);
  ListListConv:=[];
  ListListConv[iRank+1]:=[rec(eSetConv:=[1..Length(EXTtotal)],
       ListAtt:=[rec(iOrbit:=iOrbit, eMat:=TheBound.IdentityElt)])];
  for jRank in Reversed([0..iRank-1])
  do
    ListListConv[jRank+1]:=[];
    FuncInsert:=function(eSetConv, eRec)
      local iRecConv, eRecConv, ePerm;
      for iRecConv in [1..Length(ListListConv[jRank+1])]
      do
        eRecConv:=ListListConv[jRank+1][iRecConv];
        ePerm:=RepresentativeAction(eStabPermMain, eSetConv, eRecConv.eSetConv, OnSets);
        if ePerm<>fail then
          Add(ListListConv[jRank+1][iRecConv].ListAtt, rec(iOrbit:=eRec.iOrbit, eMat:=eRec.eMat*PreImagesRepresentative(phi, ePerm)));
          return;          
        fi;
      od;
      Add(ListListConv[jRank+1], rec(eSetConv:=eSetConv, ListAtt:=[eRec]));
    end;
    nbOrbit:=Length(ListListConv[jRank+2]);
    for iOrbit in [1..nbOrbit]
    do
      nbAtt:=Length(ListListConv[jRank+2][iOrbit].ListAtt);
      for iAtt in [1..nbAtt]
      do
        eAtt:=ListListConv[jRank+2][iOrbit].ListAtt[iAtt];
        TheBoundary:=TheBound.ListOrbitByRank[jRank+3][eAtt.iOrbit].BoundaryImage;
        len:=Length(TheBoundary.ListIFace);
        for iL in [1..len]
        do
          iFace:=TheBoundary.ListIFace[iL];
          eElt:=TheBoundary.ListElt[iL];
          eNewElt:=eElt*eAtt.eMat;
          EXTf:=TheBound.ListOrbitByRank[jRank+2][iFace].EXT*eNewElt;
          NSP:=NullspaceMat(TransposedMat(EXTf));
          EXTface:=Filtered(EXTmain, x->First(NSP, y->y*x<>0)=fail);
          eSetConv:=Set(List(EXTface, x->Position(EXTmain, x)));
          FuncInsert(eSetConv, rec(iOrbit:=iFace, eMat:=eNewElt));
        od;
      od;
    od;
  od;
  Print("The set ListListConv has been created\n");
  IsInListSetConv:=function(iRank, eSetConv)
    local eOrbit, ePerm;
    for eOrbit in ListListConv[iRank+1]
    do
      ePerm:=RepresentativeAction(eStabPermMain, eOrbit.eSetConv, eSetConv, OnSets);
      if ePerm<>fail then
        return true;
      fi;
    od;
    return false;
  end;
  EXTmain:=[];
  for eRepr in eCase.ListRepresentent
  do
    FuncInsertBlockVertices(eRepr.EXT);
  od;
  Print("DoCloture, EXTmain created |EXTmain|=", Length(EXTmain), "\n");
  ListSets:=[];
  for eRepr in eCase.ListRepresentent
  do
    eSet:=Set(List(eRepr.EXT, x->Position(EXTmain, x)));
    O:=Orbit(eStabPermMain, eSet, OnSets);
    Append(ListSets, O);
  od;
  VertexCompletion:=function(EXTinput)
    local eRec, FAC, eList, iExt, eEXT, posA, eEXTred, pos;
    eRec:=ColumnReduction(EXTinput);
    FAC:=DualDescription(eRec.EXT);
    eList:=[];
    for iExt in [1..Length(EXTmain)]
    do
      eEXT:=EXTmain[iExt];
      posA:=First(NSP, x->x*eEXT<>0);
      if posA=fail then
        eEXTred:=eEXT{eRec.Select};
        pos:=First(FAC, x->x*eEXTred<0);
        if pos=fail then
          Add(eList, iExt);
        fi;
      fi;
    od;
    return EXTmain{eList};
  end;
  ComputeIntersection:=function(EXT1, EXT2)
    local rnk1, rnk2, rnk12, eRec, EXTred1, EXTred2, eRecRow, FAC1, FAC2, FACtot, EXTredTot, EXT1proj, EXT1redProj, EXTtot, EXTtot_f1;
    rnk1:=RankMat(EXT1);
    rnk2:=RankMat(EXT2);
    if rnk1<>rnk2 then
      return rec(reply:=fail, NewSub:=false);
    fi;
    rnk12:=RankMat(Concatenation(EXT1, EXT2));
    if rnk1<>rnk12 then
      return rec(reply:=fail);
    fi;
    if Set(EXT1)=Set(EXT2) then
      return rec(reply:=true, NewSub:=false, EXT:=EXT1);
    fi;
    eRec:=ColumnReductionExten(EXT1);
    EXTred1:=List(EXT1, x->x{eRec.Select});
    EXTred2:=List(EXT2, x->x{eRec.Select});
    FAC1:=DualDescription(EXTred1);
    FAC2:=DualDescription(EXTred2);
    FACtot:=Concatenation(FAC1, FAC2);
    EXTredTot:=DualDescription(FACtot);
    EXTtot:=EXTredTot*eRec.eMatBack;
    EXTtot_f1:=List(EXTtot, x->x/x[1]);
    return rec(reply:=true, NewSub:=true, EXT:=EXTtot_f1);
  end;
  GetFaceDecomposition:=function(EXTface, EXTref)
    local rnkFace, eSetFace, ListCand, NewListCand, ListReturn, NewListReturn, eCand, IsOK, eSetB, eSet, eSetInt;
    rnkFace:=RankMat(EXTface);
    eSetFace:=Set(List(EXTface, x->Position(EXTmain, x)));
    ListCand:=[eSetFace];
    ListReturn:=[];
    while(true)
    do
      NewListCand:=[];
      for eCand in ListCand
      do
        IsOK:=true;
        for eSet in ListSets
        do
          eRecInt:=ComputeIntersection(EXTmain{eCand}, EXTmain{eSet});
          if eRecInt.NewSub then
            IsOK:=false;
            FuncInsertBlockVertices(eRecInt.EXT);
            eSetInt:=Set(List(eRecInt.EXT, x->Position(EXTmain, x)));
            AddSet(NewListCand, eSetInt);
          fi;
        od;
        if IsOK=true then
          Add(ListReturn, eCand);
        fi;
      od;
      if Length(NewListCand)=0 then
        break;
      fi;
      ListCand:=ShallowCopy(NewListCand);
    od;
#    Print("ListReturn=", ListReturn, "\n");
    NewListReturn:=[];
    for eSet in ListReturn
    do
      eSetB:=Set(EXTmain{eSet});
      Add(NewListReturn, eSetB);
    od;
#    Print("NewListReturn=", NewListReturn, "\n");
    return NewListReturn;
  end;
  PreListRepr:=[];
  nbRepr:=Length(eCase.ListRepresentent);
  for iRepr in [1..nbRepr]
  do
    Print("DoCloture iRepr=", iRepr, "/", nbRepr, "\n");
    eRepr:=eCase.ListRepresentent[iRepr];
    if TestForRepetition(eRepr.EXT)=true then
      Print("The array eRepr.EXT has some repetition\n");
      Print("and this is not allowed in DoClotureOperation\n");
      Error("Please correct");
    fi;
    EXTirred:=RemoveRedundancyByDualDescription(eRepr.EXT);
    eSetIrred:=Set(List(EXTirred, x->Position(EXTmain, x)));
    if Position(eSetIrred, fail)<>fail then
      Error("Please debug from that point");
    fi;
    eStabCell:=Stabilizer(eStabPermMain, eSetIrred, OnSets);
    if Length(Set(eSetIrred))<>Length(eSetIrred) then
      Error("2: Incorrection in the code");
    fi;
    SecondGRP:=SecondReduceGroupAction(eStabCell, eSetIrred);
    eRecBound:=BoundaryOperatorsCellularDecompositionPolytope(SecondGRP, EXTirred, iRank-1);
    ListRecConv:=[];
    for jRank in [1..iRank]
    do
      Print("jRank=", jRank, "/", iRank, "\n");
      nbOrbit:=Length(eRecBound.ListOrbitByRank[jRank+2]);
      for jOrbit in [1..nbOrbit]
      do
        EXTface:=EXTirred{eRecBound.ListOrbitByRank[jRank+2][jOrbit].eSet};
        NSP:=NullspaceMat(TransposedMat(EXTface));
        EXTfaceTotal:=Filtered(eRepr.EXT, x->First(NSP, y->y*x<>0)=fail);
        rnkFace:=RankMat(EXTfaceTotal)-1;
        if IsSubset(Set(EXTtotal), Set(EXTfaceTotal))=false then
          IsNewFace:=true;
        else
          eSetConv:=Set(List(EXTfaceTotal, x->Position(EXTtotal, x)));
          test:=IsInListSetConv(rnkFace, eSetConv);
          if test=true then
            IsNewFace:=false;
          else
            IsNewFace:=true;
          fi;
        fi;
        if IsNewFace=true then
          eSetConvB:=Set(List(EXTfaceTotal, x->Position(eRepr.EXT, x)));
          ListReturnEXT:=GetFaceDecomposition(EXTfaceTotal, eRepr.EXT);
          if Length(ListReturnEXT)>1 then
            Add(ListRecConv, rec(EXTfaceTotal:=EXTfaceTotal, ListEXT:=ListReturnEXT));
          fi;
        fi;
      od;
    od;
    Add(PreListRepr, rec(EXT:=eRepr.EXT, ListRecConv:=ListRecConv));
  od;
  Print("DoCloture_NextGeneration finished\n");
  NewListRepr:=[];
  for eRepr in PreListRepr
  do
    NewEXT:=VertexCompletion(eRepr.EXT);
    eVol1:=VolumeComputationPolytope(List(eRepr.EXT, x->x{eSelect}));
    eVol2:=VolumeComputationPolytope(List(NewEXT, x->x{eSelect}));
    if eVol1<>eVol2 then
      Error("We have error in the volume");
    fi;
    NewListRecConv:=[];
    for eRecConv in eRepr.ListRecConv
    do
      eSetFace:=Set(List(eRecConv.EXTfaceTotal, x->Position(NewEXT, x)));
      ListSetFace:=List(eRecConv.ListEXT, x->Set(List(x, y->Position(NewEXT, y))));
      Add(NewListRecConv, rec(eSetConv:=eSetFace, ListSets:=ListSetFace));
    od;
    Add(NewListRepr, rec(EXT:=NewEXT, ListRecConv:=NewListRecConv));
  od;
  return rec(iRank:=eCase.iRank, iOrbit:=eCase.iOrbit, ListRepresentent:=NewListRepr);
end;

#
# The code below is deeply wrong for several reasons:
# ---There is the puzzle thing AND the ListDecompose while
#    it is clear that they describe the same geometric object.
# ---When the puzzle is actually a covering, then things stop
#    working correctly.
# ---Overly complex code.
# The right code
PolyhedralTesselationDecomposeCells:=function(eRecordTessel, eRecIAI, ListCellDecompose)
  local ListGens, FunctionFaceDecomposition, ListListEXT, ListListFAC, ListListPermGRP, ListDecomposition, IsFinished, iCase, ListStatusInsert, eRec, pos, ListCellChanges, iRank, eBound, jOrbit, iOrbit, nbCase, eCase, ListEXT, ListFAC, GRPperm, TotalListBoundary, eRecDecomp, eStabPerm, EXT, eList, ListPermGens, ListMatrGens, ListBoundInfo, TheActionFace, eStabBig, FAC, eRepr, eSelect, eNewList, TheStab, eGen, eStab, TestIsomorphism, NewListCells, eNewRec, TheDimension, nbOrbit, ListPermGRP, FuncInsertInList, phi, eRecIns, eFaceNew, TheRotSub, eRecF, nbRepr, iRepr, eNewBound, FuncSignatureDet, NewListOrbitByRank, NewListElt, NewListSign, NewListIFace, eSign, fSign, eElt, iFace, eOrigin, eNature, ListListListListRecIns, ListListListRecIns, ListListRecIns, ListRecIns, iBound, nbBound, SetEXT, eFaceIrr, ListDecompositionCell, IsFacePuzzle, ListListPhi, ListPhi, lenBound, ListOccuringCoefficients, eMulSign, eAddElt, ListElementM2, iBoundB, TheBoundary, iOrbitAsk, ListSetsM2, eSet, EXTimage, iFaceM2, eEltM2, lenBoundB, iFaceM1, eEltB, eProd, posChg, ListPuzzleFaceInclusion, lenB, iB, iOrbitB, GetPositionOld, eRecChg, eBoundOld, len, EXTn, eEltN, iOrbitN, PuzzleDatabaseUpdate, FuncInsertPiecePuzzle, posChg2, iL, nbOldOrbit, iRankBis, iOrbitBis, nbOrbitBis, iCaseOrig, iReprOrig, iRankOrig, iOrbitOrig, ListListPhiNew, ListPhiNew, ePosOld, ThePermStab, ePerm, iOrbitOld, GetStabilizerAndRotation, EXTpuzzle, EXTmain, GetLinearMerge, ListLinearDecomposition, TheFindInLinearMerge, eRecBound, Ofac, ListDebugInfo, DebugEXT, eEXTspec, DebugListIBound, DebugListSets, DebugListSetsAtt, DebugGRP, DebugEXT2, DebugGRP2, DebugRecBound, EXTdiff, eSetDiff, EXTimageB, DebugListEXTM1, DebugGRA, eIntEXT, i, j, DebugListSetsByBound, DebugSetsByBound, DebugListListEXTimage, DebugListEXTimage, eIntSet, DebugListListAdjSet, DebugListAdjSet, MainRecOrigin;
  TheActionFace:=function(x, g)
    return Set(x*g);
  end;
  ListListPermGRP:=[];
  ListListPhi:=[];
  TheDimension:=Length(eRecordTessel.ListOrbitByRank)-2;
  Print("TheDimension=", TheDimension, "\n");
  for iRank in [0..TheDimension]
  do
    nbOrbit:=Length(eRecordTessel.ListOrbitByRank[iRank+2]);
    ListPermGRP:=[];
    ListPhi:=[];
    for iOrbit in [1..nbOrbit]
    do
      EXT:=eRecordTessel.ListOrbitByRank[iRank+2][iOrbit].EXT;
      if TestForRepetition(EXT)=true then
        Print("We have some repetition in EXT\n");
        Print("In the input eRecordTessel, with more clearly\n");
        Print("This is for iRank=", iRank, " iOrbit=", iOrbit, "\n");
        Error("Clearly a bug");
      fi;
      ListPermGens:=[];
      TheStab:=eRecordTessel.ListOrbitByRank[iRank+2][iOrbit].TheStab;
      ListMatrGens:=GeneratorsOfGroup(TheStab);
      for eGen in ListMatrGens
      do
        eList:=List(EXT, x->Position(EXT, x*eGen));
        Add(ListPermGens, PermList(eList));
      od;
      GRPperm:=PersoGroupPerm(ListPermGens);
      phi:=GroupHomomorphismByImagesNC(TheStab, GRPperm, ListMatrGens, ListPermGens);
      Add(ListPhi, phi);
      Add(ListPermGRP, GRPperm);
    od;
    Add(ListListPermGRP, ListPermGRP);
    Add(ListListPhi, ListPhi);
  od;
  ListCellChanges:=[];
  ListStatusInsert:=[];
  for eCase in ListCellDecompose
  do
    iRank:=eCase.iRank;
    iOrbit:=eCase.iOrbit;
    eRec:=rec(iRank:=iRank, iOrbit:=iOrbit);
    Add(ListCellChanges, eRec);
    Add(ListStatusInsert, 0);
  od;
  if Length(Set(ListCellChanges))<>Length(ListCellChanges) then
    Error("Inconsistency in your input");
  fi;
  while(true)
  do
    IsFinished:=true;
    nbCase:=Length(ListCellChanges);
    for iCase in [1..nbCase]
    do
      if ListStatusInsert[iCase]=0 then
        IsFinished:=false;
        ListStatusInsert[iCase]:=1;
        iRank:=ListCellChanges[iCase].iRank;
        iOrbit:=ListCellChanges[iCase].iOrbit;
        if iRank>=1 then
          eBound:=eRecordTessel.ListOrbitByRank[iRank+2][iOrbit].BoundaryImage;
          for jOrbit in eBound.ListIFace
          do
            eRec:=rec(iRank:=iRank-1, iOrbit:=jOrbit);
            pos:=Position(ListCellChanges, eRec);
            if pos=fail then
              Add(ListCellChanges, eRec);
              Add(ListStatusInsert, 0);
            fi;
          od;
        fi;
      fi;
    od;
    if IsFinished=true then
      break;
    fi;
  od;
  Print("ListCellChanges determined\n");
  NewListOrbitByRank:=[];
  eFaceIrr:=rec(EXT:=[], TheStab:="irrelevant", BoundaryImage:="irrelevant", TheDel:="irrelevant");
  NewListOrbitByRank[1]:=[eFaceIrr];
  for iRank in [0..TheDimension]
  do
    nbOrbit:=Length(eRecordTessel.ListOrbitByRank[iRank+2]);
    eNewList:=[];
    nbOldOrbit:=0;
    for iOrbit in [1..nbOrbit]
    do
      eRec:=rec(iRank:=iRank, iOrbit:=iOrbit);
      pos:=Position(ListCellChanges, eRec);
      if pos=fail then
        EXT:=eRecordTessel.ListOrbitByRank[iRank+2][iOrbit].EXT;
        TheStab:=eRecordTessel.ListOrbitByRank[iRank+2][iOrbit].TheStab;
        TheRotSub:=eRecordTessel.ListOrbitByRank[iRank+2][iOrbit].RotationSubgroup;
        eNewRec:=rec(TheStab:=TheStab, RotationSubgroup:=TheRotSub, eNature:="old", eOrigin:=[iRank, iOrbit]);
#        Print("iRank=", iRank, " iOrbit=", iOrbit, " |stab|=", Order(TheStab), "\n");
        if iRank=0 then
          eNewRec.EXT:=EXT;
        fi;
        Add(eNewList, eNewRec);
        nbOldOrbit:=nbOldOrbit+1;
      fi;
    od;
    NewListOrbitByRank[iRank+2]:=eNewList;
#    Print("iRank=", iRank, " nbOldOrbit=", nbOldOrbit, "\n");
  od;
  GetPositionOld:=function(iRank, iOrbit)
    local len, i;
    len:=Length(NewListOrbitByRank[iRank+2]);
    for i in [1..len]
    do
      if NewListOrbitByRank[iRank+2][i].eOrigin=[iRank, iOrbit] then
        return i;
      fi;
    od;
    Error("We fail to find the position in GetPositionOld");
  end;
  GetStabilizerAndRotation:=function(EXT)
    local eSumEXT, TheStab, TheRed, TheBasis, ListMatrGens, ListPermGens, TheSym2, eGen, eMat, eEXT, eDet, FuncInsertGenerator, eElt, ePerm, eRotSubgroup, TheSubgroup;
    eSumEXT:=Sum(EXT);
    TheStab:=eRecIAI.FuncAutomorphism(eSumEXT);
    ListMatrGens:=[];
    TheSubgroup:=Group([eRecordTessel.IdentityElt]);
    FuncInsertGenerator:=function(eElt)
      local pos;
      pos:=First(EXT*eElt, x->Position(EXT, x)=fail);
      if pos=fail then
        if eElt in TheSubgroup then
          return;
        fi;
        Add(ListMatrGens, eElt);
        TheSubgroup:=Group(ListMatrGens);
      fi;
    end;
    for eElt in TheStab
    do
      FuncInsertGenerator(eElt);
    od;
    #
    TheRed:=RowReduction(EXT);
    TheBasis:=TheRed.EXT;
    ListPermGens:=[];
    TheSym2:=SymmetricGroup(2);
    for eGen in ListMatrGens
    do
      eMat:=[];
      for eEXT in TheBasis
      do
        Add(eMat, SolutionMat(TheBasis, eEXT*eGen));
      od;
      eDet:=DeterminantMat(eMat);
      if eDet=1 then
        ePerm:=();
      else
        ePerm:=(1,2);
      fi;
      Add(ListPermGens, ePerm);
    od;
    eRotSubgroup:=GetKernelOfMapping(TheSubgroup, TheSym2, ListMatrGens, ListPermGens);
    return rec(TheStab:=TheSubgroup, RotationSubgroup:=eRotSubgroup);
  end;
  TestIsomorphism:=function(eFace1, eFace2)
    local eSumEXT1, eSumEXT2, testIso, eElt, eProd, pos;
    eSumEXT1:=Sum(eFace1.EXT);
    eSumEXT2:=Sum(eFace2.EXT);
    testIso:=eRecIAI.FuncIsomorphism(eSumEXT1, eSumEXT2);
    if testIso=fail then
      return fail;
    fi;
    for eElt in eFace1.TheStab
    do
      eProd:=eElt*testIso;
      pos:=First(eFace1.EXT*eProd, x->Position(eFace2.EXT, x)=fail);
      if pos=fail then
        return eProd;
      fi;
    od;
    return fail;
  end;
  GetLinearMerge:=function(iRank, iOrbit)
    local ListListMerges, EXT, ePermStab, phi, jRank, ListFaceStab, FuncInsertFace, TheNewList, eStabFaceConv, eRecIns, eRecChg, posChg, iEnt, nbEnt, eEXT, EXTproj, FACproj, eSelect;
    ListListMerges:=[];
    EXT:=eRecordTessel.ListOrbitByRank[iRank+2][iOrbit].EXT;
    eSelect:=ColumnReduction(EXT).Select;
    EXTproj:=List(EXT, x->x{eSelect});
    FACproj:=DualDescription(EXTproj);
    ePermStab:=ListListPermGRP[iRank+1][iOrbit];
    phi:=ListListPhi[iRank+1][iOrbit];
    eRecChg:=rec(iRank:=iRank, iOrbit:=iOrbit);
    posChg:=Position(ListCellChanges, eRecChg);
    for jRank in [0..iRank]
    do
      TheNewList:=[];
      ListFaceStab:=[];
      FuncInsertFace:=function(eNewRec)
        local iOrbit, eRec, testPerm, testMatr, eSetImg, eRecOrbit, len, iL, eElt, EXTface, ListEXT, ListElt, ListIOrbitOld;
        for iOrbit in [1..Length(TheNewList)]
        do
          eRec:=TheNewList[iOrbit];
          testPerm:=RepresentativeAction(ePermStab, eNewRec.eSetConv, eRec.eSetConv, OnSets);
          if testPerm<>fail then
            testMatr:=PreImagesRepresentative(phi, testPerm);
            eSetImg:=OnSets(eNewRec.eSet, testPerm);
            eRecOrbit:=OrbitWithAction(ListFaceStab[iOrbit], eSetImg, OnSets);
            len:=Length(eRecOrbit.ListElement);
            for iL in [1..len]
            do
              eElt:=eNewRec.eElt*testMatr*PreImagesRepresentative(phi, eRecOrbit.ListElement[iL]);
              EXTface:=EXT{eRecOrbit.ListCoset[iL]};
              for eEXT in EXTface
              do
                if First(FACproj, x->x*eEXT{eSelect}<0)<>fail then
                  Error("Non correct vertex");
                fi;
              od;
              Add(TheNewList[iOrbit].ListEXT, EXTface);
              Add(TheNewList[iOrbit].ListElt, eElt);
              Add(TheNewList[iOrbit].ListIOrbitOld, eNewRec.iOrbit);
            od;
            return;
          fi;
        od;
        eStabFaceConv:=Stabilizer(ePermStab, eNewRec.eSetConv, OnSets);
        Add(ListFaceStab, eStabFaceConv);
        eRecOrbit:=OrbitWithAction(eStabFaceConv, eNewRec.eSet, OnSets);
        len:=Length(eRecOrbit.ListElement);
        ListEXT:=[];
        ListElt:=[];
        ListIOrbitOld:=[];
        for iL in [1..len]
        do
          eElt:=eNewRec.eElt*PreImagesRepresentative(phi, eRecOrbit.ListElement[iL]);
          EXTface:=EXT{eRecOrbit.ListCoset[iL]};
          Add(ListEXT, EXTface);
          Add(ListElt, eElt);
          Add(ListIOrbitOld, eNewRec.iOrbit);
        od;
        eRecIns:=rec(eSetConv:=eNewRec.eSetConv, 
                     ListEXT:=ListEXT, 
                     ListElt:=ListElt, 
                     ListIOrbitOld:=ListIOrbitOld);
        Add(TheNewList, eRecIns);
      end;
      nbOrbit:=Length(ListDecompositionCell[posChg][jRank+1]);
      for iOrbit in [1..nbOrbit]
      do
        eRecIns:=ListDecompositionCell[posChg][jRank+1][iOrbit];
        FuncInsertFace(eRecIns);
      od;
      for iOrbit in [1..Length(TheNewList)]
      do
        nbEnt:=Length(TheNewList[iOrbit].ListEXT);
        for iEnt in [1..nbEnt]
        do
          if Set(TheNewList[iOrbit].ListEXT[iEnt])<>Set(eRecordTessel.ListOrbitByRank[jRank+2][TheNewList[iOrbit].ListIOrbitOld[iEnt]].EXT*TheNewList[iOrbit].ListElt[iEnt]) then
            Error("Bookkeeping error");
          fi;
        od;
      od;
      Add(ListListMerges, TheNewList);
    od;
    return ListListMerges;
  end;
  TheFindInLinearMerge:=function(EXT, iRank, iOrbit)
    local ListBoundary, NSP, EXTface, eSetConv, eRecChg, posChg, eCase, testPerm, testMatr, ListEXTdecompo, eSelect, EXTproj, FACproj, eStabPerm, phi, EXTinProj, FACinProj, FACint, EXTint, O, iRankTarget, EXTinImg, EXTin, iL, len, ListEltDecompo, ListIOrbitOldDecompo, ListSelect, EXTinProjIrred, IsCorrect, ePerm, iCase, GRPperm, ListPermGens, ListNature, FACsel, eSetConvTotal, EXTfaceSelProj, eSelectFace, EXTfacePROJ, FACfacePROJ, eEXT, DoCheck, SumVol, TotVol;
    NSP:=NullspaceMat(TransposedMat(EXT));
    Print("|EXT|=", Length(EXT), " |EXT[1]|=", Length(EXT[1]), "\n");
    eSelect:=ColumnReduction(EXT).Select;
    DoCheck:=true;
    if DoCheck then
      TotVol:=VolumeComputationPolytope(List(EXT, x->x{eSelect}));
    fi;
    if Length(EXT)<>Length(Set(EXT)) then
      Error("Input has some repetition, illegal of course");
    fi;
    if SearchPositiveRelationSimple(EXT)<>false then
      Error("Apparently, we are not dealing with a polytope");
    fi;
    EXTface:=eRecordTessel.ListOrbitByRank[iRank+2][iOrbit].EXT;
    eSelectFace:=ColumnReduction(EXTface).Select;
    EXTfacePROJ:=List(EXTface, x->x{eSelectFace});
    FACfacePROJ:=DualDescription(EXTfacePROJ);
    for eEXT in EXT
    do
      if First(FACfacePROJ, x->x*eEXT{eSelectFace}<0)<>fail then
        Error("We have a wrong vertex");
      fi;
    od;
    EXTproj:=List(EXT, x->x{eSelect});
    FACproj:=DualDescription(EXTproj);
    eStabPerm:=ListListPermGRP[iRank+1][iOrbit];
    phi:=ListListPhi[iRank+1][iOrbit];
    iRankTarget:=RankMat(EXT)-1;
    Print("EXTface=", Length(EXTface), "\n");
    eSetConv:=Filtered([1..Length(EXTface)], x->First(NSP, y->y*EXTface[x]<>0)=fail);
    EXTfaceSelProj:=List(EXTface{eSetConv}, x->x{eSelect});
    FACsel:=Filtered(FACproj, x->First(EXTfaceSelProj, y->y*x<>0)=fail);
    eSetConvTotal:=eSetConv{Filtered([1..Length(eSetConv)], x->First(FACsel, y->y*EXTfaceSelProj[x]<>0)=fail)};
    eRecChg:=rec(iRank:=iRank, iOrbit:=iOrbit);
    posChg:=Position(ListCellChanges, eRecChg);
    if posChg=fail then
      Error("Please debug from here posChg");
    fi;
    Print("eSetConv=", eSetConv, " eSetConvTotal=", eSetConvTotal, "\n");
    if eSetConv<>eSetConvTotal then
      Print("We are in Case 1\n");
      return rec(ListEXT:=[EXT],
                 ListNature:=["new"],
                 ListElt:=["irrelevant"],
                 ListIOrbitOld:=["irrelevant"]);
    fi;
    for iCase in [1..Length(ListLinearDecomposition[posChg][iRankTarget+1])]
    do
      eCase:=ListLinearDecomposition[posChg][iRankTarget+1][iCase];
      testPerm:=RepresentativeAction(eStabPerm, eCase.eSetConv, eSetConv, OnSets);
      if testPerm<>fail then
        testMatr:=PreImagesRepresentative(phi, testPerm);
        ListEXTdecompo:=[];
        ListEltDecompo:=[];
        ListIOrbitOldDecompo:=[];
        ListNature:=[];
        len:=Length(eCase.ListEXT);
        IsCorrect:=true;
        for iL in [1..len]
        do
          Print("iL=", iL, "/", len, "\n");
          EXTin:=eCase.ListEXT[iL];
          EXTinImg:=EXTin*testMatr;
          EXTinProj:=List(EXTinImg, x->x{eSelect});
          FACinProj:=DualDescription(EXTinProj);
          EXTinProjIrred:=DualDescription(FACinProj);
          FACint:=Concatenation(FACinProj, FACproj);
          if SearchPositiveRelationSimple(FACint)=false then
            EXTint:=DualDescription(FACint);
            if RankMat(EXTint)=iRankTarget+1 then
              if Set(EXTinProjIrred)<>Set(EXTint) then
                IsCorrect:=false;
              fi;
              Add(ListEXTdecompo, Set(EXTinImg));
              Add(ListEltDecompo, eCase.ListElt[iL]*testMatr);
              Add(ListIOrbitOldDecompo, eCase.ListIOrbitOld[iL]);
              Add(ListNature, "old");
            fi;
          fi;
        od;
        if IsCorrect=true then
          Print("We are in Case 2\n");
          if DoCheck then
            SumVol:=Sum(List(ListEXTdecompo, x->VolumeComputationPolytope(List(x, y->y{eSelect}))));
            Print(" SumVol=", SumVol, " TotVol=", TotVol, "\n");
            if SumVol<>TotVol then
              Error("The volume error is just the beginning");
            fi;
          fi;
          return rec(ListEXT:=ListEXTdecompo,
                     ListNature:=ListNature,
                     ListElt:=ListEltDecompo,
                     ListIOrbitOld:=ListIOrbitOldDecompo);
        fi;
      fi;
    od;
    Print("We are in Case 3\n");
    return rec(ListEXT:=[EXT],
               ListNature:=["new"],
               ListElt:=["irrelevant"],
               ListIOrbitOld:=["irrelevant"]);
  end;
  ListDecompositionCell:=[];
  ListPuzzleFaceInclusion:=[];
  for eRec in ListCellChanges
  do
#    Print("Computing orbit subfaces for iRank=", eRec.iRank, " iOrbit=", eRec.iOrbit, "\n");
    Add(ListDecompositionCell, GetCollectionSubfaces(eRecordTessel, eRec.iRank, eRec.iOrbit));
    Add(ListPuzzleFaceInclusion, rec(EXT:=[], ListRecOrigin:=[], ListNewIOrbit:=[], ListNewElt:=[], ListNewEXT:=[]));
  od;
  ListLinearDecomposition:=[];
  for eRec in ListCellChanges
  do
    Add(ListLinearDecomposition, GetLinearMerge(eRec.iRank, eRec.iOrbit));
  od;
  FuncInsertInList:=function(eFaceNew, iRank)
    local iOrbit, nbOrbit, testIso, eRecStab, NewFace;
    nbOrbit:=Length(NewListOrbitByRank[iRank+2]);
    for iOrbit in [1..nbOrbit]
    do
      if NewListOrbitByRank[iRank+2][iOrbit].eNature="new" then
        testIso:=TestIsomorphism(NewListOrbitByRank[iRank+2][iOrbit], eFaceNew);
        if testIso<>fail then
          return rec(iOrbit:=iOrbit, IsNew:=false, eMap:=testIso);
        fi;
      fi;
    od;
    eRecStab:=GetStabilizerAndRotation(eFaceNew.EXT);
    NewFace:=rec(iRank:=eFaceNew.iRank,
                 EXT:=eFaceNew.EXT,
                 eNature:=eFaceNew.eNature,
                 eOrigin:=eFaceNew.eOrigin,
                 TheStab:=eRecStab.TheStab,
                 RotationSubgroup:=eRecStab.RotationSubgroup);
    Add(NewListOrbitByRank[iRank+2], NewFace);
    return rec(iOrbit:=nbOrbit+1, IsNew:=true, eMap:=eRecordTessel.IdentityElt);
  end;
  # we need to determine if eFaceNew is part of the puzzle of a face
  # and resolve the puzzle later on.
  # 
  IsFacePuzzle:=function(EXTbig, EXTsmall)
    local FACbig, eEXT, pos;
    FACbig:=DualDescription(EXTbig);
    for eEXT in EXTsmall
    do
      pos:=First(FACbig, x->x*eEXT<0);
      if pos<>fail then
        return false;
      fi;
    od;
    return true;
  end;
  FuncInsertPiecePuzzle:=function(posChg, eRecOrigin, EXTn, iOrbitN, eEltN)
    local len, SetEXT, i;
    len:=Length(ListPuzzleFaceInclusion[posChg].ListNewIOrbit);
    SetEXT:=Set(EXTn);
    for i in [1..len]
    do
      if SetEXT=ListPuzzleFaceInclusion[posChg].ListNewEXT[i] then
        return;
      fi;
    od;
    Add(ListPuzzleFaceInclusion[posChg].ListNewIOrbit, iOrbitN);
    Add(ListPuzzleFaceInclusion[posChg].ListRecOrigin, eRecOrigin);
    Add(ListPuzzleFaceInclusion[posChg].ListNewEXT, SetEXT);
    Add(ListPuzzleFaceInclusion[posChg].ListNewElt, eEltN);
    ListPuzzleFaceInclusion[posChg].EXT:=Union(ListPuzzleFaceInclusion[posChg].EXT, SetEXT);
    eRecChg:=ListCellChanges[posChg];
    Print("Now iRank=", eRecChg.iRank, " iOrbit=", eRecChg.iOrbit, " |ListPuzzleFaceInclusion|=", Length(ListPuzzleFaceInclusion[posChg].ListNewIOrbit), " |EXT|=", Length(ListPuzzleFaceInclusion[posChg].EXT), "\n");
  end;
  PuzzleDatabaseUpdate:=function(eFaceNew, MainRecOrigin, eRecIns, iRank, iOrbit)
    local rnk, iRankTarget, posChg, eRecChg, eSetConv, EXTnull,  NSP, testPuzzle, ePermStab, eStabBperm, eStabBmatr, eStabCperm, eStabCmatr, ListImages, ListIOrbit, ListElement, SetEXTsub, phi, eRecOrbitC, eRecOrbitB, lenOrbC, lenOrb, iOrbC, eSet, SetEXTproj, len, ePerm, iOrb, eProd, eProdInv, testMatr, testPerm, posChg2, eRecChg2, EXTred, SetEXT, EXT, eRecOrigin;
    iRankTarget:=eFaceNew.iRank;
    EXT:=eRecordTessel.ListOrbitByRank[iRank+2][iOrbit].EXT;
    NSP:=NullspaceMat(TransposedMat(eFaceNew.EXT));
    eSelect:=ColumnReduction(eFaceNew.EXT).Select;
    EXTred:=List(eFaceNew.EXT, x->x{eSelect});
    SetEXTsub:=Set(eFaceNew.EXT);
    EXTnull:=Filtered(EXT, x->First(NSP, y->y*x<>0)=fail);
    eSetConv:=Set(List(EXTnull, x->Position(EXT, x)));
    ePermStab:=ListListPermGRP[iRank+1][iOrbit];
    phi:=ListListPhi[iRank+1][iOrbit];
    eRecChg:=rec(iRank:=iRank, iOrbit:=iOrbit);
    posChg:=Position(ListCellChanges, eRecChg);
    for eRec in ListDecompositionCell[posChg][iRankTarget+1]
    do
      testPerm:=RepresentativeAction(ePermStab, eRec.eSetConv, eSetConv, OnSets);
      if testPerm<>fail then
        testMatr:=PreImagesRepresentative(phi, testPerm);
        eStabBperm:=Stabilizer(ePermStab, eSetConv, OnSets);
        eStabBmatr:=PreImage(phi, eStabBperm);
        SetEXT:=Set(EXT{eRec.eSet}*testMatr);
        eRecOrbitB:=OrbitWithAction(eStabBmatr, SetEXT, TheActionFace);
        lenOrb:=Length(eRecOrbitB.ListCoset);
        for iOrb in [1..lenOrb]
        do
          SetEXTproj:=List(eRecOrbitB.ListCoset[iOrb], x->x{eSelect});
          testPuzzle:=IsFacePuzzle(SetEXTproj, EXTred);
          if testPuzzle=true then
            eRecChg2:=rec(iRank:=iRankTarget, iOrbit:=eRec.iOrbit);
            posChg2:=Position(ListCellChanges, eRecChg2);
            eSet:=Set(List(eRecOrbitB.ListCoset[iOrb], x->Position(EXT, x)));
            eStabCperm:=Stabilizer(eStabBperm, eSet, OnSets);
            eStabCmatr:=PreImage(phi, eStabCperm);
            eRecOrbitC:=OrbitWithAction(eStabCmatr, SetEXTsub, TheActionFace);
            lenOrbC:=Length(eRecOrbitC.ListCoset);
            iOrbitN:=eRecIns.iOrbit;
            eProd:=eRec.eElt*testMatr*eRecOrbitB.ListElement[iOrb];
            eProdInv:=Inverse(eProd);
            for iOrbC in [1..lenOrbC]
            do
              eEltN:=eRecOrbitC.ListElement[iOrbC]*eProdInv;
              EXTn:=eFaceNew.EXT*eEltN;
              eRecOrigin:=rec(iRepr:=MainRecOrigin.iRepr, 
                              iOrbC:=iOrbC, posChg:=posChg);
              FuncInsertPiecePuzzle(posChg2, eRecOrigin, EXTn, iOrbitN, eEltN);
            od;
            return;
          fi;
        od;
      fi;
    od;
  end;
  ListDecomposition:=[];
  TotalListBoundary:=[];
  nbCase:=Length(ListCellDecompose);
  ListListListListRecIns:=[];
  ListListPhiNew:=[];
  for iCase in [1..nbCase]
  do
    Print("iCase=", iCase, "/", nbCase, "\n");
    eCase:=ListCellDecompose[iCase];
    CheckDecomposition(eRecordTessel, eCase);
    iRank:=eCase.iRank;
    iOrbit:=eCase.iOrbit;
    ListBoundInfo:=[];
    nbRepr:=Length(eCase.ListRepresentent);
    ListListListRecIns:=[];
    ListPhiNew:=[];
    for iRepr in [1..nbRepr]
    do
      Print("  iRepr=", iRepr, "/", nbRepr, "\n");
      eRepr:=eCase.ListRepresentent[iRepr];
      Print("FaceLattComp, EXT=", eRepr.EXT, "\n");
      eStabBig:=eRecordTessel.ListOrbitByRank[iRank+2][iOrbit].TheStab;
      eStab:=Stabilizer(eStabBig, Set(eRepr.EXT), TheActionFace);
      ListPermGens:=[];
      ListGens:=GeneratorsOfGroup(eStab);
      for eGen in ListGens
      do
        eList:=List(eRepr.EXT, x->Position(eRepr.EXT, x*eGen));
        Add(ListPermGens, PermList(eList));
      od;
      eStabPerm:=PersoGroupPerm(ListPermGens);
      phi:=GroupHomomorphismByImagesNC(eStab, eStabPerm, ListGens, ListPermGens);
      Add(ListPhiNew, phi);
      Print("|eStabBig|=", Order(eStabBig), " |eStab|=", Order(eStab), "\n");
      FunctionFaceDecomposition:=function(EXTinp)
        local eSetConv, eRecConv, testPerm, NewListEXT, eSet, eSetImg, NewListElt, NewListNature, NewListIOrbitOld, eSelect, DoCheck, SumVol, TotVol;
        eSetConv:=Set(List(EXTinp, x->Position(eRepr.EXT,x)));
        eSelect:=ColumnReduction(EXTinp).Select;
        DoCheck:=true;
        if DoCheck then
          TotVol:=VolumeComputationPolytope(List(EXTinp, x->x{eSelect}));
        fi;
        for eRecConv in eRepr.ListRecConv
        do
          testPerm:=RepresentativeAction(eStabPerm, eRecConv.eSetConv, eSetConv, OnSets);
          if testPerm<>fail then
            NewListEXT:=[];
            NewListElt:=[];
            NewListNature:=[];
            NewListIOrbitOld:=[];
            SumVol:=0;
            for eSet in eRecConv.ListSets
            do
              eSetImg:=OnSets(eSet, testPerm);
              if DoCheck then
                SumVol:=SumVol + VolumeComputationPolytope(List(eRepr.EXT{eSetImg}, x->x{eSelect}));
              fi;
              Add(NewListEXT, eRepr.EXT{eSetImg});
              Add(NewListElt, "irrelevant");
              Add(NewListNature, "new");
              Add(NewListIOrbitOld, "irrelevant");
            od;
            if DoCheck then
              Print("SumVol=", SumVol, " TotVol=", TotVol, "\n");
              if SumVol<>TotVol then
                Error("Error in the volume considered");
              fi;
            fi;
            return rec(ListEXT:=NewListEXT,
                       ListElt:=NewListElt, 
                       ListNature:=NewListNature, 
                       ListIOrbitOld:=NewListIOrbitOld);
          fi;
        od;
        return TheFindInLinearMerge(EXTinp, iRank, iOrbit);
      end;
      if Length(eRepr.EXT)<>Length(Set(eRepr.EXT)) then
        Error("We have repetition in eRepr.EXT");
      fi;
      eRecDecomp:=GetCompleteAndTotalDecomposition(eRepr.EXT, eStabPerm, FunctionFaceDecomposition, eRecordTessel);
      ListListRecIns:=[];
      for iRankBis in [0..eRecDecomp.rnk]
      do
        nbOrbitBis:=Length(eRecDecomp.ListOrbitByRank[iRankBis+2]);
        ListRecIns:=[];
        for iOrbitBis in [1..nbOrbitBis]
        do
          eRecF:=eRecDecomp.ListOrbitByRank[iRankBis+2][iOrbitBis];
          eFaceNew:=rec(iRank:=iRankBis, EXT:=eRepr.EXT{eRecF.eSet}, eNature:="new", eOrigin:=[iCase, iRepr, iRankBis, iOrbitBis]);
          eRecIns:=FuncInsertInList(eFaceNew, iRankBis);
          if Length(eFaceNew.EXT)=1 then
            Print("             EXT=", eFaceNew.EXT, "\n");
          fi;
          if eRecIns.IsNew=true then
            MainRecOrigin:=rec(iRepr:=iRepr, iRank:=iRank, iOrbit:=iOrbit);
            PuzzleDatabaseUpdate(eFaceNew, MainRecOrigin, eRecIns, iRank, iOrbit);
          fi;
          Add(ListRecIns, eRecIns);
        od;
        Add(ListListRecIns, ListRecIns);
      od;
      Add(ListBoundInfo, eRecDecomp);
      Add(ListListListRecIns, ListListRecIns);
    od;
    Add(TotalListBoundary, ListBoundInfo);
    Add(ListListListListRecIns, ListListListRecIns);
    Add(ListListPhiNew, ListPhiNew);
  od;
  FuncSignatureDet:=function(iRank, iOrbit, eElt)
    if not(eElt in NewListOrbitByRank[iRank+2][iOrbit].TheStab) then
      Error("Element is not in stabilizer, this is illegal");
    fi;    
    if eElt in NewListOrbitByRank[iRank+2][iOrbit].RotationSubgroup then
      return 1;
    fi;    
    return -1;
  end;
  Print("Checking correctness by volume and covering arguments\n");
  for iRank in [0..TheDimension]
  do
    nbOrbit:=Length(eRecordTessel.ListOrbitByRank[iRank+2]);
    Print("iRank=", iRank, " nbOrbit=", nbOrbit, "\n");
    for iOrbit in [1..nbOrbit]
    do
      eRecChg:=rec(iRank:=iRank, iOrbit:=iOrbit);
      posChg:=Position(ListCellChanges, eRecChg);
      Print("iRank=", iRank, "  iOrbit=", iOrbit, " posChg=", posChg, "\n");
      if posChg<>fail then
        EXTmain:=eRecordTessel.ListOrbitByRank[iRank+2][iOrbit].EXT;
        TheStab:=eRecordTessel.ListOrbitByRank[iRank+2][iOrbit].TheStab;
        EXTpuzzle:=ListPuzzleFaceInclusion[posChg].EXT;
        ListEXT:=ListPuzzleFaceInclusion[posChg].ListNewEXT;
        Print("  |EXTpuzzle|=", Length(EXTpuzzle), " |EXTmain|=", Length(EXTmain), " |Stab|=", Order(TheStab), " |ListEXT|=", Length(ListEXT), "\n");
        if IsSubset(Set(EXTpuzzle), Set(EXTmain))=false then
          Error("The puzzle vertices do not cover the original vertices");
        fi;
        Print("Call from checking by volume and covering\n");
        CheckCellularDecomposition(EXTmain, TheStab, ListEXT);
      fi;
    od;
  od;
  Print("Now computing the differentials\n");
  for iRank in [0..TheDimension]
  do
    nbOrbit:=Length(NewListOrbitByRank[iRank+2]);
    Print("iRank=", iRank, "\n");
    if iRank=0 then
      for iOrbit in [1..nbOrbit]
      do
        eBound:=rec(ListIFace:=[1], ListSign:=[1], ListElt:=[eRecordTessel.IdentityElt]);
        NewListOrbitByRank[iRank+2][iOrbit].BoundaryImage:=eBound;
        NewListOrbitByRank[iRank+2][iOrbit].TheStabPerm:=Group(());
        Print("  iOrbit=", iOrbit, " |EXT|=", Length(NewListOrbitByRank[iRank+2][iOrbit].EXT), " |GRP|=", Order(NewListOrbitByRank[iRank+2][iOrbit].TheStab), "\n");
      od;
    else
      for iOrbit in [1..nbOrbit]
      do
        eOrigin:=NewListOrbitByRank[iRank+2][iOrbit].eOrigin;
        eNature:=NewListOrbitByRank[iRank+2][iOrbit].eNature;
        NewListIFace:=[];
        NewListElt:=[];
        if eNature="new" then
          iCaseOrig:=eOrigin[1];
          iReprOrig:=eOrigin[2];
          iRankOrig:=eOrigin[3];
          iOrbitOrig:=eOrigin[4];
          if iRankOrig<>iRank then
            Error("It is an apparent bug in ranks");
          fi;
          eRecBound:=TotalListBoundary[iCaseOrig][iReprOrig];
          EXT:=NewListOrbitByRank[iRank+2][iOrbit].EXT;
#          Print("  EXT=", EXT, "\n");
          eBound:=eRecBound.ListOrbitByRank[iRankOrig+2][iOrbitOrig].BoundaryImage;
          nbBound:=Length(eBound.ListIFace);
          for iBound in [1..nbBound]
          do
            iFace:=eBound.ListIFace[iBound];
            eElt:=eBound.ListElt[iBound];
            eRecIns:=ListListListListRecIns[iCaseOrig][iReprOrig][iRankOrig][iFace];
            Add(NewListIFace, eRecIns.iOrbit);
            Add(NewListElt, eRecIns.eMap*PreImagesRepresentative(ListListPhiNew[iCaseOrig][iReprOrig], eElt));
          od;
        else
          EXT:=[];
          iOrbitOld:=NewListOrbitByRank[iRank+2][iOrbit].eOrigin[2];
          eBoundOld:=eRecordTessel.ListOrbitByRank[iRank+2][iOrbitOld].BoundaryImage;
          len:=Length(eBoundOld.ListIFace);
          for iL in [1..len]
          do
            iOrbitB:=eBoundOld.ListIFace[iL];
            eEltB:=eBoundOld.ListElt[iL];
            eRecChg:=rec(iRank:=iRank-1, iOrbit:=iOrbitB);
            posChg:=Position(ListCellChanges, eRecChg);
            if posChg=fail then
              ePosOld:=GetPositionOld(iRank-1, iOrbitB);
              EXTimage:=Set(NewListOrbitByRank[iRank+1][ePosOld].EXT*eEltB);
              Add(NewListIFace, ePosOld);
              Add(NewListElt, eEltB);
            else
              EXTimage:=Set(ListPuzzleFaceInclusion[posChg].EXT*eEltB);
              lenB:=Length(ListPuzzleFaceInclusion[posChg].ListNewIOrbit);
              for iB in [1..lenB]
              do
                eProd:=ListPuzzleFaceInclusion[posChg].ListNewElt[iB]*eEltB;
                Add(NewListIFace, ListPuzzleFaceInclusion[posChg].ListNewIOrbit[iB]);
                Add(NewListElt, eProd);
              od;
            fi;
            EXT:=Union(EXT, EXTimage);
          od;
          if IsSubset(EXT, Set(eRecordTessel.ListOrbitByRank[iRank+2][iOrbitOld].EXT))=false then
            Error("We did not respect the face inclusion");
          fi;
        fi;
        if RankMat(EXT)-1<>iRank then
          Error("Non correct rank of EXT");
        fi;
        if TestForRepetition(EXT)=true then
          Print("We have some repetition in EXT\n");
          Error("Clearly a bug");
        fi;
        NewListOrbitByRank[iRank+2][iOrbit].EXT:=EXT;
        ListPermGens:=[];
        for eGen in GeneratorsOfGroup(NewListOrbitByRank[iRank+2][iOrbit].TheStab)
        do
          eList:=List(EXT, x->Position(EXT, x*eGen));
          ePerm:=PermList(eList);
          if ePerm=fail then
            Error("Please debug from here 2");
          fi;
          Add(ListPermGens, ePerm);
        od;
        ThePermStab:=PersoGroupPerm(ListPermGens);
        NewListOrbitByRank[iRank+2][iOrbit].TheStabPerm:=ThePermStab;
        FAC:=[];
        len:=Length(NewListIFace);
        for iL in [1..len]
        do
#          Print("    iL=", iL, "  len=", len, "\n");
          iFace:=NewListIFace[iL];
          eElt:=NewListElt[iL];
          EXTimage:=NewListOrbitByRank[iRank+1][iFace].EXT*eElt;
          eSet:=Set(List(EXTimage, x->Position(EXT, x)));
          if Position(eSet, fail)<>fail then
            Error("vertices of face not found, please panic");
          fi;
          Add(FAC, eSet);
        od;
        Ofac:=Orbits(ThePermStab, FAC, OnSets);
        NewListOrbitByRank[iRank+2][iOrbit].FAC:=FAC;
        Print("  iOrbit=", iOrbit, " |EXT|=", Length(EXT), " |stab|=", Order(NewListOrbitByRank[iRank+2][iOrbit].TheStab), " |stabPerm|=", Order(ThePermStab), " |FAC|=", len, " |Ofac|=", Length(Ofac), "\n");
        if iRank=1 then
          if Length(NewListIFace)<>2 then
            Error("Deep inconsistency apparently");
          fi;
          NewListSign:=[1,-1];
        else
          ListSetsM2:=[];
          ListElementM2:=[];
          ListDebugInfo:=[];
          ListOccuringCoefficients:=[];
          lenBound:=Length(NewListIFace);
          for iBound in [1..lenBound]
          do
            iFaceM1:=NewListIFace[iBound];
            TheBoundary:=NewListOrbitByRank[iRank+1][iFaceM1].BoundaryImage;
            lenBoundB:=Length(TheBoundary.ListIFace);
            for iBoundB in [1..lenBoundB]
            do
              iFaceM2:=TheBoundary.ListIFace[iBoundB];
              eSign:=TheBoundary.ListSign[iBoundB];
              eEltM2:=TheBoundary.ListElt[iBoundB];
              eAddElt:=eEltM2*NewListElt[iBound];
              EXTimage:=NewListOrbitByRank[iRank][iFaceM2].EXT*eAddElt;
              eSet:=Set(List(EXTimage, x->Position(EXT, x)));
              pos:=Position(ListSetsM2, eSet);
              if pos=fail then
                Add(ListSetsM2, eSet);
                Add(ListElementM2, eAddElt);
                Add(ListDebugInfo, rec(iFaceM1:=iFaceM1, iBound:=iBound));
                Add(ListOccuringCoefficients, [rec(Sign:=eSign, idx:=iBound)]);
              else
                eMulSign:=FuncSignatureDet(iRank-2, iFaceM2, ListElementM2[pos]*eAddElt^(-1));
                Add(ListOccuringCoefficients[pos], rec(Sign:=eMulSign*eSign, idx:=iBound));
              fi;
            od;
          od;
          NewListSign:=UntangleAllSigns(ListOccuringCoefficients, lenBound);
        fi;
        eNewBound:=rec(ListIFace:=NewListIFace, ListSign:=NewListSign, ListElt:=NewListElt);
        NewListOrbitByRank[iRank+2][iOrbit].BoundaryImage:=eNewBound;
      od;
    fi;
  od;
  return rec(ListOrbitByRank:=NewListOrbitByRank,
             IdentityElt:=eRecordTessel.IdentityElt);
end;

# Idea is that for the interior of a cell, we use DoCloture_NextGeneration
# for having the family of cells.
# When we decompose one cell, we induce a decomposition of the subcell
# containing it. This has to be combined with other decompositions in
# order to get a puzzle out of it.
# When puzzles are constructed, we are adding vertices. Hence, we may actually
# add vertices to all the faces in which they are contained.
# This vertex addition takes place at all times via the DoCloture_NextGeneration
# 
PolyhedralTesselationDecomposeCells_NextGeneration:=function(eRecordTessel, eRecIAI, ListCellDecompose)
  local ListGens, FunctionFaceDecomposition, ListListEXT, ListListFAC, ListListPermGRP, ListDecomposition, IsFinished, iCase, ListStatusInsert, eRec, pos, ListCellChanges, iRank, eBound, jOrbit, iOrbit, nbCase, eCase, ListEXT, ListFAC, GRPperm, TotalListBoundary, eRecDecomp, eStabPerm, EXT, eList, ListPermGens, ListMatrGens, ListBoundInfo, TheActionFace, eStabBig, FAC, eRepr, eSelect, eNewList, TheStab, eGen, eStab, TestIsomorphism, NewListCells, eNewRec, TheDimension, nbOrbit, ListPermGRP, FuncInsertInList, phi, eRecIns, eFaceNew, TheRotSub, eRecF, nbRepr, iRepr, eNewBound, FuncSignatureDet, NewListOrbitByRank, NewListElt, NewListSign, NewListIFace, eSign, fSign, eElt, iFace, eOrigin, eNature, ListListListListRecIns, ListListListRecIns, ListListRecIns, ListRecIns, iBound, nbBound, SetEXT, eFaceIrr, ListDecompositionCell, IsFacePuzzle, ListListPhi, ListPhi, lenBound, ListOccuringCoefficients, eMulSign, eAddElt, ListElementM2, iBoundB, TheBoundary, iOrbitAsk, ListSetsM2, eSet, EXTimage, iFaceM2, eEltM2, lenBoundB, iFaceM1, eEltB, eProd, posChg, ListPuzzleFaceInclusion, lenB, iB, iOrbitB, GetPositionOld, eRecChg, eBoundOld, len, EXTn, eEltN, iOrbitN, PuzzleDatabaseUpdate, FuncInsertPiecePuzzle, posChg2, iL, nbOldOrbit, iRankBis, iOrbitBis, nbOrbitBis, iCaseOrig, iReprOrig, iRankOrig, iOrbitOrig, ListListPhiNew, ListPhiNew, ePosOld, ThePermStab, ePerm, iOrbitOld, GetStabilizerAndRotation, EXTpuzzle, EXTmain, GetLinearMerge, ListLinearDecomposition, TheFindInLinearMerge, eRecBound, Ofac, ListDebugInfo, DebugEXT, eEXTspec, DebugListIBound, DebugListSets, DebugListSetsAtt, DebugGRP, DebugEXT2, DebugGRP2, DebugRecBound, EXTdiff, eSetDiff, EXTimageB, DebugListEXTM1, DebugGRA, eIntEXT, i, j, DebugListSetsByBound, DebugSetsByBound, DebugListListEXTimage, DebugListEXTimage, eIntSet, DebugListListAdjSet, DebugListAdjSet, MainRecOrigin;
  TheActionFace:=function(x, g)
    return Set(x*g);
  end;
  ListListPermGRP:=[];
  ListListPhi:=[];
  TheDimension:=Length(eRecordTessel.ListOrbitByRank)-2;
  Print("TheDimension=", TheDimension, "\n");
  for iRank in [0..TheDimension]
  do
    nbOrbit:=Length(eRecordTessel.ListOrbitByRank[iRank+2]);
    ListPermGRP:=[];
    ListPhi:=[];
    for iOrbit in [1..nbOrbit]
    do
      EXT:=eRecordTessel.ListOrbitByRank[iRank+2][iOrbit].EXT;
      if TestForRepetition(EXT)=true then
        Print("We have some repetition in EXT\n");
        Print("In the input eRecordTessel, with more clearly\n");
        Print("This is for iRank=", iRank, " iOrbit=", iOrbit, "\n");
        Error("Clearly a bug");
      fi;
      ListPermGens:=[];
      TheStab:=eRecordTessel.ListOrbitByRank[iRank+2][iOrbit].TheStab;
      ListMatrGens:=GeneratorsOfGroup(TheStab);
      for eGen in ListMatrGens
      do
        eList:=List(EXT, x->Position(EXT, x*eGen));
        Add(ListPermGens, PermList(eList));
      od;
      GRPperm:=PersoGroupPerm(ListPermGens);
      phi:=GroupHomomorphismByImagesNC(TheStab, GRPperm, ListMatrGens, ListPermGens);
      Add(ListPhi, phi);
      Add(ListPermGRP, GRPperm);
    od;
    Add(ListListPermGRP, ListPermGRP);
    Add(ListListPhi, ListPhi);
  od;
  ListCellChanges:=[];
  ListStatusInsert:=[];
  for eCase in ListCellDecompose
  do
    iRank:=eCase.iRank;
    iOrbit:=eCase.iOrbit;
    eRec:=rec(iRank:=iRank, iOrbit:=iOrbit);
    Add(ListCellChanges, eRec);
    Add(ListStatusInsert, 0);
  od;
  if Length(Set(ListCellChanges))<>Length(ListCellChanges) then
    Error("Inconsistency in your input");
  fi;
  while(true)
  do
    IsFinished:=true;
    nbCase:=Length(ListCellChanges);
    for iCase in [1..nbCase]
    do
      if ListStatusInsert[iCase]=0 then
        IsFinished:=false;
        ListStatusInsert[iCase]:=1;
        iRank:=ListCellChanges[iCase].iRank;
        iOrbit:=ListCellChanges[iCase].iOrbit;
        if iRank>=1 then
          eBound:=eRecordTessel.ListOrbitByRank[iRank+2][iOrbit].BoundaryImage;
          for jOrbit in eBound.ListIFace
          do
            eRec:=rec(iRank:=iRank-1, iOrbit:=jOrbit);
            pos:=Position(ListCellChanges, eRec);
            if pos=fail then
              Add(ListCellChanges, eRec);
              Add(ListStatusInsert, 0);
            fi;
          od;
        fi;
      fi;
    od;
    if IsFinished=true then
      break;
    fi;
  od;
  Print("ListCellChanges determined\n");
  NewListOrbitByRank:=[];
  eFaceIrr:=rec(EXT:=[], TheStab:="irrelevant", BoundaryImage:="irrelevant", TheDel:="irrelevant");
  NewListOrbitByRank[1]:=[eFaceIrr];
  for iRank in [0..TheDimension]
  do
    nbOrbit:=Length(eRecordTessel.ListOrbitByRank[iRank+2]);
    eNewList:=[];
    nbOldOrbit:=0;
    for iOrbit in [1..nbOrbit]
    do
      eRec:=rec(iRank:=iRank, iOrbit:=iOrbit);
      pos:=Position(ListCellChanges, eRec);
      if pos=fail then
        EXT:=eRecordTessel.ListOrbitByRank[iRank+2][iOrbit].EXT;
        TheStab:=eRecordTessel.ListOrbitByRank[iRank+2][iOrbit].TheStab;
        TheRotSub:=eRecordTessel.ListOrbitByRank[iRank+2][iOrbit].RotationSubgroup;
        eNewRec:=rec(TheStab:=TheStab, RotationSubgroup:=TheRotSub, eNature:="old", eOrigin:=[iRank, iOrbit]);
#        Print("iRank=", iRank, " iOrbit=", iOrbit, " |stab|=", Order(TheStab), "\n");
        if iRank=0 then
          eNewRec.EXT:=EXT;
        fi;
        Add(eNewList, eNewRec);
        nbOldOrbit:=nbOldOrbit+1;
      fi;
    od;
    NewListOrbitByRank[iRank+2]:=eNewList;
#    Print("iRank=", iRank, " nbOldOrbit=", nbOldOrbit, "\n");
  od;
  GetPositionOld:=function(iRank, iOrbit)
    local len, i;
    len:=Length(NewListOrbitByRank[iRank+2]);
    for i in [1..len]
    do
      if NewListOrbitByRank[iRank+2][i].eOrigin=[iRank, iOrbit] then
        return i;
      fi;
    od;
    Error("GetPositionOld did not get the right index");
  end;
  GetStabilizerAndRotation:=function(EXT)
    local eSumEXT, TheStab, TheRed, TheBasis, ListMatrGens, ListPermGens, TheSym2, eGen, eMat, eEXT, eDet, FuncInsertGenerator, eElt, ePerm, eRotSubgroup, TheSubgroup;
    eSumEXT:=Sum(EXT);
    TheStab:=eRecIAI.FuncAutomorphism(eSumEXT);
    ListMatrGens:=[];
    TheSubgroup:=Group([eRecordTessel.IdentityElt]);
    FuncInsertGenerator:=function(eElt)
      local pos;
      pos:=First(EXT*eElt, x->Position(EXT, x)=fail);
      if pos=fail then
        if eElt in TheSubgroup then
          return;
        fi;
        Add(ListMatrGens, eElt);
        TheSubgroup:=Group(ListMatrGens);
      fi;
    end;
    for eElt in TheStab
    do
      FuncInsertGenerator(eElt);
    od;
    #
    TheRed:=RowReduction(EXT);
    TheBasis:=TheRed.EXT;
    ListPermGens:=[];
    TheSym2:=SymmetricGroup(2);
    for eGen in ListMatrGens
    do
      eMat:=[];
      for eEXT in TheBasis
      do
        Add(eMat, SolutionMat(TheBasis, eEXT*eGen));
      od;
      eDet:=DeterminantMat(eMat);
      if eDet=1 then
        ePerm:=();
      else
        ePerm:=(1,2);
      fi;
      Add(ListPermGens, ePerm);
    od;
    eRotSubgroup:=GetKernelOfMapping(TheSubgroup, TheSym2, ListMatrGens, ListPermGens);
    return rec(TheStab:=TheSubgroup, RotationSubgroup:=eRotSubgroup);
  end;
  TestIsomorphism:=function(eFace1, eFace2)
    local eSumEXT1, eSumEXT2, testIso, eElt, eProd, pos;
    eSumEXT1:=Sum(eFace1.EXT);
    eSumEXT2:=Sum(eFace2.EXT);
    testIso:=eRecIAI.FuncIsomorphism(eSumEXT1, eSumEXT2);
    if testIso=fail then
      return fail;
    fi;
    for eElt in eFace1.TheStab
    do
      eProd:=eElt*testIso;
      pos:=First(eFace1.EXT*eProd, x->Position(eFace2.EXT, x)=fail);
      if pos=fail then
        return eProd;
      fi;
    od;
    return fail;
  end;
  GetLinearMerge:=function(iRank, iOrbit)
    local ListListMerges, EXT, ePermStab, phi, jRank, ListFaceStab, FuncInsertFace, TheNewList, eStabFaceConv, eRecIns, eRecChg, posChg, iEnt, nbEnt, eEXT, EXTproj, FACproj, eSelect;
    ListListMerges:=[];
    EXT:=eRecordTessel.ListOrbitByRank[iRank+2][iOrbit].EXT;
    eSelect:=ColumnReduction(EXT).Select;
    EXTproj:=List(EXT, x->x{eSelect});
    FACproj:=DualDescription(EXTproj);
    ePermStab:=ListListPermGRP[iRank+1][iOrbit];
    phi:=ListListPhi[iRank+1][iOrbit];
    eRecChg:=rec(iRank:=iRank, iOrbit:=iOrbit);
    posChg:=Position(ListCellChanges, eRecChg);
    for jRank in [0..iRank]
    do
      TheNewList:=[];
      ListFaceStab:=[];
      FuncInsertFace:=function(eNewRec)
        local iOrbit, eRec, testPerm, testMatr, eSetImg, eRecOrbit, len, iL, eElt, EXTface, ListEXT, ListElt, ListIOrbitOld;
        for iOrbit in [1..Length(TheNewList)]
        do
          eRec:=TheNewList[iOrbit];
          testPerm:=RepresentativeAction(ePermStab, eNewRec.eSetConv, eRec.eSetConv, OnSets);
          if testPerm<>fail then
            testMatr:=PreImagesRepresentative(phi, testPerm);
            eSetImg:=OnSets(eNewRec.eSet, testPerm);
            eRecOrbit:=OrbitWithAction(ListFaceStab[iOrbit], eSetImg, OnSets);
            len:=Length(eRecOrbit.ListElement);
            for iL in [1..len]
            do
              eElt:=eNewRec.eElt*testMatr*PreImagesRepresentative(phi, eRecOrbit.ListElement[iL]);
              EXTface:=EXT{eRecOrbit.ListCoset[iL]};
              for eEXT in EXTface
              do
                if First(FACproj, x->x*eEXT{eSelect}<0)<>fail then
                  Error("Non correct vertex");
                fi;
              od;
              Add(TheNewList[iOrbit].ListEXT, EXTface);
              Add(TheNewList[iOrbit].ListElt, eElt);
              Add(TheNewList[iOrbit].ListIOrbitOld, eNewRec.iOrbit);
            od;
            return;
          fi;
        od;
        eStabFaceConv:=Stabilizer(ePermStab, eNewRec.eSetConv, OnSets);
        Add(ListFaceStab, eStabFaceConv);
        eRecOrbit:=OrbitWithAction(eStabFaceConv, eNewRec.eSet, OnSets);
        len:=Length(eRecOrbit.ListElement);
        ListEXT:=[];
        ListElt:=[];
        ListIOrbitOld:=[];
        for iL in [1..len]
        do
          eElt:=eNewRec.eElt*PreImagesRepresentative(phi, eRecOrbit.ListElement[iL]);
          EXTface:=EXT{eRecOrbit.ListCoset[iL]};
          Add(ListEXT, EXTface);
          Add(ListElt, eElt);
          Add(ListIOrbitOld, eNewRec.iOrbit);
        od;
        eRecIns:=rec(eSetConv:=eNewRec.eSetConv, 
                     ListEXT:=ListEXT, 
                     ListElt:=ListElt, 
                     ListIOrbitOld:=ListIOrbitOld);
        Add(TheNewList, eRecIns);
      end;
      nbOrbit:=Length(ListDecompositionCell[posChg][jRank+1]);
      for iOrbit in [1..nbOrbit]
      do
        eRecIns:=ListDecompositionCell[posChg][jRank+1][iOrbit];
        FuncInsertFace(eRecIns);
      od;
      for iOrbit in [1..Length(TheNewList)]
      do
        nbEnt:=Length(TheNewList[iOrbit].ListEXT);
        for iEnt in [1..nbEnt]
        do
          if Set(TheNewList[iOrbit].ListEXT[iEnt])<>Set(eRecordTessel.ListOrbitByRank[jRank+2][TheNewList[iOrbit].ListIOrbitOld[iEnt]].EXT*TheNewList[iOrbit].ListElt[iEnt]) then
            Error("Bookkeeping error");
          fi;
        od;
      od;
      Add(ListListMerges, TheNewList);
    od;
    return ListListMerges;
  end;
  TheFindInLinearMerge:=function(EXT, iRank, iOrbit)
    local ListBoundary, NSP, EXTface, eSetConv, eRecChg, posChg, eCase, testPerm, testMatr, ListEXTdecompo, eSelect, EXTproj, FACproj, eStabPerm, phi, EXTinProj, FACinProj, FACint, EXTint, O, iRankTarget, EXTinImg, EXTin, iL, len, ListEltDecompo, ListIOrbitOldDecompo, ListSelect, EXTinProjIrred, IsCorrect, ePerm, iCase, GRPperm, ListPermGens, ListNature, FACsel, eSetConvTotal, EXTfaceSelProj, eSelectFace, EXTfacePROJ, FACfacePROJ, eEXT, DoCheck, SumVol, TotVol;
    NSP:=NullspaceMat(TransposedMat(EXT));
    Print("|EXT|=", Length(EXT), " |EXT[1]|=", Length(EXT[1]), "\n");
    eSelect:=ColumnReduction(EXT).Select;
    DoCheck:=true;
    if DoCheck then
      TotVol:=VolumeComputationPolytope(List(EXT, x->x{eSelect}));
    fi;
    if Length(EXT)<>Length(Set(EXT)) then
      Error("Input has some repetition, illegal of course");
    fi;
    if SearchPositiveRelationSimple(EXT)<>false then
      Error("Apparently, this is not a polytope");
    fi;
    EXTface:=eRecordTessel.ListOrbitByRank[iRank+2][iOrbit].EXT;
    eSelectFace:=ColumnReduction(EXTface).Select;
    EXTfacePROJ:=List(EXTface, x->x{eSelectFace});
    FACfacePROJ:=DualDescription(EXTfacePROJ);
    for eEXT in EXT
    do
      if First(FACfacePROJ, x->x*eEXT{eSelectFace}<0)<>fail then
        Error("We have a wrong vertex");
      fi;
    od;
    EXTproj:=List(EXT, x->x{eSelect});
    FACproj:=DualDescription(EXTproj);
    eStabPerm:=ListListPermGRP[iRank+1][iOrbit];
    phi:=ListListPhi[iRank+1][iOrbit];
    iRankTarget:=RankMat(EXT)-1;
    Print("EXTface=", Length(EXTface), "\n");
    eSetConv:=Filtered([1..Length(EXTface)], x->First(NSP, y->y*EXTface[x]<>0)=fail);
    EXTfaceSelProj:=List(EXTface{eSetConv}, x->x{eSelect});
    FACsel:=Filtered(FACproj, x->First(EXTfaceSelProj, y->y*x<>0)=fail);
    eSetConvTotal:=eSetConv{Filtered([1..Length(eSetConv)], x->First(FACsel, y->y*EXTfaceSelProj[x]<>0)=fail)};
    eRecChg:=rec(iRank:=iRank, iOrbit:=iOrbit);
    posChg:=Position(ListCellChanges, eRecChg);
    if posChg=fail then
      Error("Please debug from here posChg");
    fi;
    Print("eSetConv=", eSetConv, " eSetConvTotal=", eSetConvTotal, "\n");
    if eSetConv<>eSetConvTotal then
      Print("We are in Case 1\n");
      return rec(ListEXT:=[EXT],
                 ListNature:=["new"],
                 ListElt:=["irrelevant"],
                 ListIOrbitOld:=["irrelevant"]);
    fi;
    for iCase in [1..Length(ListLinearDecomposition[posChg][iRankTarget+1])]
    do
      eCase:=ListLinearDecomposition[posChg][iRankTarget+1][iCase];
      testPerm:=RepresentativeAction(eStabPerm, eCase.eSetConv, eSetConv, OnSets);
      if testPerm<>fail then
        testMatr:=PreImagesRepresentative(phi, testPerm);
        ListEXTdecompo:=[];
        ListEltDecompo:=[];
        ListIOrbitOldDecompo:=[];
        ListNature:=[];
        len:=Length(eCase.ListEXT);
        IsCorrect:=true;
        for iL in [1..len]
        do
          Print("iL=", iL, "/", len, "\n");
          EXTin:=eCase.ListEXT[iL];
          EXTinImg:=EXTin*testMatr;
          EXTinProj:=List(EXTinImg, x->x{eSelect});
          FACinProj:=DualDescription(EXTinProj);
          EXTinProjIrred:=DualDescription(FACinProj);
          FACint:=Concatenation(FACinProj, FACproj);
          if SearchPositiveRelationSimple(FACint)=false then
            EXTint:=DualDescription(FACint);
            if RankMat(EXTint)=iRankTarget+1 then
              if Set(EXTinProjIrred)<>Set(EXTint) then
                IsCorrect:=false;
              fi;
              Add(ListEXTdecompo, Set(EXTinImg));
              Add(ListEltDecompo, eCase.ListElt[iL]*testMatr);
              Add(ListIOrbitOldDecompo, eCase.ListIOrbitOld[iL]);
              Add(ListNature, "old");
            fi;
          fi;
        od;
        if IsCorrect=true then
          Print("We are in Case 2\n");
          if DoCheck then
            SumVol:=Sum(List(ListEXTdecompo, x->VolumeComputationPolytope(List(x, y->y{eSelect}))));
            Print(" SumVol=", SumVol, " TotVol=", TotVol, "\n");
            if SumVol<>TotVol then
              Error("The volume error is just the beginning");
            fi;
          fi;
          return rec(ListEXT:=ListEXTdecompo,
                     ListNature:=ListNature,
                     ListElt:=ListEltDecompo,
                     ListIOrbitOld:=ListIOrbitOldDecompo);
        fi;
      fi;
    od;
    Print("We are in Case 3\n");
    return rec(ListEXT:=[EXT],
               ListNature:=["new"],
               ListElt:=["irrelevant"],
               ListIOrbitOld:=["irrelevant"]);
  end;
  ListDecompositionCell:=[];
  ListPuzzleFaceInclusion:=[];
  for eRec in ListCellChanges
  do
#    Print("Computing orbit subfaces for iRank=", eRec.iRank, " iOrbit=", eRec.iOrbit, "\n");
    Add(ListDecompositionCell, GetCollectionSubfaces(eRecordTessel, eRec.iRank, eRec.iOrbit));
    Add(ListPuzzleFaceInclusion, rec(EXT:=[], ListRecOrigin:=[], ListNewIOrbit:=[], ListNewElt:=[], ListNewEXT:=[]));
  od;
  ListLinearDecomposition:=[];
  for eRec in ListCellChanges
  do
    Add(ListLinearDecomposition, GetLinearMerge(eRec.iRank, eRec.iOrbit));
  od;
  FuncInsertInList:=function(eFaceNew, iRank)
    local iOrbit, nbOrbit, testIso, eRecStab, NewFace;
    nbOrbit:=Length(NewListOrbitByRank[iRank+2]);
    for iOrbit in [1..nbOrbit]
    do
      if NewListOrbitByRank[iRank+2][iOrbit].eNature="new" then
        testIso:=TestIsomorphism(NewListOrbitByRank[iRank+2][iOrbit], eFaceNew);
        if testIso<>fail then
          return rec(iOrbit:=iOrbit, IsNew:=false, eMap:=testIso);
        fi;
      fi;
    od;
    eRecStab:=GetStabilizerAndRotation(eFaceNew.EXT);
    NewFace:=rec(iRank:=eFaceNew.iRank,
                 EXT:=eFaceNew.EXT,
                 eNature:=eFaceNew.eNature,
                 eOrigin:=eFaceNew.eOrigin,
                 TheStab:=eRecStab.TheStab,
                 RotationSubgroup:=eRecStab.RotationSubgroup);
    Add(NewListOrbitByRank[iRank+2], NewFace);
    return rec(iOrbit:=nbOrbit+1, IsNew:=true, eMap:=eRecordTessel.IdentityElt);
  end;
  # we need to determine if eFaceNew is part of the puzzle of a face
  # and resolve the puzzle later on.
  # 
  IsFacePuzzle:=function(EXTbig, EXTsmall)
    local FACbig, eEXT, pos;
    FACbig:=DualDescription(EXTbig);
    for eEXT in EXTsmall
    do
      pos:=First(FACbig, x->x*eEXT<0);
      if pos<>fail then
        return false;
      fi;
    od;
    return true;
  end;
  FuncInsertPiecePuzzle:=function(posChg, eRecOrigin, EXTn, iOrbitN, eEltN)
    local len, SetEXT, i;
    len:=Length(ListPuzzleFaceInclusion[posChg].ListNewIOrbit);
    SetEXT:=Set(EXTn);
    for i in [1..len]
    do
      if SetEXT=ListPuzzleFaceInclusion[posChg].ListNewEXT[i] then
        return;
      fi;
    od;
    Add(ListPuzzleFaceInclusion[posChg].ListNewIOrbit, iOrbitN);
    Add(ListPuzzleFaceInclusion[posChg].ListRecOrigin, eRecOrigin);
    Add(ListPuzzleFaceInclusion[posChg].ListNewEXT, SetEXT);
    Add(ListPuzzleFaceInclusion[posChg].ListNewElt, eEltN);
    ListPuzzleFaceInclusion[posChg].EXT:=Union(ListPuzzleFaceInclusion[posChg].EXT, SetEXT);
    eRecChg:=ListCellChanges[posChg];
    Print("Now iRank=", eRecChg.iRank, " iOrbit=", eRecChg.iOrbit, " |ListPuzzleFaceInclusion|=", Length(ListPuzzleFaceInclusion[posChg].ListNewIOrbit), " |EXT|=", Length(ListPuzzleFaceInclusion[posChg].EXT), "\n");
  end;
  PuzzleDatabaseUpdate:=function(eFaceNew, MainRecOrigin, eRecIns, iRank, iOrbit)
    local rnk, iRankTarget, posChg, eRecChg, eSetConv, EXTnull,  NSP, testPuzzle, ePermStab, eStabBperm, eStabBmatr, eStabCperm, eStabCmatr, ListImages, ListIOrbit, ListElement, SetEXTsub, phi, eRecOrbitC, eRecOrbitB, lenOrbC, lenOrb, iOrbC, eSet, SetEXTproj, len, ePerm, iOrb, eProd, eProdInv, testMatr, testPerm, posChg2, eRecChg2, EXTred, SetEXT, EXT, eRecOrigin;
    iRankTarget:=eFaceNew.iRank;
    EXT:=eRecordTessel.ListOrbitByRank[iRank+2][iOrbit].EXT;
    NSP:=NullspaceMat(TransposedMat(eFaceNew.EXT));
    eSelect:=ColumnReduction(eFaceNew.EXT).Select;
    EXTred:=List(eFaceNew.EXT, x->x{eSelect});
    SetEXTsub:=Set(eFaceNew.EXT);
    EXTnull:=Filtered(EXT, x->First(NSP, y->y*x<>0)=fail);
    eSetConv:=Set(List(EXTnull, x->Position(EXT, x)));
    ePermStab:=ListListPermGRP[iRank+1][iOrbit];
    phi:=ListListPhi[iRank+1][iOrbit];
    eRecChg:=rec(iRank:=iRank, iOrbit:=iOrbit);
    posChg:=Position(ListCellChanges, eRecChg);
    for eRec in ListDecompositionCell[posChg][iRankTarget+1]
    do
      testPerm:=RepresentativeAction(ePermStab, eRec.eSetConv, eSetConv, OnSets);
      if testPerm<>fail then
        testMatr:=PreImagesRepresentative(phi, testPerm);
        eStabBperm:=Stabilizer(ePermStab, eSetConv, OnSets);
        eStabBmatr:=PreImage(phi, eStabBperm);
        SetEXT:=Set(EXT{eRec.eSet}*testMatr);
        eRecOrbitB:=OrbitWithAction(eStabBmatr, SetEXT, TheActionFace);
        lenOrb:=Length(eRecOrbitB.ListCoset);
        for iOrb in [1..lenOrb]
        do
          SetEXTproj:=List(eRecOrbitB.ListCoset[iOrb], x->x{eSelect});
          testPuzzle:=IsFacePuzzle(SetEXTproj, EXTred);
          if testPuzzle=true then
            eRecChg2:=rec(iRank:=iRankTarget, iOrbit:=eRec.iOrbit);
            posChg2:=Position(ListCellChanges, eRecChg2);
            eSet:=Set(List(eRecOrbitB.ListCoset[iOrb], x->Position(EXT, x)));
            eStabCperm:=Stabilizer(eStabBperm, eSet, OnSets);
            eStabCmatr:=PreImage(phi, eStabCperm);
            eRecOrbitC:=OrbitWithAction(eStabCmatr, SetEXTsub, TheActionFace);
            lenOrbC:=Length(eRecOrbitC.ListCoset);
            iOrbitN:=eRecIns.iOrbit;
            eProd:=eRec.eElt*testMatr*eRecOrbitB.ListElement[iOrb];
            eProdInv:=Inverse(eProd);
            for iOrbC in [1..lenOrbC]
            do
              eEltN:=eRecOrbitC.ListElement[iOrbC]*eProdInv;
              EXTn:=eFaceNew.EXT*eEltN;
              eRecOrigin:=rec(iRepr:=MainRecOrigin.iRepr, 
                              iOrbC:=iOrbC, posChg:=posChg);
              FuncInsertPiecePuzzle(posChg2, eRecOrigin, EXTn, iOrbitN, eEltN);
            od;
            return;
          fi;
        od;
      fi;
    od;
  end;
  ListDecomposition:=[];
  TotalListBoundary:=[];
  nbCase:=Length(ListCellDecompose);
  ListListListListRecIns:=[];
  ListListPhiNew:=[];
  for iCase in [1..nbCase]
  do
    Print("iCase=", iCase, "/", nbCase, "\n");
    eCase:=ListCellDecompose[iCase];
    CheckDecomposition(eRecordTessel, eCase);
    iRank:=eCase.iRank;
    iOrbit:=eCase.iOrbit;
    ListBoundInfo:=[];
    nbRepr:=Length(eCase.ListRepresentent);
    ListListListRecIns:=[];
    ListPhiNew:=[];
    for iRepr in [1..nbRepr]
    do
      Print("  iRepr=", iRepr, "/", nbRepr, "\n");
      eRepr:=eCase.ListRepresentent[iRepr];
      Print("FaceLattComp, EXT=", eRepr.EXT, "\n");
      eStabBig:=eRecordTessel.ListOrbitByRank[iRank+2][iOrbit].TheStab;
      eStab:=Stabilizer(eStabBig, Set(eRepr.EXT), TheActionFace);
      ListPermGens:=[];
      ListGens:=GeneratorsOfGroup(eStab);
      for eGen in ListGens
      do
        eList:=List(eRepr.EXT, x->Position(eRepr.EXT, x*eGen));
        Add(ListPermGens, PermList(eList));
      od;
      eStabPerm:=PersoGroupPerm(ListPermGens);
      phi:=GroupHomomorphismByImagesNC(eStab, eStabPerm, ListGens, ListPermGens);
      Add(ListPhiNew, phi);
      Print("|eStabBig|=", Order(eStabBig), " |eStab|=", Order(eStab), "\n");
      FunctionFaceDecomposition:=function(EXTinp)
        local eSetConv, eRecConv, testPerm, NewListEXT, eSet, eSetImg, NewListElt, NewListNature, NewListIOrbitOld, eSelect, DoCheck, SumVol, TotVol;
        eSetConv:=Set(List(EXTinp, x->Position(eRepr.EXT,x)));
        eSelect:=ColumnReduction(EXTinp).Select;
        DoCheck:=true;
        if DoCheck then
          TotVol:=VolumeComputationPolytope(List(EXTinp, x->x{eSelect}));
        fi;
        for eRecConv in eRepr.ListRecConv
        do
          testPerm:=RepresentativeAction(eStabPerm, eRecConv.eSetConv, eSetConv, OnSets);
          if testPerm<>fail then
            NewListEXT:=[];
            NewListElt:=[];
            NewListNature:=[];
            NewListIOrbitOld:=[];
            SumVol:=0;
            for eSet in eRecConv.ListSets
            do
              eSetImg:=OnSets(eSet, testPerm);
              if DoCheck then
                SumVol:=SumVol + VolumeComputationPolytope(List(eRepr.EXT{eSetImg}, x->x{eSelect}));
              fi;
              Add(NewListEXT, eRepr.EXT{eSetImg});
              Add(NewListElt, "irrelevant");
              Add(NewListNature, "new");
              Add(NewListIOrbitOld, "irrelevant");
            od;
            if DoCheck then
              Print("SumVol=", SumVol, " TotVol=", TotVol, "\n");
              if SumVol<>TotVol then
                Error("Error in the volume considered");
              fi;
            fi;
            return rec(ListEXT:=NewListEXT,
                       ListElt:=NewListElt, 
                       ListNature:=NewListNature, 
                       ListIOrbitOld:=NewListIOrbitOld);
          fi;
        od;
        return TheFindInLinearMerge(EXTinp, iRank, iOrbit);
      end;
      if Length(eRepr.EXT)<>Length(Set(eRepr.EXT)) then
        Error("We have repetition in eRepr.EXT");
      fi;
      eRecDecomp:=GetCompleteAndTotalDecomposition(eRepr.EXT, eStabPerm, FunctionFaceDecomposition, eRecordTessel);
      ListListRecIns:=[];
      for iRankBis in [0..eRecDecomp.rnk]
      do
        nbOrbitBis:=Length(eRecDecomp.ListOrbitByRank[iRankBis+2]);
        ListRecIns:=[];
        for iOrbitBis in [1..nbOrbitBis]
        do
          eRecF:=eRecDecomp.ListOrbitByRank[iRankBis+2][iOrbitBis];
          eFaceNew:=rec(iRank:=iRankBis, EXT:=eRepr.EXT{eRecF.eSet}, eNature:="new", eOrigin:=[iCase, iRepr, iRankBis, iOrbitBis]);
          eRecIns:=FuncInsertInList(eFaceNew, iRankBis);
          if Length(eFaceNew.EXT)=1 then
            Print("             EXT=", eFaceNew.EXT, "\n");
          fi;
          if eRecIns.IsNew=true then
            MainRecOrigin:=rec(iRepr:=iRepr, iRank:=iRank, iOrbit:=iOrbit);
            PuzzleDatabaseUpdate(eFaceNew, MainRecOrigin, eRecIns, iRank, iOrbit);
          fi;
          Add(ListRecIns, eRecIns);
        od;
        Add(ListListRecIns, ListRecIns);
      od;
      Add(ListBoundInfo, eRecDecomp);
      Add(ListListListRecIns, ListListRecIns);
    od;
    Add(TotalListBoundary, ListBoundInfo);
    Add(ListListListListRecIns, ListListListRecIns);
    Add(ListListPhiNew, ListPhiNew);
  od;
  FuncSignatureDet:=function(iRank, iOrbit, eElt)
    if not(eElt in NewListOrbitByRank[iRank+2][iOrbit].TheStab) then
      Error("Element is not in stabilizer, this is illegal");
    fi;    
    if eElt in NewListOrbitByRank[iRank+2][iOrbit].RotationSubgroup then
      return 1;
    fi;    
    return -1;
  end;
  Print("Checking correctness by volume and covering arguments\n");
  for iRank in [0..TheDimension]
  do
    nbOrbit:=Length(eRecordTessel.ListOrbitByRank[iRank+2]);
    Print("iRank=", iRank, " nbOrbit=", nbOrbit, "\n");
    for iOrbit in [1..nbOrbit]
    do
      eRecChg:=rec(iRank:=iRank, iOrbit:=iOrbit);
      posChg:=Position(ListCellChanges, eRecChg);
      Print("iRank=", iRank, "  iOrbit=", iOrbit, " posChg=", posChg, "\n");
      if posChg<>fail then
        EXTmain:=eRecordTessel.ListOrbitByRank[iRank+2][iOrbit].EXT;
        TheStab:=eRecordTessel.ListOrbitByRank[iRank+2][iOrbit].TheStab;
        EXTpuzzle:=ListPuzzleFaceInclusion[posChg].EXT;
        ListEXT:=ListPuzzleFaceInclusion[posChg].ListNewEXT;
        Print("  |EXTpuzzle|=", Length(EXTpuzzle), " |EXTmain|=", Length(EXTmain), " |Stab|=", Order(TheStab), " |ListEXT|=", Length(ListEXT), "\n");
        if IsSubset(Set(EXTpuzzle), Set(EXTmain))=false then
          Error("The puzzle vertices do not cover the original vertices");
        fi;
        Print("Call from checking by volume and covering\n");
        CheckCellularDecomposition(EXTmain, TheStab, ListEXT);
      fi;
    od;
  od;
  Print("Now computing the differentials\n");
  for iRank in [0..TheDimension]
  do
    nbOrbit:=Length(NewListOrbitByRank[iRank+2]);
    Print("iRank=", iRank, "\n");
    if iRank=0 then
      for iOrbit in [1..nbOrbit]
      do
        eBound:=rec(ListIFace:=[1], ListSign:=[1], ListElt:=[eRecordTessel.IdentityElt]);
        NewListOrbitByRank[iRank+2][iOrbit].BoundaryImage:=eBound;
        NewListOrbitByRank[iRank+2][iOrbit].TheStabPerm:=Group(());
        Print("  iOrbit=", iOrbit, " |EXT|=", Length(NewListOrbitByRank[iRank+2][iOrbit].EXT), " |GRP|=", Order(NewListOrbitByRank[iRank+2][iOrbit].TheStab), "\n");
      od;
    else
      for iOrbit in [1..nbOrbit]
      do
        eOrigin:=NewListOrbitByRank[iRank+2][iOrbit].eOrigin;
        eNature:=NewListOrbitByRank[iRank+2][iOrbit].eNature;
        NewListIFace:=[];
        NewListElt:=[];
        if eNature="new" then
          iCaseOrig:=eOrigin[1];
          iReprOrig:=eOrigin[2];
          iRankOrig:=eOrigin[3];
          iOrbitOrig:=eOrigin[4];
          if iRankOrig<>iRank then
            Error("It is an apparent bug in the ranks");
          fi;
          eRecBound:=TotalListBoundary[iCaseOrig][iReprOrig];
          EXT:=NewListOrbitByRank[iRank+2][iOrbit].EXT;
#          Print("  EXT=", EXT, "\n");
          eBound:=eRecBound.ListOrbitByRank[iRankOrig+2][iOrbitOrig].BoundaryImage;
          nbBound:=Length(eBound.ListIFace);
          for iBound in [1..nbBound]
          do
            iFace:=eBound.ListIFace[iBound];
            eElt:=eBound.ListElt[iBound];
            eRecIns:=ListListListListRecIns[iCaseOrig][iReprOrig][iRankOrig][iFace];
            Add(NewListIFace, eRecIns.iOrbit);
            Add(NewListElt, eRecIns.eMap*PreImagesRepresentative(ListListPhiNew[iCaseOrig][iReprOrig], eElt));
          od;
        else
          EXT:=[];
          iOrbitOld:=NewListOrbitByRank[iRank+2][iOrbit].eOrigin[2];
          eBoundOld:=eRecordTessel.ListOrbitByRank[iRank+2][iOrbitOld].BoundaryImage;
          len:=Length(eBoundOld.ListIFace);
          for iL in [1..len]
          do
            iOrbitB:=eBoundOld.ListIFace[iL];
            eEltB:=eBoundOld.ListElt[iL];
            eRecChg:=rec(iRank:=iRank-1, iOrbit:=iOrbitB);
            posChg:=Position(ListCellChanges, eRecChg);
            if posChg=fail then
              ePosOld:=GetPositionOld(iRank-1, iOrbitB);
              EXTimage:=Set(NewListOrbitByRank[iRank+1][ePosOld].EXT*eEltB);
              Add(NewListIFace, ePosOld);
              Add(NewListElt, eEltB);
            else
              EXTimage:=Set(ListPuzzleFaceInclusion[posChg].EXT*eEltB);
              lenB:=Length(ListPuzzleFaceInclusion[posChg].ListNewIOrbit);
              for iB in [1..lenB]
              do
                eProd:=ListPuzzleFaceInclusion[posChg].ListNewElt[iB]*eEltB;
                Add(NewListIFace, ListPuzzleFaceInclusion[posChg].ListNewIOrbit[iB]);
                Add(NewListElt, eProd);
              od;
            fi;
            EXT:=Union(EXT, EXTimage);
          od;
          if IsSubset(EXT, Set(eRecordTessel.ListOrbitByRank[iRank+2][iOrbitOld].EXT))=false then
            Error("We did not respect the face inclusion");
          fi;
        fi;
        if RankMat(EXT)-1<>iRank then
          Error("Non correct rank of EXT");
        fi;
        if TestForRepetition(EXT)=true then
          Error("We have some repetition in EXT");
        fi;
        NewListOrbitByRank[iRank+2][iOrbit].EXT:=EXT;
        ListPermGens:=[];
        for eGen in GeneratorsOfGroup(NewListOrbitByRank[iRank+2][iOrbit].TheStab)
        do
          eList:=List(EXT, x->Position(EXT, x*eGen));
          ePerm:=PermList(eList);
          if ePerm=fail then
            Error("Please debug from here 2");
          fi;
          Add(ListPermGens, ePerm);
        od;
        ThePermStab:=PersoGroupPerm(ListPermGens);
        NewListOrbitByRank[iRank+2][iOrbit].TheStabPerm:=ThePermStab;
        FAC:=[];
        len:=Length(NewListIFace);
        for iL in [1..len]
        do
#          Print("    iL=", iL, "  len=", len, "\n");
          iFace:=NewListIFace[iL];
          eElt:=NewListElt[iL];
          EXTimage:=NewListOrbitByRank[iRank+1][iFace].EXT*eElt;
          eSet:=Set(List(EXTimage, x->Position(EXT, x)));
          if Position(eSet, fail)<>fail then
            Error("vertices of face not found, please panic");
          fi;
          Add(FAC, eSet);
        od;
        Ofac:=Orbits(ThePermStab, FAC, OnSets);
        NewListOrbitByRank[iRank+2][iOrbit].FAC:=FAC;
        Print("  iOrbit=", iOrbit, " |EXT|=", Length(EXT), " |stab|=", Order(NewListOrbitByRank[iRank+2][iOrbit].TheStab), " |stabPerm|=", Order(ThePermStab), " |FAC|=", len, " |Ofac|=", Length(Ofac), "\n");
        if iRank=1 then
          if Length(NewListIFace)<>2 then
            Error("Deep inconsistency apparently");
          fi;
          NewListSign:=[1,-1];
        else
          ListSetsM2:=[];
          ListElementM2:=[];
          ListDebugInfo:=[];
          ListOccuringCoefficients:=[];
          lenBound:=Length(NewListIFace);
          for iBound in [1..lenBound]
          do
            iFaceM1:=NewListIFace[iBound];
            TheBoundary:=NewListOrbitByRank[iRank+1][iFaceM1].BoundaryImage;
            lenBoundB:=Length(TheBoundary.ListIFace);
            for iBoundB in [1..lenBoundB]
            do
              iFaceM2:=TheBoundary.ListIFace[iBoundB];
              eSign:=TheBoundary.ListSign[iBoundB];
              eEltM2:=TheBoundary.ListElt[iBoundB];
              eAddElt:=eEltM2*NewListElt[iBound];
              EXTimage:=NewListOrbitByRank[iRank][iFaceM2].EXT*eAddElt;
              eSet:=Set(List(EXTimage, x->Position(EXT, x)));
              pos:=Position(ListSetsM2, eSet);
              if pos=fail then
                Add(ListSetsM2, eSet);
                Add(ListElementM2, eAddElt);
                Add(ListDebugInfo, rec(iFaceM1:=iFaceM1, iBound:=iBound));
                Add(ListOccuringCoefficients, [rec(Sign:=eSign, idx:=iBound)]);
              else
                eMulSign:=FuncSignatureDet(iRank-2, iFaceM2, ListElementM2[pos]*eAddElt^(-1));
                Add(ListOccuringCoefficients[pos], rec(Sign:=eMulSign*eSign, idx:=iBound));
              fi;
            od;
          od;
          NewListSign:=UntangleAllSigns(ListOccuringCoefficients, lenBound);
        fi;
        eNewBound:=rec(ListIFace:=NewListIFace, ListSign:=NewListSign, ListElt:=NewListElt);
        NewListOrbitByRank[iRank+2][iOrbit].BoundaryImage:=eNewBound;
      od;
    fi;
  od;
  return rec(ListOrbitByRank:=NewListOrbitByRank,
             IdentityElt:=eRecordTessel.IdentityElt);
end;



PrintPolyhedralTesselationKeyInformation:=function(eRecordTessel)
  local TheDimension, iRank, nbOrbit, iOrbit, EXT, ThePermStab, TheStab, len;
  TheDimension:=Length(eRecordTessel.ListOrbitByRank)-2;
  for iRank in [0..TheDimension]
  do
    nbOrbit:=Length(eRecordTessel.ListOrbitByRank[iRank+2]);
    Print("iRank=", iRank, "\n");
    for iOrbit in [1..nbOrbit]
    do
      EXT:=eRecordTessel.ListOrbitByRank[iRank+2][iOrbit].EXT;
      ThePermStab:=eRecordTessel.ListOrbitByRank[iRank+2][iOrbit].TheStabPerm;
      TheStab:=eRecordTessel.ListOrbitByRank[iRank+2][iOrbit].TheStab;
      len:=Length(eRecordTessel.ListOrbitByRank[iRank+2][iOrbit].BoundaryImage.ListIFace);
      Print("  iOrbit=", iOrbit, " |EXT|=", Length(EXT), " |stab|=", Order(TheStab), " |stabPerm|=", Order(ThePermStab), " |FAC|=", len, "\n");
    od;
  od;
end;






ConvexVertexClosure:=function(EXTbig, EXTsmall)
  local SetCand, eRec, EXTproj, FACcand, SetCandExt;
  SetCand:=List(EXTsmall, x->Position(EXTbig, x));
  eRec:=ColumnReduction(EXTsmall);
  EXTproj:=List(EXTbig, x->x{eRec.Select});
  FACcand:=DualDescription(EXTproj{SetCand});
  SetCandExt:=Filtered([1..Length(EXTproj)], x->First(FACcand, y->y*EXTproj[x]<0)=fail);
  return EXTbig{SetCandExt};
end;


DetermineMergings:=function(EXT, ListEXTsub, PermGRP)
  local nbSub, eBlock, TotalListSol, eNewSol, eNewTot, eNewSelectCand, eSol, eUnion, eCand, TotalListCand, NewListSol, ListSol, FuncInsertTotalList, testInt, testVol, CheckVolumeNeg, CheckIntersection, FACtot, GetFACunion, eDiff, LCand, eNewCand, test, GRAconn, eVal, HSet, ListForbidden, PermGRPsub, TList, iSub, jSub, NewListCand, IsPresentTotalList, EXTred, rnk, ListVolume, ListPermGens, eInt, eList, ListFAC, eGen, EXTsub, eVol, iOSub, nbOSub, Osub;
  nbSub:=Length(ListEXTsub);
  rnk:=RankMat(EXT);
  EXTred:=ColumnReduction(EXT).EXT;
  ListVolume:=[];
  ListFAC:=[];
  for iSub in [1..nbSub]
  do
    EXTsub:=EXTred{ListEXTsub[iSub]};
    eVol:=VolumeComputationPolytope(EXTsub);
    Add(ListVolume, eVol);
    Add(ListFAC, DualDescription(EXTsub));
  od;
  ListPermGens:=[];
  for eGen in GeneratorsOfGroup(PermGRP)
  do
    eList:=List([1..nbSub], x->Position(ListEXTsub, OnSets(ListEXTsub[x],eGen)));
    Add(ListPermGens, PermList(eList));
  od;
  PermGRPsub:=Group(ListPermGens);
  #
  GRAconn:=NullGraph(Group(()), nbSub);
  for iSub in [1..nbSub-1]
  do
    for jSub in [iSub+1..nbSub]
    do
      eInt:=Intersection(ListEXTsub[iSub], ListEXTsub[jSub]);
      if PersoRankMat(EXT{eInt})=rnk-1 then
        AddEdgeOrbit(GRAconn, [iSub, jSub]);
        AddEdgeOrbit(GRAconn, [jSub, iSub]);
      fi;
    od;
  od;
  Print("We have GRAconn\n");
  #
  TotalListCand:=[];
  FuncInsertTotalList:=function(eCand)
    local fCand;
    for fCand in TotalListCand
    do
      if RepresentativeAction(PermGRPsub, eCand, fCand, OnSets)<>fail then
        return;
      fi;
    od;
    Add(TotalListCand, eCand);
  end;
  IsPresentTotalList:=function(eCand)
    local fCand;
    for fCand in TotalListCand
    do
      if RepresentativeAction(PermGRPsub, eCand, fCand, OnSets)<>fail then
        return true;
      fi;
    od;
    return false;
  end;
  GetFACunion:=function(eCand)
    local EXTtot, FACtot;
    EXTtot:=EXTred{Union(List(eCand, x->ListEXTsub[x]))};
    FACtot:=DualDescription(EXTtot);
    return FACtot;
  end;
  CheckIntersection:=function(ListUnauth, FACtot)
    local FACmerge, TheSpann;
    for jSub in ListUnauth
    do
      FACmerge:=Concatenation(ListFAC[jSub], FACtot);
      TheSpann:=LinearDeterminedByInequalities(FACmerge);
      if Length(TheSpann)=rnk then
        return true;
      fi;
    od;
    return false;
  end;
  CheckVolumeNeg:=function(eCand)
    local EXTtot, eVol, SumVol;
    EXTtot:=EXTred{Union(List(eCand, x->ListEXTsub[x]))};
    eVol:=VolumeComputationPolytope(EXTtot);
    SumVol:=Sum(ListVolume{eCand});
    if SumVol>eVol then
      Error("A priori this is impossible so please debug");
    fi;
    if SumVol=eVol then
      return false;
    fi;
    return true;
  end;
  Osub:=Orbits(PermGRPsub, [1..nbSub], OnPoints);
  nbOSub:=Length(Osub);
  for iOSub in [1..nbOSub]
  do
    iSub:=Osub[iOSub][1];
    Print("iOSub=", iSub, "/", nbOSub, " iSub=", iSub, "\n");
    LCand:=[[iSub]];
    TList:=[];
    while(true)
    do
      Print("  |TList|=", Length(TList), "\n");
      if Length(LCand)=0 then
        break;
      fi;
      NewListCand:=[];
      for eCand in LCand
      do
        Add(TList, eCand);
        ListForbidden:=[];
        for eVal in eCand
        do
          HSet:=Difference(Set(Orbit(PermGRPsub, eVal, OnPoints)), [eVal]);
          ListForbidden:=Union(ListForbidden, HSet);
        od;
        for eVal in Difference([1..nbSub], Union(eCand, ListForbidden))
        do
          if Length(Intersection(Adjacency(GRAconn, eVal), eCand))>0 then
            eNewCand:=Union(eCand, [eVal]);
            FACtot:=GetFACunion(eNewCand);
            test:=CheckIntersection(ListForbidden, FACtot);
            if test=false then
              if IsPresentTotalList(eNewCand)=false then
                Add(NewListCand, eNewCand);
              fi;
            fi;
          fi;
        od;
      od;
      LCand:=NewListCand;
    od;
#    Print("TList=", TList, "\n");
    for eCand in TList
    do
      eDiff:=Difference([1..nbSub], eCand);
      FACtot:=GetFACunion(eCand);
      testInt:=CheckIntersection(eDiff, FACtot);
      testVol:=CheckVolumeNeg(eCand);
      if testInt<>testVol then
        Error("This is unlikely, so please debug");
      fi;
      if testInt=false then
        FuncInsertTotalList(eCand);
      fi;
    od;
    Print("Now |TotalListCand|=", Length(TotalListCand), "\n");
  od;
  Print("Before enum |TotalListCand|=", Length(TotalListCand), "\n");
  ListSol:=Set([ rec(SelectedCand:=[], TotIdx:=[]) ]);
  TotalListSol:=[];
  while(true)
  do
    Print("|ListSol|=", Length(ListSol), "\n");
    if Length(ListSol)=0 then
      break;
    fi;
    NewListSol:=[];
    for eSol in ListSol
    do
      for eCand in TotalListCand
      do
        eUnion:=OrbitUnion(eCand, PermGRPsub);
        if Length(Intersection(eUnion, eSol.TotIdx))=0 then
          eNewSelectCand:=Set(Concatenation(eSol.SelectedCand, [eCand]));
          eNewTot:=Union(eSol.TotIdx, eUnion);
          eNewSol:=rec(SelectedCand:=eNewSelectCand, TotIdx:=eNewTot);
          if Length(eNewTot)=nbSub then
            Add(TotalListSol, eNewSol);
          fi;
          Add(NewListSol, eNewSol);
        fi;
      od;
    od;
    ListSol:=Set(NewListSol);
  od;
  return Set(TotalListSol);
end;


InvarSplitting:=function(TheBound, iRank, iOrbit)
  local EXT, FAC, TheStabPerm, eRec, EXTproj, TheDim, ListMatrGens, eGen, eMat, ListEqua, TheId, DiffMat, NSP, eRec2, eCompl, TheDimBis, TheBasis, EXTprojBis, eEXT, eSol, ListEXTtotalInv, iEXT, pos, eRay, eFACineq, eFACset, eV, GRPmatrBis, ListMatrGensBis, FAClin, FAClinSet, eFACIneq, IsCoxeterSituation, TheCoxeterSubgroup, ListPermPlanes, eElt, EXTprojBisC, EXTprojBisCIrred, EXTprojIrred, EXTprojBisIrred, FACproj, FACprojSets, Oset, ListStabsFac, GetCentralSplittingConvex, GetCentralSplitting, nbFac, MatrixAdjacencies, ListColorsFAC, eMatch, posAdj, eList, eSubset, FACimage, iFace, eFAC, eSet, eBound, EXTimage, lenBound, i, eO, iO, O, GRAfac, eCentFace, ListSubFacs, SumEXT, GetCoxeterInformation, GetVertexOrbitsRepresentationDecomposition, PolyhedralDecomposition, GetPolyhedralNormalizer, ListPermGens, phi, TheStabMatr, TheStab, Ofac, FACsetConv, GRAfacConv, eSetInt, iFacConv, jFacConv, rnkTot, nbFacConv, GRPfacConv, ListPermGensFacConv, FACconv, eFACconv, OfacConv, ListColorFACconv, eRecCoxeter, GetSomeHyperplaneSplitting, GetTotallyInvariantHyperplane, eRecRow, TheStabPermBisIrred, TheStabPermIrred, ListPermGenIrred, TheSelectBisIrred, TheSelectIrred, PreEXTprojBisIrred, Overt, EXTtotInv, ListTotInv, eVert, eRecEXT, LFacIneq, ListRankVertex, rnk, eSetDimReduce, Oirred, ListIncd, Opair, ListCandHyperplaneSplitIrred;
  EXT:=TheBound.ListOrbitByRank[iRank+2][iOrbit].EXT;
  FAC:=TheBound.ListOrbitByRank[iRank+2][iOrbit].FAC;
  if Length(FAC)<>Length(Set(FAC)) then
    Error("FAC is not disjoint");
  fi;
  TheStabPerm:=TheBound.ListOrbitByRank[iRank+2][iOrbit].TheStabPerm;
  TheStab:=TheBound.ListOrbitByRank[iRank+2][iOrbit].TheStab;
  nbFac:=Length(FAC);
  ListColorsFAC:=ListWithIdenticalEntries(nbFac, 0);
  GRAfac:=NullGraph(Group(()), nbFac);
  Ofac:=Orbits(TheStabPerm, FAC, OnSets);
  Overt:=Orbits(TheStabPerm, [1..Length(EXT)], OnPoints);
  for iO in [1..Length(Ofac)]
  do
    eO:=Ofac[iO];
    for eSet in eO
    do
      ListColorsFAC[Position(FAC,eSet)]:=iO;
    od;
  od;
  if iRank>=2 then
    MatrixAdjacencies:=NullMat(nbFac,nbFac);
    eBound:=TheBound.ListOrbitByRank[iRank+2][iOrbit].BoundaryImage;
    lenBound:=Length(eBound.ListIFace);
    for i in [1..lenBound]
    do
      iFace:=eBound.ListIFace[i];
      eElt:=eBound.ListElt[i];
      EXTimage:=TheBound.ListOrbitByRank[iRank+1][iFace].EXT*eElt;
      eList:=List(EXTimage, x->Position(EXT, x));
      eSet:=Set(eList);
      pos:=Position(FAC, eSet);
      FACimage:=TheBound.ListOrbitByRank[iRank+1][iFace].FAC;
      for eFAC in FACimage
      do
        eSubset:=Set(eList{eFAC});
        eMatch:=Filtered([1..nbFac], x->IsSubset(FAC[x],eSubset));
        if Length(eMatch)<>2 then
          Error("eMatch should have length 2");
        fi;
        posAdj:=Difference(eMatch, [pos])[1];
        MatrixAdjacencies[pos][posAdj]:=MatrixAdjacencies[pos][posAdj]+1;
        AddEdgeOrbit(GRAfac, [pos, posAdj]);
      od;
    od;
  else
    MatrixAdjacencies:="unset";
  fi;
  eRec:=ColumnReduction(EXT);
  eRecRow:=RowReduction(EXT);
  EXTproj:=List(EXT, x->x{eRec.Select});
  FAClin:=DualDescription(EXTproj);
  FAClinSet:=List(FAClin, x->Filtered([1..Length(EXTproj)], y->EXTproj[y]*x=0));
  TheDim:=Length(EXTproj[1]);
  ListMatrGens:=[];
  ListPermGens:=GeneratorsOfGroup(TheStabPerm);
  for eGen in ListPermGens
  do
    eMat:=FindTransformation(EXTproj, EXTproj, eGen);
    Add(ListMatrGens, eMat);
  od;
  TheStabMatr:=Group(ListMatrGens);
  phi:=GroupHomomorphismByImagesNC(TheStabPerm, TheStabMatr, ListPermGens, ListMatrGens);
  ListEqua:=[];
  TheId:=IdentityMat(TheDim);
  for eGen in ListMatrGens
  do
    DiffMat:=TransposedMat(eGen)-TheId;
    Append(ListEqua, DiffMat);
  od;
  NSP:=NullspaceMat(TransposedMat(ListEqua));
  eRec2:=ColumnReduction(NSP);
  eCompl:=TheId{Difference([1..TheDim], eRec2.Select)};
  TheDimBis:=Length(eCompl);
  TheBasis:=Concatenation(eCompl, NSP);
  eRecEXT:=ColumnReduction(EXT);
  FACconv:=[];
  LFacIneq:=[];
  for eFAC in FAC
  do
    NSP:=NullspaceMat(TransposedMat(EXT{eFAC}));
    eFACconv:=Filtered([1..Length(EXT)], x->First(NSP, y->EXT[x]*y<>0)=fail);
    Add(FACconv, eFACconv);
    Add(LFacIneq, RemoveFraction(NullspaceMat(TransposedMat(eRecEXT.EXT{eFACconv}))[1]));
  od;
  FACsetConv:=Set(FACconv);
  ListRankVertex:=[];
  for eEXT in eRecEXT.EXT
  do
    ListIncd:=Filtered(LFacIneq, x->x*eEXT=0);
    rnk:=RankMat(ListIncd);
    Add(ListRankVertex, RankMat(LFacIneq) - rnk);
  od;
  ListPermGensFacConv:=[];
  for eGen in GeneratorsOfGroup(TheStabPerm)
  do
    eList:=List(FACsetConv, x->Position(FACsetConv, OnSets(x, eGen)));
    Add(ListPermGensFacConv, PermList(eList));
  od;
  GRPfacConv:=Group(ListPermGensFacConv);
  nbFacConv:=Length(FACsetConv);
  OfacConv:=Orbits(GRPfacConv, [1..nbFacConv], OnPoints);
  ListColorFACconv:=ListWithIdenticalEntries(nbFacConv,0);
  for iO in [1..Length(OfacConv)]
  do
    eO:=OfacConv[iO];
    ListColorFACconv{eO}:=ListWithIdenticalEntries(Length(eO),iO);
  od;
  GRAfacConv:=NullGraph(GRPfacConv, nbFacConv);
  rnkTot:=RankMat(EXT);
  for iFacConv in [1..nbFacConv-1]
  do
    for jFacConv in [iFacConv..nbFacConv]
    do
      eSetInt:=Intersection(FACsetConv[iFacConv], FACsetConv[jFacConv]);
      if Length(eSetInt)> 0 then
        if RankMat(EXT{eSetInt})=rnkTot-2 then
          AddEdgeOrbit(GRAfacConv, [iFacConv, jFacConv]);
          AddEdgeOrbit(GRAfacConv, [jFacConv, iFacConv]);
        fi;
      fi;
    od;
  od;
  GetCoxeterInformation:=function(eGroupPerm)
    local ListMatrGens, ListPermGems, eGen, eMat, eGroupMatr, eRecCoxeter, eVectBas, FACineqCoxeter, FACineqDomain, eSet, eFACineq, EXTprojConv, eEXT, eSol, FACtotal, EXTconv, EXTconvReord, EXTcand, PreSplitting, EXTadmi, pos, EXTprojCand, TheO, TheO2, ListRepresentent, eO2, NewEXT, TheAct, GetSubdomainFromIneq, nbRoot, nbRootHalf, iRootHalf, ListPossPreSplitting, ePreSplitting;
    ListMatrGens:=[];
    ListPermGens:=GeneratorsOfGroup(eGroupPerm);
    for eGen in ListPermGens
    do
      eMat:=FindTransformation(EXTproj, EXTproj, eGen);
      if eMat=fail then
        Error("The input is not correct");
      fi;
      Add(ListMatrGens, eMat);
    od;
    eGroupMatr:=Group(ListMatrGens);
    eRecCoxeter:=DetermineCoxeterNatureFundamentalDomain(eGroupMatr);
    GetSubdomainFromIneq:=function(ListIneq)
      local FACineqNew, eVectBas, FACineqDomain, eSet, eFACineq, FACtotal, EXTprojConv, EXTconv, eEXT, eSol, EXTconvReord, EXTadmi, pos;
      FACineqNew:=[];
      for eVectBas in ListIneq
      do
        Add(FACineqNew, eVectBas);
      od;
      FACineqDomain:=[];
      for eSet in FAC
      do
        eFACineq:=__FindFacetInequality(EXTproj, eSet);
        Add(FACineqDomain, eFACineq);
      od;
      FACtotal:=Concatenation(FACineqNew, FACineqDomain);
      EXTprojConv:=DualDescription(FACtotal);
      EXTconv:=[];
      for eEXT in EXTprojConv
      do
        eSol:=SolutionMat(EXTproj{eRecRow.Select}, eEXT);
        Add(EXTconv, eSol*EXT{eRecRow.Select});
      od;
      EXTconvReord:=List(EXTconv, x->x/x[1]);
      EXTadmi:=[];
      for eEXT in EXT
      do
        pos:=First(FACtotal, x->x*eEXT{eRec.Select}<0);
        if pos=fail then
          Add(EXTadmi, eEXT);
        fi;
      od;
      return Union(Set(EXTconvReord), Set(EXTadmi));
    end;
    if eRecCoxeter.TheBasis<>"unset" then
      TheAct:=function(h, g)
        return Set(h*g);
      end;
      EXTcand:=GetSubdomainFromIneq(eRecCoxeter.TheBasis);
      EXTprojCand:=Set(List(EXTcand, x->x{eRec.Select}));
      TheO:=Orbit(eGroupMatr, EXTprojCand, TheAct);
      TheO2:=Orbits(TheStabMatr, TheO, TheAct);
      ListRepresentent:=[];
      for eO2 in TheO2
      do
        NewEXT:=[];
        for eEXT in eO2[1]
        do
          eSol:=SolutionMat(EXTproj{eRecRow.Select}, eEXT);
          Add(NewEXT, eSol*EXT{eRecRow.Select});
        od;
        Add(ListRepresentent, rec(EXT:=NewEXT));
      od;
      PreSplitting:=rec(iRank:=iRank, iOrbit:=iOrbit,
         ListRepresentent:=ListRepresentent);
      nbRoot:=Length(eRecCoxeter.ListRoot);
      nbRootHalf:=nbRoot/2;
      ListPossPreSplitting:=[];
      for iRootHalf in [1..nbRootHalf]
      do
        EXTcand:=GetSubdomainFromIneq([eRecCoxeter.ListRoot[2*iRootHalf-1]]);
        ePreSplitting:=rec(iRank:=iRank, iOrbit:=iOrbit,
           ListRepresentent:=[rec(EXT:=EXTcand)]);
        Add(ListPossPreSplitting, ePreSplitting);
      od;
    else
      PreSplitting:="unset";
      ListPossPreSplitting:="unset";
    fi;
    return rec(eRecCoxeter:=eRecCoxeter,
               PreSplitting:=PreSplitting,
               ListPossPreSplitting:=ListPossPreSplitting);
  end;
  if TheDimBis>0 then
    EXTprojBis:=[];
    for eEXT in EXTproj
    do
      eSol:=SolutionMat(TheBasis, eEXT);
      Add(EXTprojBis, eSol{[1..TheDimBis]});
    od;
    ListMatrGensBis:=[];
    for eGen in GeneratorsOfGroup(TheStabPerm)
    do
      eMat:=FindTransformation(EXTprojBis, EXTprojBis, eGen);
      Add(ListMatrGensBis, eMat);
    od;
    GRPmatrBis:=Group(ListMatrGensBis);
    eRecCoxeter:=GetCoxeterInformation(TheStabPerm).eRecCoxeter;
    TheCoxeterSubgroup:=eRecCoxeter.TheCoxeterSubgroup;
    IsCoxeterSituation:=eRecCoxeter.IsCoxeterTotal;
  else
    EXTprojBis:="undefined";
    GRPmatrBis:="undefined";
    TheCoxeterSubgroup:="undefined";
    IsCoxeterSituation:="undefined";
  fi;
  ListEXTtotalInv:=[];
  for iEXT in [1..Length(EXT)]
  do
    pos:=First(ListEqua, x->x*EXTproj[iEXT]<>0);
    if pos=fail then
      Add(ListEXTtotalInv, EXT[iEXT]);
    fi;
  od;
  if Length(NSP)=1 then
    eFACset:=FAC[1];
    eFACIneq:=__FindFacetInequality(EXTproj, eFACset);
    if NSP[1]*eFACIneq > 0 then
      eV:=NSP[1];
    else
      eV:=-NSP[1];
    fi;
    eSol:=SolutionMat(EXTproj, eV);
    eRay:=eSol*EXT;
    for eGen in GeneratorsOfGroup(TheBound.ListOrbitByRank[iRank+2][iOrbit].TheStab)
    do
      if eRay*eGen<>eRay then
        Error("Error in the ray generation");
      fi;
    od;
  else
    eV:="unset";
    eSol:="unset";
    eRay:="unset";
  fi;
  EXTprojIrred:=RemoveRedundancyByDualDescription(EXTproj);
  TheSelectIrred:=List(EXTprojIrred, x->Position(EXTproj, x));
  ListPermGenIrred:=[];
  for eGen in GeneratorsOfGroup(TheStabPerm)
  do
    eList:=List(TheSelectIrred, x->Position(TheSelectIrred, OnPoints(x, eGen)));
    Add(ListPermGenIrred, PermList(eList));
  od;
  Oirred:=Orbits(TheStabPerm, TheSelectIrred, OnPoints);
  eSetDimReduce:=[];
  for eO in Oirred
  do
    if Length(eO)>1 then
      eSetDimReduce:=Union(eSetDimReduce, Set(eO));
    fi;
  od;
  TheStabPermIrred:=Group(ListPermGenIrred);
  ListTotInv:=[];
  for eVert in TheSelectIrred
  do
    if Length(Orbit(TheStabPerm, eVert, OnPoints))=1 then
      Add(ListTotInv, eVert);
    fi;
  od;
  EXTtotInv:=Set(EXT{ListTotInv});
  if TheDimBis>0 then
    EXTprojBisC:=List(EXTprojBis, x->Concatenation([1], x));
    EXTprojBisCIrred:=RemoveRedundancyByDualDescription(EXTprojBisC);
    TheSelectBisIrred:=List(EXTprojBisCIrred, x->Filtered([1..Length(EXTprojBisC)], y->EXTprojBisC[y]=x));
    ListPermGenIrred:=[];
    for eGen in GeneratorsOfGroup(TheStabPerm)
    do
      eList:=List(TheSelectBisIrred, x->Position(TheSelectBisIrred, OnSets(x, eGen)));
      Add(ListPermGenIrred, PermList(eList));
    od;
    TheStabPermBisIrred:=Group(ListPermGenIrred);
    PreEXTprojBisIrred:=List(EXTprojBisCIrred,x->EXTprojBis[Position(EXTprojBisC,x)]);
    EXTprojBisIrred:=List(PreEXTprojBisIrred, x->Concatenation([1],x));
    Opair:=Orbits(Group([-IdentityMat(Length(PreEXTprojBisIrred[1]))]), PreEXTprojBisIrred, OnPoints);
    ListCandHyperplaneSplitIrred:=List(Opair, x->x[1]);
    FACproj:=DualDescription(EXTprojBisCIrred);
    FACprojSets:=List(FACproj, y->Filtered([1..Length(EXTprojBis)], x->EXTprojBisC[x]*y=0));
    Oset:=Orbits(TheStabPerm, FACprojSets, OnSets);
    ListSubFacs:=List(FACprojSets, y->Filtered(FAC, x->IsSubset(y,x)));
    # it is possible to have zero sets.
    ListStabsFac:=List(Oset, x->Order(Stabilizer(TheStabPerm, x[1], OnSets)));
  else
    EXTprojBisIrred:="undefined";
    Oset:="undefined";
    FACproj:="undefined";
    FACprojSets:="undefined";
    ListSubFacs:="undefined";
    ListStabsFac:="undefined";
  fi;
  SumEXT:=ListWithIdenticalEntries(TheDim,0);
  for eEXT in EXT
  do
    SumEXT:=SumEXT + eEXT;
  od;
  eCentFace:=SumEXT/Length(EXT);
  #
  GetPolyhedralNormalizer:=function()
    local eSym, eNorm, GRPreturn, ListGens, FuncInsertElt, eElt, eRes;
    eSym:=LinPolytope_Automorphism(EXT);
    eNorm:=Normalizer(eSym, TheStabPerm);
    GRPreturn:=Group(());
    ListGens:=[];
    FuncInsertElt:=function(eElt)
      if eElt in GRPreturn then
        return;
      fi;
      Add(ListGens, eElt);
      GRPreturn:=Group(ListGens);
    end;
    for eElt in eNorm
    do
      eRes:=FindTransformation(EXTproj, EXTproj, eElt);
      if eRes<>fail then
        FuncInsertElt(eElt);
      fi;
    od;
    return GRPreturn;
  end;
  GetCentralSplitting:=function()
    local EXTsing, StabSing, O, ListRepresentent, eOrb, EXT, eCase;
    EXTsing:=TheBound.ListOrbitByRank[iRank+2][iOrbit].EXT;
    StabSing:=TheBound.ListOrbitByRank[iRank+2][iOrbit].TheStabPerm;
    if Length(FAC)<>Length(Set(FAC)) then
      Error("FAC is not disjoint");
    fi;
    O:=Orbits(StabSing, FAC, OnSets);
    Print("|FAC|=", Length(FAC), " |O|=", Length(O), "\n");
    #
    ListRepresentent:=[];
    for eOrb in O
    do
      EXT:=Concatenation(EXTsing{eOrb[1]}, [eCentFace]);
      Add(ListRepresentent, rec(EXT:=EXT, ListRecConv:=[]));
    od;
    eCase:=rec(iRank:=iRank, iOrbit:=iOrbit, ListRepresentent:=ListRepresentent);
#    return eCase;
    return DoClotureOperation(TheBound, eCase);
  end;
  GetCentralSplittingConvex:=function(TheOption)
    local EXTsing, StabSing, O, ListRepresentent, eOrb, EXT, eFAC, NSP, eFACconv, FACconv, SetFACconv, Orelevant, O2, eO2, Lidx, eOrbRepr, eStab, eO, eCase;
    EXTsing:=TheBound.ListOrbitByRank[iRank+2][iOrbit].EXT;
    StabSing:=TheBound.ListOrbitByRank[iRank+2][iOrbit].TheStabPerm;
    if Length(FAC)<>Length(Set(FAC)) then
      Error("FAC is not disjoint");
    fi;
    Print("|FAC|=", Length(FAC), "\n");
    FACconv:=[];
    for eFAC in FAC
    do
      NSP:=NullspaceMat(TransposedMat(EXTsing{eFAC}));
      eFACconv:=Filtered([1..Length(EXTsing)], x->First(NSP, y->EXTsing[x]*y<>0)=fail);
      Add(FACconv, eFACconv);
    od;
    SetFACconv:=Set(FACconv);
    Print("|FAC|=", Length(FAC), " |FACconv|=", Length(FACconv), " |SetFACconv|=", Length(SetFACconv), "\n");
    O:=Orbits(StabSing, SetFACconv, OnSets);
    Print("|O|=", Length(O), "\n");
    Orelevant:=[];
    if TheOption=1 then
      for eO in O
      do
        eStab:=Stabilizer(StabSing, eO[1], OnSets);
        if Order(eStab)=1 then
          Add(Orelevant, eO[1]);
        else
          Lidx:=Filtered([1..Length(FAC)], x->FACconv[x]=eO[1]);
          O2:=Orbits(StabSing, FAC{Lidx}, OnSets);
          for eO2 in O2
          do
            Add(Orelevant, eO2[1]);
          od;
        fi;
      od;
    elif TheOption=2 then
      for eO in O
      do
        Print(" |eO|=", Length(eO), "\n");
        Add(Orelevant, eO[1]);
      od;
    else
      Error("Please put here what you have in mind");
    fi;
    Print("|Orelevant|=", Length(Orelevant), "\n");
    #
    ListRepresentent:=[];
    for eOrbRepr in Orelevant
    do
      EXT:=Concatenation(EXTsing{eOrbRepr}, [eCentFace]);
      Add(ListRepresentent, rec(EXT:=EXT, ListRecConv:=[]));
    od;
    eCase:=rec(iRank:=iRank, iOrbit:=iOrbit, ListRepresentent:=ListRepresentent);
    return eCase;
#    return DoClotureOperation(TheBound, eCase);
  end;
  PolyhedralDecomposition:=function(ListVert)
    local NSP, eSetTot, eStab, ListListColl, ListListFaces, jRank, ListFaces, nbOrbit, iOrbitWork, eRecord, eO, eSet, ListListOrbits, O;
    NSP:=NullspaceMat(TransposedMat(EXT{ListVert}));
    eSetTot:=Filtered([1..Length(EXT)], x->First(NSP, y->y*EXT[x]<>0)=fail);
    eStab:=Stabilizer(TheStabPerm, eSetTot, OnSets);
    ListListColl:=GetCollectionSubfaces(TheBound, iRank, iOrbit);
    ListListFaces:=[];
    for jRank in [0..iRank]
    do
      ListFaces:=[];
      nbOrbit:=Length(ListListColl[jRank+1]);
      for iOrbitWork in [1..nbOrbit]
      do
        eRecord:=ListListColl[jRank+1][iOrbitWork];
        eO:=Orbit(TheStabPerm, eRecord.eSet, OnSets);
        for eSet in eO
        do
          if IsSubset(eSetTot, eSet)=true then
            Add(ListFaces, eSet);
          fi;
        od;
      od;
     Add(ListListFaces, ListFaces);
    od;
    ListListOrbits:=[];
    for jRank in [0..iRank]
    do
      O:=Orbits(eStab, ListListFaces[jRank+1], OnSets);
      ListOrbits:=List(O, x->x[1]);
      Add(ListListOrbits, ListOrbits);
    od;
    return rec(ListVert:=ListVert, eSetTot:=eSetTot, 
               ListListOrbits:=ListListOrbits, 
               ListListFaces:=ListListFaces);
  end;
  GetTotallyInvariantHyperplane:=function(eGroup)
    local ListPosTotInv, TheSet, O, nbO, ListSets, eSol, hSet, iO, rnk, rnkTot, NSP, eVectZero, LPos, EXTcand, PreSplitting, ListPreSplitting, gSet, ListVectZero, ePairPM, LPlus, LMinus, ListSetPair, GetVertexPartition, HyperplaneUnion, ListLPos;
    ListPosTotInv:=List(ListEXTtotalInv, x->Position(EXT,x));
    TheSet:=Difference([1..Length(EXT)], ListPosTotInv);
    O:=Orbits(eGroup, TheSet, OnPoints);
    rnkTot:=RankMat(EXT);
    nbO:=Length(O);
    Print("nbO=", nbO, "\n");
    ListSets:=[];
    for eSol in BuildSet(nbO, [0,1])
    do
      hSet:=[];
      Append(hSet, ListPosTotInv);
      for iO in [1..nbO]
      do
        if eSol[iO]=1 then
          Append(hSet, O[iO]);
        fi;
      od;
      rnk:=RankMat(EXTproj{hSet})+1;
      if rnk=rnkTot then
        NSP:=NullspaceMat(TransposedMat(EXTproj{hSet}));
        eVectZero:=NSP[1];
        gSet:=Filtered([1..Length(EXTproj)], x->EXTproj[x]*eVectZero=0);
        AddSet(ListSets, gSet);
      fi;
    od;
    ListPreSplitting:=[];
    ListVectZero:=[];
    ListSetPair:=[];
    ListLPos:=[];
    HyperplaneUnion:=[];
    for gSet in ListSets
    do
      HyperplaneUnion:=Union(HyperplaneUnion, gSet);
      NSP:=NullspaceMat(TransposedMat(EXTproj{gSet}));
      if Length(NSP)<>1 then
        Error("We have an inconsistency");
      fi;
      eVectZero:=NSP[1];
      Add(ListVectZero, eVectZero);
      LPos:=Filtered([1..Length(EXTproj)], x->EXTproj[x]*eVectZero>=0);
      LPlus:=Filtered([1..Length(EXTproj)], x->EXTproj[x]*eVectZero>0);
      LMinus:=Filtered([1..Length(EXTproj)], x->EXTproj[x]*eVectZero<0);
      Add(ListLPos, LPos);
      ePairPM:=rec(LPlus:=LPlus, LMinus:=LMinus);
      Add(ListSetPair, ePairPM);
      EXTcand:=EXT{LPos};
      PreSplitting:=rec(iRank:=iRank, iOrbit:=iOrbit, LPos:=LPos, 
         ListRepresentent:=[rec(EXT:=EXTcand)]);
      Add(ListPreSplitting, PreSplitting);
    od;
    GetVertexPartition:=function()
      local nbPlane, ListFound, eVect, hSet, i, rSet;
      nbPlane:=Length(ListSets);
      ListFound:=[];
      for eVect in BuildSet(nbPlane, [0,1])
      do
        hSet:=[1..Length(EXT)];
        for i in [1..nbPlane]
        do
          if eVect[i]=0 then
            rSet:=ListSetPair[i].LPlus;
          else
            rSet:=ListSetPair[i].LMinus;
          fi;
          hSet:=Intersection(hSet, rSet);
        od;
        if Length(hSet)>0 then
          Add(ListFound, rec(eVect:=eVect, hSet:=hSet));
        fi;
      od;
      return ListFound;
    end;
    return rec(ListPreSplitting:=ListPreSplitting, 
               HyperplaneUnion:=HyperplaneUnion, 
               ListSets:=ListSets,
               ListLPos:=ListLPos,
               ListSetPair:=ListSetPair, 
               GetVertexPartition:=GetVertexPartition,
               ListVectZero:=ListVectZero);
  end;
  GetSomeHyperplaneSplitting:=function()
    local rnk1, rnk2, ListPosTotInv, TheSet, ListGroup, NSP, eVal, TheFilt, eVectZero, ListPreSplitting, LPos, EXTcand, PreSplitting, eGroup;
    rnk1:=RankMat(ListEXTtotalInv)+2;
    rnk2:=RankMat(EXT);
    if rnk1<>rnk2 then
      Print("Further work is needed\n");
      Error("Please program some more");
    fi;
    ListPosTotInv:=List(ListEXTtotalInv, x->Position(EXT,x));
    TheSet:=Difference([1..Length(EXT)], ListPosTotInv);
    ListGroup:=[];
    while(true)
    do
      if Length(TheSet)=0 then
        break;
      fi;
      eVal:=TheSet[1];
      NSP:=NullspaceMat(TransposedMat(EXTproj{Concatenation(ListPosTotInv, [eVal])}));
      if Length(NSP)<>1 then
        Error("We have an inconsistency");
      fi;
      eVectZero:=NSP[1];
      TheFilt:=Filtered(TheSet, x->EXTproj[x]*eVectZero=0);
      if Position(TheFilt, eVal)=fail then
        Error("Please debug from here");
      fi;
      Add(ListGroup, TheFilt);
      TheSet:=Difference(TheSet, TheFilt);
    od;
    ListPreSplitting:=[];
    for eGroup in ListGroup
    do
      NSP:=NullspaceMat(TransposedMat(EXTproj{Concatenation(ListPosTotInv, eGroup)}));
      if Length(NSP)<>1 then
        Error("We have an inconsistency");
      fi;
      eVectZero:=NSP[1];
      LPos:=Filtered([1..Length(EXTproj)], x->EXTproj[x]*eVectZero>=0);
      EXTcand:=EXT{LPos};
      PreSplitting:=rec(iRank:=iRank, iOrbit:=iOrbit,
         ListRepresentent:=[rec(EXT:=EXTcand)]);
      Add(ListPreSplitting, PreSplitting);
    od;
    return rec(ListPreSplitting:=ListPreSplitting);
  end;
  GetVertexOrbitsRepresentationDecomposition:=function(eGroup)
    local eLocalGroup, CJ, tbl, eIrr, nbChar, eMatrix, iChar, iCJ, O, ListInfos, eO, EXTstl, eBasis, len, ListTraces, eRepr, eMat, eVect, pos, posImg, eSol, eTrace, eSolTrace, eRecInfo, ListMatrGens, GRPmatr, ListSpacesRepresentation, eSumProj, PreSumProj, eChar, eCJ, eDim, ListProjector, ListNSP, ListGRPind, eNSP, GRPind, jChar, eMatGen, ListMultiplicity, SignatureMultiplicity, eMultiplicity;
    eLocalGroup:=PersoGroupPerm(GeneratorsOfGroup(eGroup));
    CJ:=ConjugacyClasses(eLocalGroup);
    SetConjugacyClasses(eLocalGroup, CJ);
    tbl:=CharacterTable(eLocalGroup);
    eIrr:=Irr(tbl);
    nbChar:=Length(eIrr);
    eMatrix:=NullMat(nbChar, nbChar);
    for iChar in [1..nbChar]
    do
      for iCJ in [1..nbChar]
      do
        eMatrix[iChar][iCJ]:=eIrr[iChar][iCJ];
      od;
    od;
    ListProjector:=[];
    ListMultiplicity:=[];
    ListNSP:=[];
    ListGRPind:=[];
    for iChar in [1..nbChar]
    do
      eChar:=eIrr[iChar];
      eCJ:=ConjugacyClass(eLocalGroup, ());
      pos:=Position(CJ, eCJ);
      eDim:=eChar[pos];
      PreSumProj:=NullMat(TheDim, TheDim);
      for eElt in eLocalGroup
      do
        eCJ:=ConjugacyClass(eLocalGroup, eElt);
        pos:=Position(CJ, eCJ);
        eMat:=Image(phi, eElt);
        PreSumProj:=PreSumProj+eMat*ComplexConjugate(eChar[pos]);
      od;
      eSumProj:=PreSumProj*(eDim/Order(eLocalGroup));
      if eSumProj<>eSumProj*eSumProj then
        Error("It is not a projector apparently, please debug");
      fi;
      DiffMat:=eSumProj-IdentityMat(TheDim);
      NSP:=NullspaceMat(DiffMat);
      if Length(NSP)>0 then
        ListMatrGens:=[];
        for eGen in GeneratorsOfGroup(eLocalGroup)
        do
          eMatGen:=Image(phi, eGen);
          eMat:=[];
          for eNSP in NSP
          do
            Add(eMat, SolutionMat(NSP, eNSP*eMatGen));
          od;
          Add(ListMatrGens, eMat);
        od;
        ListTraces:=[];
        for iCJ in [1..nbChar]
        do
          eRepr:=Representative(CJ[iCJ]);
          eMatGen:=Image(phi, eRepr);
          eMat:=List(NSP, x->SolutionMat(NSP, x*eMatGen));
          eTrace:=Trace(eMat);
          Add(ListTraces, eTrace);
        od;
        eSolTrace:=SolutionMat(eMatrix, ListTraces);
        if eSolTrace{Difference([1..nbChar], [iChar])}<>ListWithIdenticalEntries(nbChar-1,0) then
          Error("The projection was apparently not done correctly");
        fi;
        eMultiplicity:=eSolTrace[iChar];
        GRPind:=Group(ListMatrGens);
      else
        eMultiplicity:=0;
        GRPind:="unset";
      fi;
      Add(ListProjector, eSumProj);
      Add(ListMultiplicity, eMultiplicity);
      Add(ListGRPind, GRPind);
      Add(ListNSP, NSP);
    od;
    ListTraces:=[];
    for iCJ in [1..nbChar]
    do
      eRepr:=Representative(CJ[iCJ]);
      eMatGen:=Image(phi, eRepr);
      eTrace:=Trace(eMatGen);
      Add(ListTraces, eTrace);
    od;
    SignatureMultiplicity:=SolutionMat(eMatrix, ListTraces);
    if SignatureMultiplicity<>ListMultiplicity then
      Error("Inconsistency in computation of multiplicities");
    fi;
    for iChar in [1..nbChar]
    do
      for jChar in [1..nbChar]
      do
        if iChar<>jChar then
          if ListProjector[iChar]*ListProjector[jChar]<>NullMat(TheDim,TheDim) then
            Error("The system of projectors should sum to zero");
          fi;
        fi;
      od;
    od;
    O:=Orbits(eLocalGroup, [1..Length(EXT)], OnPoints);
    ListInfos:=[];
    for eO in O
    do
      EXTstl:=EXT{eO};
      eBasis:=RowReduction(EXTstl).EXT;
      len:=Length(eBasis);
      ListTraces:=[];
      ListMatrGens:=[];
      for iCJ in [1..nbChar]
      do
        eRepr:=Representative(CJ[iCJ]);
        eMat:=[];
        for eVect in eBasis
        do
          pos:=Position(EXT, eVect);
          posImg:=OnPoints(pos, eRepr);
          eSol:=SolutionMat(eBasis, EXT[posImg]);
          Add(eMat, eSol);
        od;
        eTrace:=Trace(eMat);
        Add(ListTraces, eTrace);
        Add(ListMatrGens, eMat);
      od;
      eSolTrace:=SolutionMat(eMatrix, ListTraces);
      GRPmatr:=Group(ListMatrGens);
      eRecInfo:=rec(DimSpann:=len, eO:=eO, eIrredDecomp:=eSolTrace,
                    GRPmatr:=GRPmatr);
      Add(ListInfos, eRecInfo);
    od;
    return rec(ListInfos:=ListInfos, 
               ListProjector:=ListProjector,
               ListMultiplicity:=ListMultiplicity, 
               ListGRPind:=ListGRPind,
               ListNSP:=ListNSP,
               CJ:=CJ, eIrr:=eIrr);
  end;
  return rec(eRay:=eRay, 
             eV:=eV, 
             eSol:=eSol, 
             Overt:=Overt,
             ListCandHyperplaneSplitIrred:=ListCandHyperplaneSplitIrred,
             MatrixAdjacencies:=MatrixAdjacencies,
             GRAfacConv:=GRAfacConv,
             FACsetConv:=FACsetConv, 
             GRAfac:=GRAfac,
             TheStab:=TheStab, 
             TheStabPerm:=TheStabPerm,
             TheStabPermIrred:=TheStabPermIrred,
             TheStabPermBisIrred:=TheStabPermBisIrred,
             TheSelectIrred:=TheSelectIrred,
             TheSelectBisIrred:=TheSelectBisIrred,
             ListRankVertex:=ListRankVertex, 
             eSetDimReduce:=eSetDimReduce, 
             NSP:=NSP, 
             EXTproj:=EXTproj,
             EXTprojIrred:=EXTprojIrred,
             EXT:=EXT,
             FACset:=FAC, 
             FAClin:=FAClin, 
             FAClinSet:=FAClinSet, 
             EXTprojBis:=EXTprojBis, 
             EXTprojBisIrred:=EXTprojBisIrred, 
             EXTprojIrred:=EXTprojIrred,
             PreEXTprojBisIrred:=PreEXTprojBisIrred,
             FACproj:=FACproj,
             GetVertexOrbitsRepresentationDecomposition:=GetVertexOrbitsRepresentationDecomposition,
             GetPolyhedralNormalizer:=GetPolyhedralNormalizer,
             Ofac:=Ofac, 
             ListColorsFAC:=ListColorsFAC,
             ListColorFACconv:=ListColorFACconv, 
             FACprojSets:=FACprojSets,
             Oset:=Oset,
             ListSubFacs:=ListSubFacs,
             ListStabsFac:=ListStabsFac,
             GRPmatrBis:=GRPmatrBis, 
             GetCoxeterInformation:=GetCoxeterInformation, 
             eCentFace:=eCentFace, 
             TheCoxeterSubgroup:=TheCoxeterSubgroup,
             IsCoxeterSituation:=IsCoxeterSituation, 
             GetCentralSplitting:=GetCentralSplitting, 
             GetCentralSplittingConvex:=GetCentralSplittingConvex,
             GetSomeHyperplaneSplitting:=GetSomeHyperplaneSplitting,
             GetTotallyInvariantHyperplane:=GetTotallyInvariantHyperplane,
             PolyhedralDecomposition:=PolyhedralDecomposition,
             ListEXTtotalInv:=ListEXTtotalInv);
end;



DoAllComputations_Perf_Complex_Matrix_SNF:=function(eCaseGen2, SavingPrefix)
  local TheFileSavePerf, TheFileSaveRecMatrix, TheFileSaveHomolDual, TheFileSaveBoundDual, TheRES, TheTessel1, kLevel, eRecIAI, TheBoundDual, RecMatrix, RecOptionDual, DoCoho, TheFileSaveCoho, ListCoho, GetCoho, GetBoundDual, PrintResult, PrintLatexResult, GetMatrices;
  TheFileSaveCoho :=Concatenation(SavingPrefix, "Coho");
  TheFileSavePerf :=Concatenation(SavingPrefix, "Perf");
  TheFileSaveRecMatrix:=Concatenation(SavingPrefix, "RecMatrix");
  TheFileSaveHomolDual:=Concatenation(SavingPrefix, "HomolDual");
  TheFileSaveBoundDual:=Concatenation(SavingPrefix, "BoundDual");
  RecOptionDual:=rec(DoRetracted:=false);
  RemoveFileIfExist(TheFileSaveRecMatrix);
  if IsExistingFilePlusTouch(TheFileSaveRecMatrix)=false then
    #
    TheRES:=Kernel_GetEnumerationPerfectForm(eCaseGen2);
    TheTessel1:=TheRES.TheTesselation;
    SaveDataToFilePlusTouch(TheFileSavePerf, TheTessel1);
    #
    kLevel:=Length(eCaseGen2.Basis);
    eRecIAI:=TheRES.eRecIAIdual;
    #
    TheBoundDual:=GetBoundaryDual_CohomologySequenceStyle(TheTessel1, TheRES.FuncDoRetractionDirect, eRecIAI, RecOptionDual);
#    CheckCohomologyVanishingBoundaries(TheBoundDual);
    SaveDataToFilePlusTouch(TheFileSaveBoundDual, TheBoundDual.ListOrbitByRank);
    #
    RecMatrix:=KillFacesWithOrientationReversing_CohomologyKernel(TheBoundDual);
    SaveDataToFilePlusTouch(TheFileSaveRecMatrix, RecMatrix);
    #
    ListCoho:=GettingCohomologyFromSparseMatrices(RecMatrix.ListMat);
    SaveDataToFilePlusTouch(TheFileSaveCoho, ListCoho);
  fi;
  GetBoundDual:=function()
    return ReadAsFunction(TheFileSaveBoundDual)();
  end;
  GetCoho:=function()
    return ReadAsFunction(TheFileSaveCoho)();
  end;
  GetMatrices:=function()
    return ReadAsFunction(TheFileSaveRecMatrix)();
  end;
  PrintResult:=function(output)
    local ListOrbitByRank, len, i, nbOrbit, nbOrbitOri, ListCoho, eHom;
    ListOrbitByRank:=GetBoundDual();
    len:=Length(ListOrbitByRank);
    for i in [2..len]
    do
      nbOrbit:=Length(ListOrbitByRank[i]);
      nbOrbitOri:=Length(Filtered(ListOrbitByRank[i], x->x.IsOrientable=true));
      if nbOrbit>0 then
        AppendTo(output, "dim=", i-2, " nbOrb=", nbOrbit, " nbOrbOri=", nbOrbitOri, "\n");
      fi;
    od;
    #
    ListCoho:=GetCoho().ListCOHO;
    len:=Length(ListCoho);
    for i in [1..len]
    do
      eHom:=ListCoho[i];
      AppendTo(output, "H_", i, "(G)=");
      PrintHomologyGroup(output, eHom);
      AppendTo(output, "\n");
    od;
  end;
  PrintLatexResult:=function(output)
    local n, iLevel, kLevel, TheCoho, TheBound, jPos, nbOrbit, ListStabSize, eVal, eFact, fEnt, eStr, eColl, ListStrCoho, ListStrElemDiv, eRank, iLineTable, nbLineTable, nbOrbitOri, eOrbit, eSize, eMult, ListStr, nbEntPerLine, ListStrBlockStabSize, eStrStabSize, eStrElemDiv, eEnt, nbEnt, OmegaSize, eStrElem, ListStrElem, nbEntPerLineB, TheGlobalStabGroup, eOrd, eStabSize;
    AppendTo(output, "\\begin{table}[htb]\n");
    AppendTo(output, "\\begin{tabular}{|c||c|c||c|c|c|c||r|}\n");
    AppendTo(output, "\\hline\n");
    AppendTo(output, "\$n\$  &  \$|\\Sigma^{*}_{n}|\$  &  \$|\\Stab|\$  &  \$|\\Sigma_{n}|\$  &  \$\\Omega\$  &  \$\\rank\$  &  elem.~div.  &  \$H_{n}\$ \\\\\n");
    TheCoho:=GetCoho();
#    Print(NullMat(5));
    TheBound:=GetBoundDual();
    kLevel:=Length(TheBound);
    TheGlobalStabGroup:=FindFullSymmetrySpace(eCaseGen2);
    eOrd:=Order(TheGlobalStabGroup);
    for iLevel in [0..kLevel-1]
    do
      jPos:=kLevel - iLevel;
      nbOrbit:=Length(TheBound[jPos]);
      if nbOrbit>0 then
        nbOrbitOri:=Length(Filtered(TheBound[jPos], x->x.IsOrientable));
        ListStabSize:=[];
        for eOrbit in TheBound[jPos]
        do
          eSize:=Order(eOrbit.TheStab); # This needs to be corrected to get same size as in 
                                        # the paper
          eStabSize:=eSize*eOrd;
          Add(ListStabSize, eStabSize);
        od;
        eColl:=Collected(ListStabSize);
        ListStr:=[];
        for eEnt in eColl
        do
          eMult:=eEnt[2];
          eVal:=eEnt[1];
          eFact:=FactorsInt(eVal);
          eStr:="\$";
          for fEnt in Collected(eFact)
          do
            eStr:=Concatenation(eStr, String(fEnt[1]), "^{", String(fEnt[2]), "}");
          od;
          eStr:=Concatenation(eStr, "(", String(eMult), ")\$");
          Add(ListStr, eStr);
        od;
        nbEnt:=Length(eColl);
        nbEntPerLine:=4;
        ListStrBlockStabSize:=STRING_SplittingByBlock(ListStr, nbEntPerLine);
        #
        ListStrElem:=[];
        for eEnt in Collected(TheCoho.ListElemDiv[jPos])
        do
          eMult:=eEnt[2];
          eVal:=eEnt[1];
          eStrElem:=Concatenation(String(eVal), "(", String(eMult), ")");
          Add(ListStrElem, eStrElem);
        od;
        nbEntPerLineB:=2;
        ListStrElemDiv:=STRING_SplittingByBlock(ListStrElem, nbEntPerLineB);
        #
        OmegaSize:=TheCoho.ListNNZ[jPos];
        eRank:=TheCoho.ListRankMat[jPos];
        AppendTo(output, "\\hline\n");
        nbLineTable:=Maximum(Length(ListStrBlockStabSize), Length(ListStrElemDiv));
        AppendTo(output, iLevel, " & ", nbOrbit, " & ", ListStrBlockStabSize[1], " & ", nbOrbitOri, " & ", OmegaSize, " & ", eRank, " & ", ListStrElemDiv[1], " & \$", TheCoho.ListCOHObis[jPos], "\$  \\\\\n");
        for iLineTable in [2..nbLineTable]
        do
          if iLineTable <= Length(ListStrBlockStabSize) then
            eStrStabSize:=ListStrBlockStabSize[iLineTable];
          else
            eStrStabSize:="";
          fi;
          if iLineTable <= Length(ListStrElemDiv) then
            eStrElemDiv:=ListStrElemDiv[iLineTable];
          else
            eStrElemDiv:="";
          fi;
          AppendTo(output, " & ", " & ", eStrStabSize, " & ", " & ", " & ", " & ", eStrElemDiv, " & ", "\\\\\n");
        od;
      fi;
    od;
    AppendTo(output, "\\hline\n");
    AppendTo(output, "\\end{tabular}\n");
    AppendTo(output, "\\end{table}\n");
  end;
  return rec(GetBoundDual:=GetBoundDual,
             GetCoho:=GetCoho,
             GetMatrices:=GetMatrices, 
             PrintResult:=PrintResult,
             PrintLatexResult:=PrintLatexResult);
end;
