EquivariantSearchDualDescription:=function(EXT, PermGRP)
  local ListEnt, ListInv, EXTred, TheDim, nbVert, ScalarMat, eLine, FuncInsert, ComputeForSpecificGroup, GetListEnt, FuncInv, ComputeKeyInformation_EXT, ComputeKeyInformation_GRP, MapSpecificGroupOrbits, eTool;
  EXTred:=ColumnReduction(EXT).EXT;
  TheDim:=Length(EXTred[1]);
  nbVert:=Length(EXTred);
  eTool:=VectorConfiguration_Invariant_GetTools(EXTred, nbVert);
  FuncInv:=function(eInc)
    return VectorConfiguration_Invariant_ComputeAdvanced(eTool, eInc);
  end;
  ListEnt:=[];
  ListInv:=[];
  FuncInsert:=function(eEnt)
    local len, eInv, i, test;
    len:=Length(ListEnt);
    eInv:=FuncInv(eEnt);
    for i in [1..len]
    do
      if eInv=ListInv[i] then
        test:=RepresentativeAction(PermGRP, eEnt, ListEnt[i], OnSets);
	if test<>fail then
	  return;
	fi;
      fi;
    od;
    Add(ListEnt, eEnt);
    Add(ListInv, eInv);
  end;
  ComputeKeyInformation_EXT:=function(eGRP)
    local ListMatrGen, eGen, eMatr, ListEqua, DiffMat, NSP, dimNSP, EXTproj, O, Oset, nbO, eO, iO, eVect, eSol, PreEXTproj, Ofinal, eEXT;
    ListMatrGen:=[];
    for eGen in GeneratorsOfGroup(eGRP)
    do
      eMatr:=FindTransformation(EXTred,EXTred,eGen);
      Add(ListMatrGen, eMatr);
    od;
    ListEqua:=[];
    for eMatr in ListMatrGen
    do
      DiffMat:=TransposedMat(eMatr)-IdentityMat(TheDim);
      Append(ListEqua, DiffMat);
    od;
    NSP:=NullspaceMat(TransposedMat(ListEqua));
    dimNSP:=Length(NSP);
    O:=Orbits(eGRP, [1..nbVert], OnPoints);
    Oset:=List(O, Set);
    nbO:=Length(Oset);
    PreEXTproj:=[];
    for eO in Oset
    do
      eVect:=Sum(EXTred{eO});
      eSol:=SolutionMat(NSP, eVect);
      Add(PreEXTproj, eSol);
    od;
    EXTproj:=Set(PreEXTproj);
    Ofinal:=[];
    for eEXT in EXTproj
    do
      eO:=[];
      for iO in [1..nbO]
      do
        if PreEXTproj[iO] = eEXT then
          Append(eO, Oset[iO]);
        fi;
      od;
      Add(Ofinal, Set(eO));
    od;
    if RankMat(EXTproj)<>dimNSP then
      Error("This should not happen");
    fi;
    return rec(O:=Ofinal, EXT:=EXTproj);
  end;
  ComputeKeyInformation_GRP:=function(KeyEXT, eGRP)
    local eNorm, ListPermProj, eGen, eList, iO, eO, nbO, eOimg, posO, eGenProj;
    eNorm:=Normalizer(PermGRP, eGRP);
    ListPermProj:=[];
    nbO:=Length(KeyEXT.O);
    for eGen in GeneratorsOfGroup(eNorm)
    do
      eList:=[];
      for iO in [1..nbO]
      do
        eO:=KeyEXT.O[iO];
        eOimg:=OnSets(eO, eGen);
        posO:=Position(KeyEXT.O, eOimg);
        Add(eList, posO);
      od;
      eGenProj:=PermList(eList);
      Add(ListPermProj, eGenProj);
    od;
    return Group(ListPermProj);
  end;
  MapSpecificGroupOrbits:=function(KeyEXT, KeyGRP, ListOrb)
    local ListOrbTot, eOrb, hVect, eVal, eOrbTot;
    ListOrbTot:=[];
    for eOrb in ListOrb
    do
      hVect:=ListWithIdenticalEntries(nbVert,0);
      for eVal in eOrb
      do
        hVect{KeyEXT.O[eVal]}:=ListWithIdenticalEntries(Length(KeyEXT.O[eVal]), 1);
      od;
      eOrbTot:=Filtered([1..nbVert], x->hVect[x]=1);
      if RankMat(EXTred{eOrbTot}) = TheDim-1 then
        Add(ListOrbTot, eOrbTot);
      fi;
    od;
    return ListOrbTot;
  end;
  GetListEnt:=function();
    return ListEnt;
  end;
  return rec(GetListEnt:=GetListEnt,
             FuncInsert:=FuncInsert,
             ComputeKeyInformation_EXT:=ComputeKeyInformation_EXT,
             ComputeKeyInformation_GRP:=ComputeKeyInformation_GRP,
	     MapSpecificGroupOrbits:=MapSpecificGroupOrbits);
end;



SearchSymmetricFacet:=function(eCase, RecOpt)
  local PrefixSave, eComm, EXT, FileSave, PermGRP, ListGRP_CJ, CJ, ListGRP_CJ2, CJ2, ListGRP_CJtot, GetOrbitDualDescription, RetrieveListOrbit, ListCasesDone, iCJ, eCJ, NeedCompute, ESDD, KeyGRP, KeyEXT, nbSubcase, ListOrbitRaw, ListOrbSma, ListOrbFound, eOrbRaw, nbCaseDone, Key_NbVert, Key_rank, Key_grp, RecRead, RecWrite;
  #
  PrefixSave:=eCase.PrefixSave;
  eComm:=Concatenation("mkdir -p ", PrefixSave);
  Exec(eComm);
  Print("Directory created\n");
  #
  EXT:=eCase.EXT;
  Print("We have EXT |EXT|=", Length(EXT), " rank(EXT)=", RankMat(EXT), "\n");
  #
  FileSave:=Concatenation(PrefixSave, "PermGRP");
  if IsExistingFilePlusTouch(FileSave) then
    PermGRP:=ReadAsFunction(FileSave)();
  else
    PermGRP:=LinPolytope_Automorphism(EXT);
    SaveDataToFilePlusTouch(FileSave, PermGRP);
  fi;
  Print("|PermGRP|=", Order(PermGRP), "\n");
  #
  FileSave:=Concatenation(PrefixSave, "ListGRP_CJ");
  if IsExistingFilePlusTouch(FileSave) then
    ListGRP_CJ:=ReadAsFunction(FileSave)();
  else
    CJ:=ConjugacyClasses(PermGRP);
    ListGRP_CJ:=List(CJ, x->Group([Representative(x)]));
    SaveDataToFilePlusTouch(FileSave, ListGRP_CJ);
  fi;
  Print("|ListGRP_CJ|=", Length(ListGRP_CJ), "\n");
  #
  if RecOpt.ConjClassGroup then
    FileSave:=Concatenation(PrefixSave, "ListGRP_CJ2");
    if IsExistingFilePlusTouch(FileSave) then
      ListGRP_CJ2:=ReadAsFunction(FileSave)();
    else
      CJ2:=ConjugacyClassesSubgroups(PermGRP);
      ListGRP_CJ2:=List(CJ2, x->Representative(x));
      SaveDataToFilePlusTouch(FileSave, ListGRP_CJ2);
    fi;
  else
    ListGRP_CJ2:=[];
  fi;
  Print("|ListGRP_CJ2|=", Length(ListGRP_CJ2), "\n");
  #
  ListGRP_CJtot:=Concatenation(ListGRP_CJ, ListGRP_CJ2);
  nbSubcase:=Length(ListGRP_CJtot);
  Print("|ListGRP_CJtot|=", nbSubcase, "\n");
  #
  ESDD:=EquivariantSearchDualDescription(EXT, PermGRP);
  #
  ListCasesDone:=[];
  nbCaseDone:=0;
  while(true)
  do
    FileSave:=Concatenation(PrefixSave, "DualDesc_", String(nbCaseDone+1));
    if IsExistingFilePlusTouch(FileSave)=false then
      break;
    fi;
    nbCaseDone:=nbCaseDone+1;
    Add(ListCasesDone, ReadAsFunction(FileSave)());
  od;
  GetOrbitDualDescription:=function(EXTse, GRPse)
    local eCaseDone, test, ListOrb, TheRecord, FileSaveDD, idxCase, ThePathWork;
    for eCaseDone in ListCasesDone
    do
      test:=LinPolytope_Isomorphism(eCaseDone.EXT, EXTse);
      if test<>false then
        ListOrb:=List(eCaseDone.ListOrb, x->OnSets(x, test));
	return ListOrb;
      fi;
    od;
    idxCase:=Length(ListCasesDone) + 1;
    ThePathWork:=Concatenation(PrefixSave, "TheWork_", String(idxCase), "/");
    ListOrb:=RecOpt.DualDescriptionFunction(EXTse, GRPse, ThePathWork);
    TheRecord:=rec(EXT:=EXTse, ListOrb:=ListOrb);
    Add(ListCasesDone, TheRecord);
    FileSaveDD:=Concatenation(PrefixSave, "DualDesc_", String(idxCase));
    SaveDataToFilePlusTouch(FileSaveDD, TheRecord);
    return ListOrb;
  end;
  RetrieveListOrbit:=function(eKeyEXT, eKeyGRP)
    local GRPcomplete, BoundingSet, eRecRedund, EXTirr, ListOrb1, ListOrb2, eOrb1, eOrb2, ListOrb3, ListOrb4;
    GRPcomplete:=LinPolytope_Automorphism(eKeyEXT.EXT);
    Print("We have GRPcomplete\n");
    BoundingSet:=[];
    eRecRedund:=EliminationByRedundancyEquivariant(eKeyEXT.EXT, [], GRPcomplete);
    Print("We have eRecRedund\n");
    EXTirr:=eKeyEXT.EXT{eRecRedund.eSetSelect};
    #
    ListOrb1:=GetOrbitDualDescription(EXTirr, eRecRedund.PermGRPred);
    Print("We have ListOrb1\n");
    #
    ListOrb2:=[];
    for eOrb1 in ListOrb1
    do
      eOrb2:=eRecRedund.eSetSelect{eOrb1};
      Add(ListOrb2, eOrb2);
    od;
    Print("We have ListOrb2\n");
    #
    if Order(GRPcomplete)=Order(eKeyGRP) then
      ListOrb3:=ListOrb2;
    else
      ListOrb3:=[];
      for eOrb2 in ListOrb2
      do
        Append(ListOrb3, __IndividualLifting(eOrb2, eKeyGRP, GRPcomplete));
      od;
    fi;
    Print("We have ListOrb3\n");
    #
    ListOrb4:=ESDD.MapSpecificGroupOrbits(eKeyEXT, eKeyGRP, ListOrb3);
    Print("We have ListOrb4\n");
    #
    return ListOrb4;
  end;
  #
  ListOrbitRaw:=[];
  for iCJ in [1..nbSubcase]
  do
    eCJ:=ListGRP_CJtot[iCJ];
    Print("iCJ=", iCJ, " / ", nbSubcase, "   |eCJ|=", Order(eCJ), "\n");
    KeyEXT:=ESDD.ComputeKeyInformation_EXT(eCJ);
    KeyGRP:=ESDD.ComputeKeyInformation_GRP(KeyEXT, eCJ);
    NeedCompute:=false;
    Key_NbVert:=Length(KeyEXT.EXT);
    Key_rank:=RankMat(KeyEXT.EXT);
    Key_grp:=Order(KeyGRP);
    Print("   |KeyEXT.EXT|=", Key_NbVert, " rank(KeyEXT.EXT)=", Key_rank, " |KeyGRP|=", Key_grp, "\n");
    if Key_rank >= 2 then
      if RecOpt.IsAdmissible(Key_NbVert, Key_rank, Key_grp) then
        NeedCompute:=true;
      fi;
    fi;
    #
    FileSave:=Concatenation(PrefixSave, "ListOrbit_", String(iCJ));
    if NeedCompute then
      if IsExistingFilePlusTouch(FileSave) then
        ListOrbSma:=ReadAsFunction(FileSave)();
      else
        ListOrbSma:=RetrieveListOrbit(KeyEXT, KeyGRP);
        SaveDataToFilePlusTouch(FileSave, ListOrbSma);
      fi;
      Append(ListOrbitRaw, ListOrbSma);
    else
      if IsExistingFilePlusTouch(FileSave) then
        Append(ListOrbitRaw, ReadAsFunction(FileSave)());
      fi;
    fi;
    #
  od;
  Print("All considered cases have been computed |ListOrbitRaw|=", Length(ListOrbitRaw), "\n");
  #
  FileSave:=Concatenation(PrefixSave, "ListOrbitFound");
  NeedCompute:=false;
  if IsExistingFilePlusTouch(FileSave)=false then
    NeedCompute:=true;
  else
    RecRead:=ReadAsFunction(FileSave)();
    if RecRead.nbOrbitRaw<>Length(ListOrbitRaw) then
      NeedCompute:=true;
    else
      ListOrbFound:=RecRead.ListOrbFound;
    fi;
  fi;
  if NeedCompute then
    for eOrbRaw in ListOrbitRaw
    do
      ESDD.FuncInsert(eOrbRaw);
    od;
    ListOrbFound:=ESDD.GetListEnt();
    Print("|ListOrbFound|=", Length(ListOrbFound), "\n");
    RecWrite:=rec(nbOrbitRaw:=Length(ListOrbitRaw), ListOrbFound:=ListOrbFound);
    SaveDataToFilePlusTouch(FileSave, RecWrite);
  fi;
  return rec(GRP:=PermGRP, nbSubcase:=nbSubcase, ListOrbFound:=ListOrbFound);
end;












RepresentationMatrixAndFacetStandard:=function(EXT, PermGRP)
  local WorkingDim, FuncStabilizer, FuncIsomorphy, FuncGetIndex, FuncInvariant, BF, GetRecord, TmpDir, DataPolyhedral, TheGEN, ListOrbit, TheRepresentationMatrix, IsFinished, nbOrbit, iOrbit, NewData, RPLift, Ladj, eInc, idx, eRedStab, nbAdj, GetDiagMatrix, ListRepresentatives, ListIncidence, ListStabOrder, ListOrbSize, DMat, DiscriminantList, eReordPerm, ReordListRepresentatives, ReordDiscriminantList, ReordListOrbSize, ReordDMat, ReordRepresentationMatrix, IsBankSave, IsRespawn;
  WorkingDim:=RankMat(EXT);
  #
  FuncStabilizer:=function(EXTask)
    local GRP, ListGen, eGen, ListInc;
    ListInc:=List(EXTask, x->Position(EXT, x));
    if Length(ListInc) < WorkingDim+5 then
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
    local ePerm, ListInc1, ListInc2;
    if Length(EXT1)<>Length(EXT2) then
      return false;
    fi;
    ListInc1:=List(EXT1, x->Position(EXT, x));
    ListInc2:=List(EXT2, x->Position(EXT, x));
    ePerm:=RepresentativeAction(PermGRP, ListInc1, ListInc2, OnSets);
    if ePerm=fail then
      return false;
    else
      return PermList(List(ListInc1, x->Position(ListInc2, OnPoints(x, ePerm))));
    fi;
  end;
  FuncInvariant:=function(EXT)
    return [Length(EXT), RankMat(EXT)];
  end;
  BF:=BankRecording(rec(Saving:=false, BankPath:="/irrelevant/"), FuncStabilizer, FuncIsomorphy, FuncInvariant, OnSetsGroupFormalism(500));
  GetRecord:=function(eSet)
    local TheStab, OrbSize;
    TheStab:=SecondReduceGroupAction(Stabilizer(PermGRP, eSet, OnSets), eSet);
    OrbSize:=Order(PermGRP)/Order(TheStab);
    Print("OrbSize=", OrbSize, "\n");
    return rec(eSet:=eSet, Status:="NO", TheStab:=TheStab, OrbSize:=OrbSize);
  end;
  FuncGetIndex:=function(eSet)
    local iOrbit, eRepr, nbOrb;
    for iOrbit in [1..Length(ListOrbit)]
    do
      eRepr:=RepresentativeAction(PermGRP, ListOrbit[iOrbit].eSet, eSet, OnSets);
      if eRepr<>fail then
        return iOrbit;
      fi;
    od;
    Add(ListOrbit, GetRecord(eSet));
    nbOrb:=Length(ListOrbit);
    for iOrbit in [1..nbOrb-1]
    do
      TheRepresentationMatrix[iOrbit][nbOrb]:=0;
    od;
    Add(TheRepresentationMatrix, ListWithIdenticalEntries(nbOrb, 0));
    return nbOrb;
  end;
  IsRespawn:=function(OrdGRP, EXT, TheDepth)
    if OrdGRP>=50000 and TheDepth<=2 then
      return true;
    fi;
    if OrdGRP<100 then
      return false;
    fi;
    if Length(EXT)<WorkingDim+7 then
      return false;
    fi;
    if TheDepth=2 then
      return false;
    fi;
    return true;
  end;
  IsBankSave:=function(EllapsedTime, OrdGRP, EXT, TheDepth)
    if TheDepth=0 then
      return false;
    fi;
    if EllapsedTime>=600 then
      return true;
    fi;
    if Length(EXT)<=WorkingDim+5 then
      return false;
    fi;
    return true;
  end;
  TmpDir:=Filename(POLYHEDRAL_tmpdir, "");
  DataPolyhedral:=rec(IsBankSave:=IsBankSave,
        TheDepth:=0,
        IsRespawn:=IsRespawn,
        Saving:=false,
        GetInitialRays:=GetInitialRays_LinProg,
        ThePathSave:="/irrelevant/",
        ThePath:=TmpDir,
        DualDescriptionFunction:=DualDescriptionLRS_Reduction,
        GroupFormalism:=OnSetsGroupFormalism(500));
  TheGEN:=DataPolyhedral.GetInitialRays(EXT, 10);
  ListOrbit:=[GetRecord(TheGEN[1])];
  TheRepresentationMatrix:=[[0]];
  while(true)
  do
    IsFinished:=true;
    nbOrbit:=Length(ListOrbit);
    for iOrbit in [1..nbOrbit]
    do
      if ListOrbit[iOrbit].Status="NO" then
        ListOrbit[iOrbit].Status:="YES";
        IsFinished:=false;
        NewData:=ShallowCopy(DataPolyhedral);
        NewData.TheDepth:=NewData.TheDepth+1;
        RPLift:=__ProjectionLiftingFramework(EXT, ListOrbit[iOrbit].eSet);
        Ladj:=__ListFacetByAdjacencyDecompositionMethod(EXT{ListOrbit[iOrbit].eSet}, ListOrbit[iOrbit].TheStab, NewData, BF);
        for eInc in Ladj
        do
          idx:=FuncGetIndex(RPLift.FuncLift(eInc));
          eRedStab:=Stabilizer(ListOrbit[iOrbit].TheStab, eInc, OnSets);
          nbAdj:=Order(ListOrbit[iOrbit].TheStab)/Order(eRedStab);
          TheRepresentationMatrix[iOrbit][idx]:=TheRepresentationMatrix[iOrbit][idx]+nbAdj;
        od;
      fi;
    od;
    if IsFinished=true then
      break;
    fi;
  od;
  GetDiagMatrix:=function(eList)
    local nbEnt, DiagMat, i;
    nbEnt:=Length(eList);
    DiagMat:=NullMat(nbEnt, nbEnt);
    for i in [1..nbEnt]
    do
      DiagMat[i][i]:=eList[i];
    od;
    return DiagMat;
  end;
  ListRepresentatives:=List(ListOrbit, x->x.eSet);
  ListIncidence:=List(ListOrbit, x->Length(x.eSet));
  ListStabOrder:=List(ListOrbit, x->Order(x.TheStab));
  ListOrbSize:=List(ListOrbit, x->x.OrbSize);
  DMat:=GetDiagMatrix(ListOrbSize);
  if DMat*TheRepresentationMatrix<>TransposedMat(TheRepresentationMatrix)*DMat then
    Error("We have reached an inconsistency");
  fi;
  DiscriminantList:=List([1..Length(ListOrbit)], x->[1/ListIncidence[x], ListStabOrder[x]]);
  eReordPerm:=SortingPerm(DiscriminantList);
  Print("eReordPerm=", eReordPerm, "\n");
  ReordListRepresentatives:=Permuted(ListRepresentatives, eReordPerm);
  ReordDiscriminantList:=Permuted(DiscriminantList, eReordPerm);
  ReordListOrbSize:=Permuted(ListOrbSize, eReordPerm);
  ReordDMat:=GetDiagMatrix(ReordListOrbSize);
  ReordRepresentationMatrix:=Permuted(List(TheRepresentationMatrix, x->Permuted(x, eReordPerm)), eReordPerm);
  if ReordDMat*ReordRepresentationMatrix<>TransposedMat(ReordRepresentationMatrix)*ReordDMat then
    Error("We have reached an inconsistency 2");
  fi;
  return rec(ListRepresentatives:=ReordListRepresentatives, ListOrbSize:=ReordListOrbSize, TheRepresentationMatrix:=ReordRepresentationMatrix);
end;














KernelBeltComputation:=function(EXT, PermGRP, ListOrbit, ListListOrbitSubset)
  local ListPairsSet, nbOrbit, ListRPLift, ListEXTface, iOrbit, eSet, RPLift, EXTface, TheStab, TheStabRed, eSubset, ePair, nbPairs, ListStatus, DoFlipping, GetLoop, ListOrbitBelt, iPair, TheLoop, ListOrbitNr;
  if IsCentrallySymmetric(EXT)=false then
    Error("The polytope is not centrally symmetric");
  fi;
  ListPairsSet:=[];
  nbOrbit:=Length(ListOrbit);
  Print("nbOrbit facets=", nbOrbit, "\n");
  ListRPLift:=[];
  ListEXTface:=[];
  ListOrbitNr:=[];
  for iOrbit in [1..nbOrbit]
  do
    eSet:=ListOrbit[iOrbit];
    RPLift:=__ProjectionLiftingFramework(EXT, eSet);
    EXTface:=EXT{eSet};
    Add(ListRPLift, RPLift);
    Add(ListEXTface, EXTface);
    if IsCentrallySymmetric(EXTface)=false then
      Error("The facet is not centrally symmetric");
    fi;
    TheStab:=Stabilizer(PermGRP, eSet, OnSets);
    TheStabRed:=SecondReduceGroupAction(TheStab, eSet);
    for eSubset in ListListOrbitSubset[iOrbit]
    do
      ePair:=[eSet, eSet{eSubset}];
      Add(ListPairsSet, ePair);
      Add(ListOrbitNr, iOrbit);
    od;
  od;
  nbPairs:=Length(ListPairsSet);
  Print("nbPairs=", nbPairs, "\n");
  ListStatus:=ListWithIdenticalEntries(nbPairs, 1);
  DoFlipping:=function(eInfo)
    local iPair, ePair, EXTface, RPLift, eCent, EXTridge, fSubsetFace, fSet, fEXTface, fSubset, fPairImg, jPair, test, iFace;
    iPair:=eInfo.iPair;
    ePair:=ListPairsSet[iPair];
    iFace:=ListOrbitNr[iPair];
    EXTface:=ListEXTface[iFace];
    RPLift:=ListRPLift[iFace];
    eCent:=Isobarycenter(EXTface);
    EXTridge:=List(ePair[2], x->2*eCent-EXT[x]);
    fSubsetFace:=Set(List(EXTridge, x->Position(EXTface, x)));
    fSubset:=Set(List(EXTridge, x->Position(EXT, x)));
    fSet:=RPLift.FuncLift(fSubsetFace);
    fEXTface:=EXT{fSet};
    fPairImg:=[fSet, fSubset];
    for jPair in [1..nbPairs]
    do
      test:=RepresentativeAction(PermGRP, ListPairsSet[jPair], fPairImg, OnTuplesSets);
      if test<>fail then
        return rec(iPair:=jPair, eElt:=test*eInfo.eElt);
      fi;
    od;
    Error("Please debug from here");
  end;
  GetLoop:=function(iPair)
    local ListPair, ListInfo, len, fInfo, pos, TheLen;
    ListPair:=[iPair];
    ListInfo:=[rec(iPair:=iPair, eElt:=())];
    len:=1;
    while(true)
    do
      fInfo:=DoFlipping(ListInfo[len]);
      ListStatus[fInfo.iPair]:=0;
      pos:=Position(ListPair, fInfo.iPair);
      if pos<>fail then
        if pos<>1 then
          Error("Something inconsistent");
        fi;
        break;
      fi;
      Add(ListPair, fInfo.iPair);
      Add(ListInfo, fInfo);
      len:=len+1;
    od;
    TheLen:=Length(Orbit(Group([fInfo.eElt]), ListPairsSet[iPair], OnTuplesSets));
    return rec(TotalLen:=TheLen*Length(ListInfo), ListInfo:=ListInfo);
  end;
  ListOrbitBelt:=[];
  for iPair in [1..nbPairs]
  do
    if ListStatus[iPair]=1 then
      TheLoop:=GetLoop(iPair);
      Add(ListOrbitBelt, TheLoop);
    fi;
  od;
  return ListOrbitBelt;
end;




BeltComputationStandard:=function(EXT, PermGRP)
  local ListOrbit, nbOrbit, ListRPLift, iOrbit, eSet, EXTface, TheStab, TheStabRed, ListOrbitSubset, ListListOrbitSubset;
  if IsCentrallySymmetric(EXT)=false then
    Error("The polytope is not centrally symmetric");
  fi;
  ListOrbit:=DualDescriptionStandard(EXT, PermGRP);
  nbOrbit:=Length(ListOrbit);
  Print("nbOrbit facets=", nbOrbit, "\n");
  ListListOrbitSubset:=[];
  for iOrbit in [1..nbOrbit]
  do
    eSet:=ListOrbit[iOrbit];
    EXTface:=EXT{eSet};
    if IsCentrallySymmetric(EXTface)=false then
      Error("The facet is not centrally symmetric");
    fi;
    TheStab:=Stabilizer(PermGRP, eSet, OnSets);
    TheStabRed:=SecondReduceGroupAction(TheStab, eSet);
    ListOrbitSubset:=DualDescriptionStandard(EXTface, TheStabRed);
    Add(ListListOrbitSubset, ListOrbitSubset);
  od;
  return KernelBeltComputation(EXT, PermGRP, ListOrbit, ListListOrbitSubset);
end;


FindSolutionToLinearProgram:=function(ListInequalities, ToBeMinimized)
  local TheLP, TheDim, eVect, eEnt;
  TheLP:=LinearProgramming(ListInequalities, ToBeMinimized);
  TheDim:=Length(ToBeMinimized)-1;
  if IsBound(TheLP.primal_solution)=false then
    Error("There is no solution to the primal problem");
  fi;
  eVect:=ListWithIdenticalEntries(TheDim, 0);
  for eEnt in TheLP.primal_solution
  do
    eVect[eEnt[1]]:=eEnt[2];
  od;
  return eVect;
end;



#
# We resole a linear program, which is assumed to be all ok.
# (primal_solution, dual_solution, ...)
# If the solution is non-degenerate then we return the vertex
# if not then we take the isobarycenter of the vertices of
# the face that realize the maximum.
# This is expensive, but the result is a vertex that is invariant
# under affine transformation.
FindGeometricallyUniqueSolutionToLinearProgramming:=function(ListInequalities, ToBeMinimized)
  local TheLP, eVect, eEnt, eVectAdd, testNonDeg, ListMatchingIneq, eIneq, eIneqRed, nbIneq, ListStatus, ListToBeConsidered, iIneq, pos, len, TheConstraint, eNewIneq, ListVertices, eVert, NSP, NewListInequalities, TheSumVert, TheSoughtVert, eSolPositive, eVal, ListIdx, TheDim, TheSoughtVertRed, TheSecondSoughtVert, NSPext, DimFace;
  TheLP:=LinearProgramming(ListInequalities, ToBeMinimized);
  TheDim:=Length(ToBeMinimized)-1;
  if IsBound(TheLP.primal_solution)=false then
    Error("There is no solution to the primal problem");
  fi;
  eVect:=ListWithIdenticalEntries(TheDim, 0);
  for eEnt in TheLP.primal_solution
  do
    eVect[eEnt[1]]:=eEnt[2];
  od;
  eVectAdd:=Concatenation([1], eVect);
  testNonDeg:=IsSolutionToLinearProgNonDegenerate(ListInequalities, ToBeMinimized, eVectAdd);
  if testNonDeg=true then
    return eVect;
  fi;
  ListMatchingIneq:=[];
  for eIneq in ListInequalities
  do
    if eIneq*eVectAdd=0 then
      eIneqRed:=eIneq{[2..TheDim+1]};
      Add(ListMatchingIneq, eIneqRed);
    fi;
  od;
  eIneqRed:=ToBeMinimized{[2..TheDim+1]};
  Add(ListMatchingIneq, -eIneqRed);
  nbIneq:=Length(ListMatchingIneq);
  #
  ListStatus:=ListWithIdenticalEntries(nbIneq,-1);
  ListToBeConsidered:=[1..nbIneq];
  for iIneq in [1..nbIneq]
  do
    if ListStatus[iIneq]=-1 then
      pos:=Position(ListToBeConsidered, iIneq);
      len:=Length(ListToBeConsidered);
      TheConstraint:=rec(ListStrictlyPositive:=[pos], ListPositive:=Difference([1..len], [pos]), ListSetStrictPositive:=[]);
      eSolPositive:=SearchPositiveRelation(ListMatchingIneq{ListToBeConsidered}, TheConstraint);
      if eSolPositive=false then
        ListStatus[iIneq]:=0;
#        a priori, it looked like we could do that but experiement
#        showed it not to be the case.
#        Remove(ListToBeConsidered, iIneq);
      else
        ListIdx:=Filtered([1..len], x->eSolPositive[x]>0);
        ListStatus{ListToBeConsidered{ListIdx}}:=ListWithIdenticalEntries(Length(ListIdx), 1);
      fi;
    fi;
  od;
  #
  ListIdx:=Filtered([1..nbIneq], x->ListStatus[x]=1);
  if Length(ListIdx)=0 then
    Error("This is not correct, we should have at least one equation");
  fi;
  NSP:=NullspaceIntMat(TransposedMat(RemoveFractionMatrix(ListMatchingIneq{ListIdx})));
  DimFace:=Length(NSP);
  NSPext:=List(NSP, x->Concatenation([0], x));
#  Print("NSP=", NSP, "\n");
  NewListInequalities:=[];
  for eIneq in ListInequalities
  do
    eIneqRed:=eIneq{[2..TheDim+1]};
    eVal:=eIneq*eVectAdd;
    if First(NSP, x->x*eIneqRed<>0)<>fail then
#      Print("eIneqRed=", eIneqRed, "\n");
      eNewIneq:=Concatenation([eVal], List(NSP, x->x*eIneqRed));
      Add(NewListInequalities, eNewIneq);
    fi;
  od;
  ListVertices:=DualDescription(NewListInequalities);
  TheSumVert:=ListWithIdenticalEntries(1+DimFace,0);
  for eVert in ListVertices
  do
    TheSumVert:=TheSumVert+eVert/eVert[1];
  od;
  TheSoughtVert:=TheSumVert/Length(ListVertices);
  TheSoughtVertRed:=TheSoughtVert{[2..DimFace+1]};
  TheSecondSoughtVert:=eVectAdd + TheSoughtVertRed*NSPext;
  return TheSecondSoughtVert{[2..TheDim+1]};
end;





# ListFacets is orbitwise or not
GetSpaceInteriorPoint_Kernel:=function(ListAddEqua, ListFacets, MatrixFaceStab, eMethod)
  local ListEqua, TheDim, eGen, DiffMat, NSP, ListInequalities, ListInequalitiesRed, ToBeMinimized, eRepFac, H, eVect, TheSol, eEqua, eVectAdd, testNonDeg;
  ListEqua:=[];
  TheDim:=Length(ListFacets[1]);
  for eGen in GeneratorsOfGroup(MatrixFaceStab)
  do
    DiffMat:=TransposedMat(eGen)-IdentityMat(TheDim);
    Append(ListEqua, DiffMat);
  od;
  Append(ListEqua, ListAddEqua);
  NSP:=NullspaceMat(TransposedMat(ListEqua));
  ListInequalities:=[];
  ToBeMinimized:=ListWithIdenticalEntries(1+Length(NSP), 0);
  for eRepFac in ListFacets
  do
    H:=Concatenation([-1], List(NSP, x->x*eRepFac));
    Add(ListInequalities, H);
    ToBeMinimized:=ToBeMinimized+H;
  od;
  ListInequalitiesRed:=Set(ListInequalities);
  if eMethod="unique" then
    eVect:=FindGeometricallyUniqueSolutionToLinearProgramming(ListInequalitiesRed, ToBeMinimized);
  else
    eVect:=FindSolutionToLinearProgram(ListInequalitiesRed, ToBeMinimized);
  fi;
  TheSol:=eVect*NSP;
  for eEqua in ListAddEqua
  do
    if TheSol*eEqua<>0 then
      Error("We have a equation failure, please debug");
    fi;
  od;
  for eRepFac in ListFacets
  do
    if TheSol*eRepFac < 1 then
      Error("We have a sign failure, please debug");
    fi;
  od;
  for eGen in GeneratorsOfGroup(MatrixFaceStab)
  do
    if TheSol*eGen<>TheSol then
      Error("The vector is not invariant, not good, please debug");
    fi;
  od;
  return TheSol;
end;

GetSpaceInteriorPoint:=function(ListAddEqua, ListFacets, MatrixFaceStab)
  return GetSpaceInteriorPoint_Kernel(ListAddEqua, ListFacets, MatrixFaceStab, "unique");
end;


GetSpaceInteriorPoint_NoGroup:=function(FAC)
  local n, ListAddEqua, MatrixFaceStab, eInterior;
#  Error("FAC case");
  n:=Length(FAC[1]);
  ListAddEqua:=[];
  MatrixFaceStab:=Group([IdentityMat(n)]);
  eInterior:=GetSpaceInteriorPoint(ListAddEqua, FAC, MatrixFaceStab);
  if First(FAC, x->eInterior*x<=0)<>fail then
    Error("Problem in the business of finding interior points");
  fi;
  return eInterior;
end;




IsIntersectionListConesRelativeInterior:=function(ListEXT)
  local ListEquaTot, BasisIntersection, GetInequality, ListIneqTot, TheSpa, ePointInt, ePointIntB, EXT, eSol, dimSpa, eVectZero, pos;
  ListEquaTot:=Concatenation(List(ListEXT, x->NullspaceMat(TransposedMat(x))));
  BasisIntersection:=NullspaceMat(TransposedMat(ListEquaTot));
  dimSpa:=Length(BasisIntersection);
  eVectZero:=ListWithIdenticalEntries(dimSpa, 0);
  #
  GetInequality:=function(EXTin)
    local eSet, EXTproj, FAC, ListIneq, eFAC, eIneq;
    eSet:=ColumnReduction(EXTin).Select;
    EXTproj:=List(EXTin, x->x{eSet});
    FAC:=DualDescription(EXTproj);
    ListIneq:=[];
    for eFAC in FAC
    do
      eIneq:=List(BasisIntersection, x->x{eSet}*eFAC);
      Add(ListIneq, eIneq);
    od;
    return ListIneq;
  end;
  ListIneqTot:=Concatenation(List(ListEXT, GetInequality));
  TheSpa:=LinearDeterminedByInequalities(ListIneqTot);
  pos:=Position(ListIneqTot, eVectZero);
  if Length(TheSpa)=Length(BasisIntersection) and Length(BasisIntersection) >0 and pos=fail then
    ePointInt:=GetSpaceInteriorPoint_NoGroup(ListIneqTot);
    ePointIntB:=ePointInt * BasisIntersection;
    for EXT in ListEXT
    do
      eSol:=SolutionMatStrictlyPositive(EXT, ePointIntB);
      if eSol=false then
        Error("The point is not in the relative interior");
      fi;
    od;
    return rec(result:=true, eEXT:=ePointIntB);
  else
    return rec(result:=false);
  fi;
end;



CheckPairwiseDecomposition:=function(ListEXT)
  local TotDim, ListFAC, TestIntersection, iPoly, jPoly, nbPoly;
  TotDim:=Length(ListEXT[1][1]);
  nbPoly:=Length(ListEXT);
  ListFAC:=List(ListEXT, DualDescription);
  TestIntersection:=function(iPoly, jPoly)
    local eFAC, ListScal, TheConcat, TheSpann;
    # First checking with the inequalities. iPoly/jPoly
    for eFAC in ListFAC[iPoly]
    do
      ListScal:=List(ListEXT[jPoly], x->x*eFAC);
      if Maximum(ListScal) <= 0 then
        return true;
      fi;
    od;
    # Second checking with the inequalities. jPoly/iPoly
    for eFAC in ListFAC[jPoly]
    do
      ListScal:=List(ListEXT[iPoly], x->x*eFAC);
      if Maximum(ListScal) <= 0 then
        return true;
      fi;
    od;
    # Third, easy ways failed. Let's use the hard way.
    TheConcat:=Concatenation(ListFAC[iPoly], ListFAC[jPoly]);
    TheSpann:=LinearDeterminedByInequalities(TheConcat);
    if RankMat(TheSpann)=TotDim then
      return false;
    else
      return true;
    fi;
  end;
  #
  for iPoly in [1..nbPoly]
  do
    for jPoly in [iPoly+1..nbPoly]
    do
      if TestIntersection(iPoly, jPoly)=false then
        return false;
      fi;
    od;
  od;
  return true;
end;
