FileWythoffEnum:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"WythoffEnum.prog");

Wythoff_IsBlocking:=function(Vset, Uset, UpSet)
  local u, v, TheInterval, TheInt;
  for u in Uset
  do
    for v in Vset
    do
      if u <= v then
        TheInterval:=[u..v];
      else
        TheInterval:=[v..u];
      fi;
      TheInt:=Intersection(TheInterval, UpSet);
      if Length(TheInt)=0 then
        return false;
      fi;
    od;
  od;
  return true;
end;

Wythoff_KernelSubsetsEnumeration:=function(OmegaSet, n, Vset)
  local ListSizes, GRA, iSet, jSet, eSet, fSet, LConn, ListRelSubsets, eConn, ListRelSizes, TheMin, pos, ListOrders, ListNewlyRanked, ListRank, NewListRanked, eRank, ListAbove, fRank;
  ListSizes:=List(OmegaSet, Length);
  GRA:=NullGraph(Group(()), Length(OmegaSet));
  for iSet in [1..Length(OmegaSet)-1]
  do
    for jSet in [iSet+1..Length(OmegaSet)]
    do
      eSet:=OmegaSet[iSet];
      fSet:=OmegaSet[jSet];
      if Wythoff_IsBlocking(Vset, eSet, fSet)=true and Wythoff_IsBlocking(Vset, fSet, eSet)=true then
        AddEdgeOrbit(GRA, [iSet, jSet]);
        AddEdgeOrbit(GRA, [jSet, iSet]);
      fi;
    od;
  od;
  LConn:=ConnectedComponents(GRA);
  ListRelSubsets:=[];
  for eConn in LConn
  do
    ListRelSizes:=ListSizes{eConn};
    TheMin:=Minimum(ListRelSizes);
    pos:=Position(ListRelSizes, TheMin);
    Add(ListRelSubsets, OmegaSet[eConn[pos]]);
  od;
  ListOrders:=[];
  for iSet in [1..Length(ListRelSubsets)]
  do
    for jSet in [1..Length(ListRelSubsets)]
    do
      if iSet<>jSet then
        eSet:=ListRelSubsets[iSet];
        fSet:=ListRelSubsets[jSet];
        if Wythoff_IsBlocking(Vset, eSet, fSet) then
          Add(ListOrders, [jSet, iSet]);
        fi;
      fi;
    od;
  od;
  ListNewlyRanked:=ListWithIdenticalEntries(Length(ListRelSubsets), 0);
  ListRank:=ListWithIdenticalEntries(Length(ListRelSubsets), -1);
  pos:=Position(ListRelSubsets, Vset);
  ListRank[pos]:=0;
  ListNewlyRanked:=[pos];
  while(true)
  do
    NewListRanked:=[];
    for iSet in ListNewlyRanked
    do
      eRank:=ListRank[iSet];
      ListAbove:=List(Filtered(ListOrders, x->x[1]=iSet), x->x[2]);
      for jSet in ListAbove
      do
        pos:=First(ListAbove, x->Position(ListOrders, [x, jSet])<>fail);
        if pos=fail then
          fRank:=eRank+1;
          if ListRank[jSet]<>-1 and ListRank[jSet]<>fRank then
            Error("Error in Wythoof function please debug");
          fi;
          ListRank[jSet]:=fRank;
          Add(NewListRanked, jSet);
        fi;
      od;
    od;
    if Length(NewListRanked)=0 then
      break;
    fi;
    ListNewlyRanked:=Set(NewListRanked);
  od;
  return rec(ListSet:=ListRelSubsets, ListRank:=ListRank);
end;

Wythoff_SubsetsEnumeration:=function(n, Vset)
  local OmegaSet;
  OmegaSet:=Difference(Combinations([1..n]), [[]]);
  return Wythoff_KernelSubsetsEnumeration(OmegaSet, n, Vset);
end;

Wythoff_CstyleSubsetsEnumeration:=function(n, Vset)
  local FileInput, FileOutput, output, Vvector, TheRead;
  FileInput:=Filename(POLYHEDRAL_tmpdir, "TheInput");
  FileOutput:=Filename(POLYHEDRAL_tmpdir, "TheOutput");
  RemoveFileIfExist(FileInput);
  RemoveFileIfExist(FileOutput);
  output:=OutputTextFile(FileInput, true);
  AppendTo(output, n, "\n");
  Vvector:=ListWithIdenticalEntries(n, 0);
  Vvector{Vset}:=ListWithIdenticalEntries(Length(Vset), 1);
  WriteVector(output, Vvector);
  CloseStream(output);
  Exec(FileWythoffEnum, " ", FileInput, " ", FileOutput);
  TheRead:=ReadAsFunction(FileOutput)();
  RemoveFile(FileInput);
  RemoveFile(FileOutput);
  return TheRead;
end;


Wythoff_ArePartialFlagCompatible:=function(eSet1, ePart1, eSet2, ePart2)
  local eBigSet, eTotFlag, eVal, pos1, pos2, len, i;
  eBigSet:=Union(eSet1, eSet2);
  eTotFlag:=[];
  for eVal in eBigSet
  do
    pos1:=Position(eSet1, eVal);
    pos2:=Position(eSet2, eVal);
    if pos1<>fail and pos2<>fail then
      if ePart1[pos1]<>ePart2[pos2] then
        return false;
      fi;
      Add(eTotFlag, ePart1[pos1]);
    elif pos1<>fail then
      Add(eTotFlag, ePart1[pos1]);
    elif pos2<>fail then
      Add(eTotFlag, ePart2[pos2]);
    else
      Error("Error in Wythoof compatibility test");
    fi;
  od;
  len:=Length(eTotFlag);
  for i in [2..len]
  do
    if IsSubset(eTotFlag[i], eTotFlag[i-1])=false then
      return false;
    fi;
  od;
  return true;
end;

PartialFlagOrbitEnumeration:=function(GroupEXT, EXT, Vset)
  local nbVert, RaiseToOneLevel, O, TheTotalList, nbLevel, i, eSingleOrb, nbIncrease, NewTotalList;
  nbVert:=Length(EXT);
  RaiseToOneLevel:=function(SingleOrb, nbIncrease)
    local TheStab, ListTotalOrbit, iInc, NewTotalList, FuncInsert, eOrb, TheSpann, eSpann, TheStab2, nbOper;
    if SingleOrb=[] then
      ListTotalOrbit:=List(Orbits(GroupEXT, [1..nbVert], OnPoints), x->[x[1]]);
      nbOper:=nbIncrease-1;
      TheStab:=Group(GeneratorsOfGroup(GroupEXT));
    else
      ListTotalOrbit:=[SingleOrb[Length(SingleOrb)]];
      TheStab:=OnTuplesSetsStabilizer(GroupEXT, SingleOrb);
      nbOper:=nbIncrease;
    fi;
    for iInc in [1..nbOper]
    do
      NewTotalList:=[];
      FuncInsert:=function(eSet)
        local fSet, test;
        for fSet in NewTotalList
        do
          test:=RepresentativeAction(TheStab, fSet, eSet, OnSets);
          if test<>fail then
            return;
          fi;
        od;
        Add(NewTotalList, eSet);
      end;
      for eOrb in ListTotalOrbit
      do
        # in principle we can use a bigger group at the cost of double
        # coset decompositions
        TheStab2:=Stabilizer(TheStab, eOrb, OnSets);
        TheSpann:=SPAN_face_LinearProgramming(eOrb, TheStab2, EXT, GroupEXT, []);
        for eSpann in TheSpann
        do
          FuncInsert(eSpann);
        od;
      od;
      ListTotalOrbit:=ShallowCopy(NewTotalList);
    od;
    return List(ListTotalOrbit, x->Concatenation(SingleOrb, [x]));
  end;
  O:=Orbits(GroupEXT, [1..nbVert], OnPoints);
  TheTotalList:=[[]];
  nbLevel:=Length(Vset);
  for i in [1..nbLevel]
  do
    if i=1 then
      nbIncrease:=Vset[1];
    else
      nbIncrease:=Vset[i]-Vset[i-1];
    fi;
    NewTotalList:=[];
    for eSingleOrb in TheTotalList
    do
      Append(NewTotalList, RaiseToOneLevel(eSingleOrb, nbIncrease));
    od;
    TheTotalList:=ShallowCopy(NewTotalList);
  od;
  return TheTotalList;
end;




Wythoff_SubsetsEnumeration:=function(n, Vset)
  local OmegaSet;
  OmegaSet:=Difference(Combinations([1..n]), [[]]);
  return Wythoff_KernelSubsetsEnumeration(OmegaSet, n, Vset);
end;

Wythoff_GetPermutationGroupDiagInfo:=function(n, k, len)
  local Vset, H, OmegaSet, i, eH, TheCOMP, ListRetSet, ListRetRank, iRank, ListIdx, ListRelSet;
  Vset:=[1..k];
  H:=Combinations([1..k]);
  OmegaSet:=List(H, x->x);
  for i in [k+1..n]
  do
    for eH in H
    do
      Add(OmegaSet, Union(eH, [i]));
    od;
  od;
  TheCOMP:=Wythoff_KernelSubsetsEnumeration(OmegaSet, n, Vset);
  ListRetSet:=[];
  ListRetRank:=[];
  for iRank in [0..len]
  do
    ListIdx:=Filtered([1..Length(TheCOMP.ListRank)], x->TheCOMP.ListRank[x]=iRank);
    ListRelSet:=TheCOMP.ListSet{ListIdx};
    Append(ListRetSet, ListRelSet);
    Append(ListRetRank, ListWithIdenticalEntries(Length(ListRelSet), iRank));
  od;
  return rec(ListSet:=ListRetSet, ListRank:=ListRetRank);
end;




Wythoff_EnumerateKcellsStabilizers:=function(DiagINFO, GroupEXT, EXT, BoundingSet, Vset, kSought)
  local iRank, ListIdx, ListSubsets, eSubset, TheClassif, iOrb, ePartFlag, TotalListStabilizerSizes, TheStab;
  if Length(EXT[1])<>RankMat(EXT) then
    Print("We have Length(EXT[1])=", Length(EXT[1]), "\n");
    Print("But       RankMat(EXT)=", RankMat(EXT), "\n");
    Print("They should be equal\n");
    Error("You should use ColumnReduction for preprocessing");
  fi;
  TotalListStabilizerSizes:=[];
  for iRank in [1..kSought+1]
  do
    Print("Doing iRank=", iRank, "\n");
    ListIdx:=Filtered([1..Length(DiagINFO.ListRank)], x->DiagINFO.ListRank[x]=iRank);
    ListSubsets:=DiagINFO.ListSet{ListIdx};
    Print("ListSubsets=", ListSubsets, "\n");
    for eSubset in ListSubsets
    do
      Print("  eSubset=", eSubset, "\n");
      TheClassif:=PartialFlagOrbitEnumeration(GroupEXT, EXT, eSubset);
      Print("  |Classif|=", Length(TheClassif), "\n");
      for iOrb in [1..Length(TheClassif)]
      do
        ePartFlag:=TheClassif[iOrb];
        TheStab:=OnTuplesSetsStabilizer(GroupEXT, ePartFlag);
        Print("    iOrb=", iOrb, "  |Stab|=", Order(TheStab), "\n");
        Add(TotalListStabilizerSizes, TheStab);
      od;
    od;
  od;
  return TotalListStabilizerSizes;
end;


Wythoff_KernelBoundaryOperatorCellularDecomposition:=function(DiagINFO, GroupEXT, EXT, BoundingSet, Vset, kSought)
  local TheDim, ClassificationBank, GetClassification, eClass, ListOrbitByRank, ListOrbVertices, TheStab, TheRec, FuncGetRepresentative, FuncSignatureDet, iRank, ListIdx, ListIdxM1, ListSubsets, ListSubsetsM1, ListOrbits, eSubset, TheClassif, ListSubsetRel, NewListOrbit, iOrb, ePartFlag, TheBoundary, eSubRel, eSubUni, ListPos1, ListPos2, ListClass, ePairOrbit, ePairOrbitRed, eEquiv, ePairOrbit2, eSubFace, eSought, TheOrbSmall, NewListElement, ListSetsM2, ListFacesM2, ListElementM2, ListIFace, ListElt, ListOccuringCoefficients, iFaceM1, TheBoundaryM1, eElt, idx, nbBound, eSign, eEltM2, eAddElt, iFaceM2, eFlag, pos, eMulSign, ListSign, TheReturnBoundary, TheRetOrbit, iBound, eOrbitSmall, eOrb, ListSubRel, eRotSubgroup, ListSignGens, ListMatrGens, TheSym2, ePerm, nbOrbit, iOrbit, TheRank, eGen, GetResolution;
  if Length(EXT[1])<>RankMat(EXT) then
    Print("We have Length(EXT[1])=", Length(EXT[1]), "\n");
    Print("But       RankMat(EXT)=", RankMat(EXT), "\n");
    Print("They should be equal\n");
    Error("You should use ColumnReduction for preprocessing");
  fi;
  TheDim:=RankMat(EXT)-1;
#  DiagINFO:=Wythoff_CstyleSubsetsEnumeration(TheDim, Vset);
  ClassificationBank:=[];
  GetClassification:=function(Hset)
    local eClass, ListOrbit;
    for eClass in ClassificationBank
    do
      if eClass.eSet=Hset then
        return eClass.ListOrbit;
      fi;
    od;
    Print("|GroupEXT|=", Order(GroupEXT), " |EXT|=", Length(EXT), " Hset=", Hset, "\n");
    ListOrbit:=PartialFlagOrbitEnumeration(GroupEXT, EXT, Hset);
    Add(ClassificationBank, rec(eSet:=Hset, ListOrbit:=ListOrbit));
    return ListOrbit;
  end;
  ListOrbitByRank:=[];
  ListOrbitByRank[1]:=[rec(EXT:=[], TheStab:="irrelevant", BoundaryImage:="irrelevant", TheDel:="irrelevant")];
  ListOrbVertices:=[];
  Print("Vset=", Vset, "\n");
  Print("|GetClassification(Vset)|=", Length(GetClassification(Vset)), "\n");
  for eOrb in GetClassification(Vset)
  do
#    Print("eOrb=", eOrb, "\n");
    TheStab:=Stabilizer(GroupEXT, eOrb, OnTuplesSets);
#    Print("|TheStab|=", Order(TheStab), "\n");
    TheRec:=rec(eFlag:=eOrb, Vset:=Vset, TheStab:=TheStab, BoundaryImage:=rec(ListIFace:=[1], ListSign:=[1], ListElt:=[()]));
    Add(ListOrbVertices, TheRec);
  od;
  Print("We have ", Length(ListOrbVertices), " orbits of vertices\n");
  Add(ListOrbitByRank, ListOrbVertices);
  FuncGetRepresentative:=function(iRank, Vset, ePartFlag)
    local iOrb, eOrb, eEquiv;
    for iOrb in [1..Length(ListOrbitByRank[iRank+2])]
    do
      eOrb:=ListOrbitByRank[iRank+2][iOrb];
      if eOrb.Vset=Vset then
        eEquiv:=OnTuplesSetsRepresentativeAction(GroupEXT, eOrb.eFlag, ePartFlag);
        if eEquiv<>fail then
          return rec(iFace:=iOrb, eEquiv:=eEquiv);
        fi;
      fi;
    od;
    Error("We failed to find the orbit. Please debug");
  end;
  FuncSignatureDet:=function(iRank, iFace, eElt)
    local TheRec, iFaceLow, eSignLow, eEltLow, ePartFlag1, ePartFlag2, iBound, iFaceSec, eEltSec, eSignSec, ePartFlagSec, eEltPres;
    if iRank=0 then
      return 1;
    fi;
    TheRec:=ListOrbitByRank[iRank+2][iFace];
    if not(eElt in TheRec.TheStab) then
      Error("The element does not stabilize. please correct");
    fi;
    iFaceLow:=TheRec.BoundaryImage.ListIFace[1];
    eSignLow:=TheRec.BoundaryImage.ListSign[1];
    eEltLow:=TheRec.BoundaryImage.ListElt[1];
    ePartFlag1:=OnTuplesSets(ListOrbitByRank[iRank+1][iFaceLow].eFlag, eEltLow);
    ePartFlag2:=OnTuplesSets(ePartFlag1, eElt);
    for iBound in [1..Length(TheRec.BoundaryImage.ListIFace)]
    do
      iFaceSec:=TheRec.BoundaryImage.ListIFace[iBound];
      if iFaceSec=iFaceLow then
        eEltSec:=TheRec.BoundaryImage.ListElt[iBound];
        eSignSec:=TheRec.BoundaryImage.ListSign[iBound];
        ePartFlagSec:=OnTuplesSets(ListOrbitByRank[iRank+1][iFaceLow].eFlag, eEltSec);
        if ePartFlagSec=ePartFlag2 then
          eEltPres:=eEltLow*eElt*(eEltSec^(-1));
          return eSignSec*eSignLow*FuncSignatureDet(iRank-1, iFaceLow, eEltPres);
        fi;
      fi;
    od;
  end;
  for iRank in [1..kSought+1]
  do
    ListIdx:=Filtered([1..Length(DiagINFO.ListRank)], x->DiagINFO.ListRank[x]=iRank);
    ListIdxM1:=Filtered([1..Length(DiagINFO.ListRank)], x->DiagINFO.ListRank[x]=iRank-1);
    ListSubsets:=DiagINFO.ListSet{ListIdx};
    Print("iRank=", iRank, "  Listsubsets=", ListSubsets, "\n");
    ListSubsetsM1:=DiagINFO.ListSet{ListIdxM1};
    NewListOrbit:=[];
    for eSubset in ListSubsets
    do
      TheClassif:=GetClassification(eSubset);
      ListSubRel:=Filtered(ListSubsetsM1, x->Wythoff_IsBlocking(Vset, eSubset, x));
      Print("eSubset=", eSubset, " |Classif|=", Length(TheClassif), "  ListSubRel=", ListSubRel, "\n");
      for iOrb in [1..Length(TheClassif)]
      do
        ePartFlag:=TheClassif[iOrb];
        TheStab:=OnTuplesSetsStabilizer(GroupEXT, ePartFlag);
        TheBoundary:=[];
        for eSubRel in ListSubRel
        do
          eSubUni:=Union(eSubRel, eSubset);
          ListPos1:=List(eSubset, x->Position(eSubUni, x));
          ListPos2:=List(eSubRel, x->Position(eSubUni, x));
          ListClass:=GetClassification(eSubUni);
          for ePairOrbit in ListClass
          do
            ePairOrbitRed:=ePairOrbit{ListPos1};
            eEquiv:=OnTuplesSetsRepresentativeAction(GroupEXT, ePairOrbitRed, ePartFlag);
            if eEquiv<>fail then
              ePairOrbit2:=OnTuplesSets(ePairOrbit, eEquiv);
              eSubFace:=ePairOrbit2{ListPos2};
              eSought:=FuncGetRepresentative(iRank-1, eSubRel, eSubFace);
              TheOrbSmall:=OrbitWithAction(TheStab, eSubFace, OnTuplesSets);
              NewListElement:=List(TheOrbSmall.ListElement, x->eSought.eEquiv*x);
              Add(TheBoundary, rec(iFace:=eSought.iFace, ListElement:=NewListElement));
            fi;
          od;
        od;
        ListSetsM2:=[];
        ListFacesM2:=[];
        ListElementM2:=[];
        ListIFace:=[];
        ListElt:=[];
        ListOccuringCoefficients:=[];
        idx:=0;
        for eOrbitSmall in TheBoundary
        do
          iFaceM1:=eOrbitSmall.iFace;
          TheBoundaryM1:=ListOrbitByRank[iRank+1][iFaceM1].BoundaryImage;
          for eElt in eOrbitSmall.ListElement
          do
            idx:=idx+1;
            Add(ListIFace, iFaceM1);
            Add(ListElt, eElt);
            nbBound:=Length(TheBoundaryM1.ListIFace);
            for iBound in [1..nbBound]
            do
              eSign:=TheBoundaryM1.ListSign[iBound];
              eEltM2:=TheBoundaryM1.ListElt[iBound];
              eAddElt:=eEltM2*eElt;
              iFaceM2:=TheBoundaryM1.ListIFace[iBound];
              if iRank=1 then
                eFlag:="bckl";
              else
                eFlag:=OnTuplesSets(ListOrbitByRank[iRank][iFaceM2].eFlag, eAddElt);
              fi;
              pos:=Position(ListSetsM2, eFlag);
              if pos=fail then
                Add(ListSetsM2, eFlag);
                Add(ListElementM2, eAddElt);
                Add(ListFacesM2, iFaceM2);
                Add(ListOccuringCoefficients, [rec(Sign:=eSign, idx:=idx)]);
              else
                if iRank<=2 then
                  eMulSign:=1;
                else
                  eMulSign:=FuncSignatureDet(iRank-2, iFaceM2, ListElementM2[pos]*eAddElt^(-1));
                fi;
                Add(ListOccuringCoefficients[pos], rec(Sign:=eMulSign*eSign, idx:=idx));
              fi;
            od;
          od;
        od;
        ListSign:=UntangleAllSigns(ListOccuringCoefficients, idx);
        TheReturnBoundary:=rec(ListIFace:=ListIFace, ListSign:=ListSign, ListElt:=ListElt);
        TheRetOrbit:=rec(eFlag:=ePartFlag, Vset:=eSubset, TheStab:=TheStab, BoundaryImage:=TheReturnBoundary);
        Add(NewListOrbit, TheRetOrbit);
      od;
    od;    
    Add(ListOrbitByRank, NewListOrbit);
  od;
  TheRank:=Length(ListOrbitByRank)-2;
  for iRank in [0..TheRank]
  do
    nbOrbit:=Length(ListOrbitByRank[iRank+2]);
    for iOrbit in [1..nbOrbit]
    do
      TheStab:=ListOrbitByRank[iRank+2][iOrbit].TheStab;
      ListMatrGens:=GeneratorsOfGroup(TheStab);
      TheSym2:=SymmetricGroup(2);
      ListSignGens:=[];
      for eGen in ListMatrGens
      do
        eSign:=FuncSignatureDet(iRank, iOrbit, eGen);
        if eSign=1 then
          ePerm:=();
        else
          ePerm:=(1,2);
        fi;
        Add(ListSignGens, ePerm);
      od;
      eRotSubgroup:=GetKernelOfMapping(TheStab, TheSym2, ListMatrGens, ListSignGens);
      ListOrbitByRank[iRank+2][iOrbit].RotationSubgroup:=eRotSubgroup;
    od;
  od;
  GetResolution:=function(GRP, kLevel)
    return ResolutionComingFromHAP(GRP, kLevel);
  end;
  return rec(ListOrbitByRank:=ListOrbitByRank, 
             GetResolution:=GetResolution, 
             IdentityElt:=());
end;

Wythoff_BoundaryOperatorCellularDecomposition:=function(GroupEXT, EXT, BoundingSet, Vset, kSought)
  local TheDim, DiagINFO;
  TheDim:=RankMat(EXT)-1;
  DiagINFO:=Wythoff_CstyleSubsetsEnumeration(TheDim, Vset);
  return Wythoff_KernelBoundaryOperatorCellularDecomposition(DiagINFO, GroupEXT, EXT, BoundingSet, Vset, kSought);
end;

Wythoff_ConstructionPermutationGroup:=function(ThePermGroup, n, kSet, kSought)
  local EXT, i, V, DiagINFO, Vset;
  EXT:=[];
  for i in [1..n]
  do
    V:=ListWithIdenticalEntries(n, 0);
    V[i]:=1;
    Add(EXT, V);
  od;
  DiagINFO:=Wythoff_GetPermutationGroupDiagInfo(n-1, kSet, kSought+1);
  Vset:=[1..kSet];
  return Wythoff_KernelBoundaryOperatorCellularDecomposition(DiagINFO, ThePermGroup, EXT, [], Vset, kSought);
end;

