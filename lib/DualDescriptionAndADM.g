DirectSumDecompositionPolyhedralCone:=function(EXT)
  local eSet, eBasis, rnk, GRA, eEXT, eSol, ListIdx, i, eVert, fVert, ListEXT, ListEXTred, NewEXT, NewEXTred, ListConn, eConn, ListListIdx, eList, iEXT;
  eSet:=RowReduction(EXT).Select;
  eBasis:=EXT{eSet};
  rnk:=Length(eSet);
  GRA:=NullGraph(Group(()), rnk);
  for eEXT in EXT
  do
    eSol:=SolutionMat(eBasis, eEXT);
    ListIdx:=Filtered([1..rnk], x->eSol[x]<>0);
    if Length(ListIdx)>1 then
      for i in [2..Length(ListIdx)]
      do
        eVert:=ListIdx[1];
        fVert:=ListIdx[i];
        AddEdgeOrbit(GRA, [eVert, fVert]);
        AddEdgeOrbit(GRA, [fVert, eVert]);
      od;
    fi;
  od;
  ListConn:=ConnectedComponents(GRA);
  ListEXT:=[];
  ListEXTred:=[];
  ListListIdx:=[];
  for eConn in ListConn
  do
    NewEXT:=[];
    NewEXTred:=[];
    eList:=[];
    for iEXT in [1..Length(EXT)]
    do
      eEXT:=EXT[iEXT];
      eSol:=SolutionMat(eBasis, eEXT);
      ListIdx:=Filtered([1..rnk], x->eSol[x]<>0);
      if IsSubset(eConn, ListIdx)=true then
        Add(eList, iEXT);
        Add(NewEXT, eEXT);
        Add(NewEXTred, eSol{eConn});
      fi;
    od;
    Add(ListEXT, NewEXT);
    Add(ListEXTred, NewEXTred);
    Add(ListListIdx, eList);
  od;
  return rec(ListConn:=ListConn,
             ListListIdx:=ListListIdx,
             ListEXT:=ListEXT,
             ListEXTred:=ListEXTred);
end;




MoveGroup:=function(TheGroup, SuSet)
  local ListNewGen, eGen, eList, i, ev, fv, j;
  ListNewGen:=[];
  for eGen in GeneratorsOfGroup(TheGroup)
  do
    eList:=[];
    for i in [1..Length(SuSet)]
    do
      ev:=SuSet[i];
      fv:=OnPoints(ev, eGen);
      j:=Position(SuSet, fv);
      Add(eList, j);
    od;
    Add(ListNewGen, PermList(eList));
  od;
  return PersoGroupPerm(ListNewGen);
end;


GetProcessIdentifier:=function()
  local U;
  U:=Filename(POLYHEDRAL_tmpdir, "");
  return U{[10..Length(U)-1]};
end;


MyParallelList:=function(TheListObject, TheFunction, ThePrefix)
  local TheIdentifier, iElt, ShortName, OurFileLock, ListFileLock, TheResult, OurFileResult;
  if IsExistingFile(ThePrefix)=false then
    Error("Directory is non-existent");
  fi;
  IsCorrectPath(ThePrefix);
  TheIdentifier:=GetProcessIdentifier();
  for iElt in [1..Length(TheListObject)]
  do
    ShortName:=Concatenation("lock", String(iElt));
    OurFileLock:=Concatenation(ThePrefix, ShortName, "_", TheIdentifier);
    ListFileLock:=Filtered(DirectoryContents(ThePrefix), x->x{[1..Length(ShortName)]}=ShortName);
    if Length(ListFileLock)=0 then
      SaveDataToFile(OurFileLock, 0);
      OurFileResult:=Concatenation("result", String(iElt), "_", TheIdentifier);
      TheResult:=TheFunction(TheListObject[iElt]);
      SaveDataToFilePlusTouch(OurFileResult, TheResult);
    fi;
  od;
end;









GetBalinskiInformation:=function(EXT, GRP)
  local EXTred, ListMatrGen, eGen, eMat, eMatB, GetSpaceExtension, rnk;
  EXTred:=List(ColumnReduction(EXT).EXT, RemoveFraction);
  ListMatrGen:=[];
  for eGen in GeneratorsOfGroup(GRP)
  do
    eMat:=FindTransformation(EXTred, EXTred, eGen);
    eMatB:=CongrMap(eMat);
    Add(ListMatrGen, eMatB);
  od;
  GetSpaceExtension:=function(FACpartial, eInc)
    local NSP, eVect, ListFACspann, ListFACstatus, FuncInsert, IsFinished, iFAC, fVect, gVect, eFAC, len, nbPartial;
    NSP:=NullspaceMat(TransposedMat(EXTred{eInc}));
    if Length(NSP)<>1 then
      Error("Wrong rank of matrix");
    fi;
    nbPartial:=Length(FACpartial);
    eVect:=NSP[1];
    ListFACspann:=[];
    for eFAC in FACpartial
    do
      Add(ListFACspann, eFAC);
    od;
    ListFACstatus:=[];
    FuncInsert:=function(eVect)
      if Length(ListFACspann)=0 then
        Add(ListFACspann, eVect);
        Add(ListFACstatus, 0);
      else
        if SolutionMat(ListFACspann, eVect)=fail then
          Add(ListFACspann, eVect);
          Add(ListFACstatus, 0);
        fi;
      fi;
    end;
    FuncInsert(eVect);
    while(true)
    do
      IsFinished:=true;
      len:=Length(ListFACspann) - nbPartial;
      for iFAC in [1..len]
      do
        if ListFACstatus[iFAC]=0 then
          ListFACstatus[iFAC]:=1;
          IsFinished:=false;
          fVect:=ListFACspann[iFAC + nbPartial];
          for eGen in ListMatrGen
          do
            gVect:=fVect*eGen;
            FuncInsert(gVect);
          od;
        fi;
      od;
      if IsFinished then
        break;
      fi;
    od;
    return ListFACspann;
  end;
  rnk:=Length(EXTred[1]);
  return rec(rnk:=rnk,
             EXTred:=EXTred,
             GetSpaceExtension:=GetSpaceExtension);
end;


#
# ---If the set has dimension <= n-2 then it does not
#    disconnect the graph
# ---If the set has dimension n-1 and it is contained in a facet
#    then it does not disconnect the graph.
# ---As a side note, if the set has dimension n-1 and this space
#    has another element not in the set, then it does not disconnect
#    the graph. But that criterion is difficult to implement.
TestBalinskiCriterion_Kernel:=function(EXT, GRP, ListOrbitFacets)
  local RbalinskiRank, rnk, FACpartial, eOrb, NSP, eVect;
  RbalinskiRank:=GetBalinskiInformation(EXT, GRP);
  rnk:=RbalinskiRank.rnk;
  FACpartial:=[];
  for eOrb in ListOrbitFacets
  do
    FACpartial:=RbalinskiRank.GetSpaceExtension(FACpartial, eOrb);
    if Length(FACpartial)=rnk then
      return false;
    fi;
  od;
  if Length(FACpartial)<=rnk-2 then
    return true;
  fi;
  if Length(FACpartial)=rnk-1 then
    NSP:=NullspaceMat(TransposedMat(FACpartial));
    if Length(NSP)<>1 then
      Error("Dimension should be 1");
    fi;
    eVect:=RemoveFraction(NSP[1]);
    if Position(RbalinskiRank.EXTred, eVect)=fail and Position(RbalinskiRank.EXTred, -eVect)=fail then
      return false;
    else
      return true;
    fi;
  fi;
end;

TestBalinskiCriterion:=function(EXT, GRP, ListOrbitFacets)
  local reply, ListSets, ListSetsBad, TheDiff, nbV, GRA, eOrb, i, j, eInt, rnk;
  reply:=TestBalinskiCriterion_Kernel(EXT, GRP, ListOrbitFacets);
  if reply=false then
    return false;
  fi;
  rnk:=RankMat(EXT);
  ListSets:=DualDescriptionSets(EXT);
  ListSetsBad:=[];
  for eOrb in ListOrbitFacets
  do
    Append(ListSetsBad, Orbit(GRP, eOrb, OnSets));
  od;
  TheDiff:=Difference(ListSets, ListSetsBad);
  nbV:=Length(TheDiff);
  GRA:=NullGraph(Group(()), nbV);
  for i in [1..nbV-1]
  do
    for j in [i+1..nbV]
    do
      eInt:=Intersection(TheDiff[i], TheDiff[j]);
      if RankMat(EXT{eInt})=rnk-2 then
        AddEdgeOrbit(GRA, [i,j]);
        AddEdgeOrbit(GRA, [j,i]);
      fi;
    od;
  od;
  if IsConnectedGraph(GRA)=false then
    Error("Fail the sanity check in Balinski theorem RAW");
  fi;
  return true;
end;


BalinskiBankFormalism:=function(FAC, GRP, ListOrbitVertices)
  local ListSolved, FuncInsert, FuncQuery, ListMatrGenFAC, ListMatrGenEXT, eGen, eMat, GRPmatrFAC, GRPmatrEXT, phiPermFAC, phiPermEXT, ListPermGen;
  ListSolved:=[];
  FuncInsert:=function(eSet)
    Add(ListSolved, eSet);
  end;
  FuncQuery:=function(eSet)
    local fSet, test;
    for fSet in ListSolved
    do
      test:=RepresentativeAction(GRP, eSet, fSet, OnSets);
      if test<>fail then
        return true;
      fi;
    od;
    return fail;
  end;
  ListMatrGenFAC:=[];
  ListMatrGenEXT:=[];
  ListPermGen:=GeneratorsOfGroup(GRP);
  for eGen in ListPermGen
  do
    eMat:=FindTransformation(FAC, FAC, eGen);
    Add(ListMatrGenFAC, eMat);
    Add(ListMatrGenEXT, CongrMap(eMat));
  od;
  GRPmatrFAC:=Group(ListMatrGenFAC);
  GRPmatrEXT:=Group(ListMatrGenEXT);
  phiPermFAC:=GroupHomomorphismByImagesNC(GRP, GRPmatrFAC, ListPermGen, ListMatrGenFAC);
  phiPermEXT:=GroupHomomorphismByImagesNC(GRP, GRPmatrEXT, ListPermGen, ListMatrGenEXT);
  return rec(FAC:=FAC,
             GRP:=GRP,
             GRPmatrFAC:=GRPmatrFAC,
             GRPmatrEXT:=GRPmatrEXT,
             phiPermFAC:=phiPermFAC,
             phiPermEXT:=phiPermEXT,
             ListOrbitVertices:=ListOrbitVertices,
             FuncInsert:=FuncInsert,
             FuncQuery:=FuncQuery);
end;



AdvancedBalinskiConnectivity_Kernel:=function(eSetFace, RecHeuristic, BF)
  local Stabface, TheSpann, ComputeSpann, GRP, FAC, NSP, ListOrbitVertices, test, eO, MatrixFaceStab, ListMatrEXTred, ListMatrFACred, eMatrGen, eMatrEXTred, eNSP, eSol, GetIneq, eFAC, ListPermGens, eList, eEXT, eEXTred, NbAllow, GRPmatrFACred, eGen, eInc, eOrbit, ListSmaRepr, eSmaRepr, NewHeuristic, HasComputedSpann, recTest, TheDim;
  NbAllow:=RecHeuristic.NbAllow;
  HasComputedSpann:=false;
  ComputeSpann:=function()
    local BoundingSet;
    if HasComputedSpann=false then
      Stabface:=Stabilizer(BF.GRP, eSetFace, OnSets);
      BoundingSet:=[];
      TheSpann:=SPAN_face_LinearProgramming(eSetFace, Stabface, BF.FAC, BF.GRP, BoundingSet);
      HasComputedSpann:=true;
    fi;
  end;
  if eSetFace=[] then
    GRP:=BF.GRP;
    FAC:=BF.FAC;
    ListOrbitVertices:=BF.ListOrbitVertices;
  else
    ComputeSpann();
    MatrixFaceStab:=Image(BF.phiPermEXT, Stabface);
    NSP:=NullspaceMat(TransposedMat(BF.FAC{eSetFace}));
    TheDim:=Length(NSP);
    ListMatrEXTred:=[];
    ListMatrFACred:=[];
    for eMatrGen in GeneratorsOfGroup(MatrixFaceStab)
    do
      eMatrEXTred:=[];
      for eNSP in NSP
      do
        eSol:=SolutionMat(NSP, eNSP*eMatrGen);
        if eSol=fail then
          Error("No correct solution found");
        fi;
        Add(eMatrEXTred, eSol);
      od;
      Add(ListMatrEXTred, eMatrEXTred);
      Add(ListMatrFACred, CongrMap(eMatrEXTred));
    od;
    GRPmatrFACred:=Group(ListMatrFACred);
    GetIneq:=function(eSet)
      local ListIneq, eVal, eIneq;
      ListIneq:=[];
      for eVal in eSet
      do
        eIneq:=List(NSP, x->BF.FAC[eVal]*x);
        if First(eIneq, x->x<>0)<>fail then
          Add(ListIneq, RemoveFraction(eIneq));
        fi;
      od;
      if Length(Set(ListIneq))<>1 then
        Error("Non coherent finding of inequality");
      fi;
      return ListIneq[1];
    end;
    FAC:=[];
    for eO in TheSpann
    do
      eFAC:=GetIneq(eO);
      Append(FAC, Orbit(GRPmatrFACred, eFAC, OnPoints));
    od;
    ListPermGens:=[];
    for eGen in ListMatrFACred
    do
      eList:=List(FAC, x->Position(FAC, x*eGen));
      Add(ListPermGens, PermList(eList));
    od;
    GRP:=Group(ListPermGens);
    ListOrbitVertices:=[];
    for eOrbit in BF.ListOrbitVertices
    do
      ListSmaRepr:=__IndividualLifting(eOrbit, Stabface, BF.GRP);
      for eSmaRepr in ListSmaRepr
      do
        if IsSubset(eSmaRepr, eSetFace) then
          eEXT:=FindFacetInequality(BF.FAC, eSmaRepr);
          eEXTred:=SolutionMat(NSP, eEXT);
          eInc:=Filtered([1..Length(FAC)], x->FAC[x]*eEXTred=0);
          Add(ListOrbitVertices, eInc);
        fi;
      od;
    od;
  fi;
  Print("|FAC|=", Length(FAC), " |GRP|=", Order(GRP), " |ListOrbitVertices|=", Length(ListOrbitVertices), "\n");
  test:=TestBalinskiCriterion(FAC, GRP, ListOrbitVertices);
  if test=true then
    return rec(result:=true, NbAllow:=NbAllow);
  fi;
  if RecHeuristic.Depth=RecHeuristic.MaxDepth then
    return rec(result:=false, NbAllow:=NbAllow);
  fi;
  ComputeSpann();
  Print("NbAllow=", NbAllow, " |TheSpann|=", Length(TheSpann), "\n");
  for eO in TheSpann
  do
    if BF.FuncQuery(eO)=fail then
      NbAllow:=NbAllow-1;
      if NbAllow=0 then
        return rec(result:=false, NbAllow:=NbAllow);
      fi;
      NewHeuristic:=rec(NbAllow:=NbAllow, Depth:=RecHeuristic.Depth+1, MaxDepth:=RecHeuristic.MaxDepth);
      recTest:=AdvancedBalinskiConnectivity_Kernel(eO, NewHeuristic, BF);
      NbAllow:=recTest.NbAllow;
      if recTest.result=false then
        return rec(result:=false, NbAllow:=NbAllow);
      fi;
    fi;
  od;
  BF.FuncInsert(eSetFace);
  return rec(result:=true, NbAllow:=NbAllow);
end;



# The Balinski theorem allows us to prove that the enumeration
# is already finished in a great many cases.
AdvancedBalinskiConnectivity:=function(FAC, GRP, RPL, RecHeuristic)
  local nbUndone, nbOrb, iOrb, eOrb, BF, eSet, ListOrbitVertices, RecHeu;
  nbUndone:=RPL.FuncNumberUndone();
  if RecHeuristic.MaxNumberUndone < nbUndone then
    return false;
  fi;
  nbOrb:=RPL.FuncNumberOrbit();
  ListOrbitVertices:=[];
  for iOrb in [1..nbOrb]
  do
    eOrb:=RPL.FuncRecord(iOrb);
    if eOrb.Status="NO" then
      Add(ListOrbitVertices, eOrb.Inc);
    fi;
  od;
  BF:=BalinskiBankFormalism(FAC, GRP, ListOrbitVertices);
  eSet:=[];
  RecHeu:=rec(NbAllow:=RecHeuristic.NbAllow, Depth:=0, MaxDepth:=RecHeuristic.MaxDepth);
  return AdvancedBalinskiConnectivity_Kernel(eSet, RecHeu, BF);
end;


# The Balinski theorem allows us to prove that the enumeration
# is already finished in a great many cases.
AdvancedBalinskiConnectivity_Standard:=function(FAC, GRP, ListOrbitToTest, RecHeuristic)
  local nbOrb, nbUndone, iO, eO, eStab, eSize, FuncNumberUndone, FuncNumberOrbit, FuncRecord, RPL;
  nbOrb:=Length(ListOrbitToTest);
  nbUndone:=0;
  for iO in [1..nbOrb]
  do
    eO:=ListOrbitToTest[iO];
    eStab:=Stabilizer(GRP, eO, OnSets);
    eSize:=Order(GRP)/Order(eStab);
    nbUndone:=nbUndone + eSize;
  od;
  FuncNumberUndone:=function()
    return nbUndone;
  end;
  FuncNumberOrbit:=function()
    return nbOrb;
  end;
  FuncRecord:=function(iOrb)
    return rec(Status:="NO",
               Inc:=ListOrbitToTest[iOrb]);
  end;
  RPL:=rec(FuncNumberUndone:=FuncNumberUndone,
           FuncNumberOrbit:=FuncNumberOrbit,
           FuncRecord:=FuncRecord);
  return AdvancedBalinskiConnectivity(FAC, GRP, RPL, RecHeuristic);
end;








Bank_GetSize:=function(ThePrefix)
  local nbRec, eFileEXT, eFileFAC;
  nbRec:=0;
  while(true)
  do
    eFileEXT:=Concatenation(ThePrefix, "AccountEXT_", String(nbRec+1));
    eFileFAC:=Concatenation(ThePrefix, "AccountFAC_", String(nbRec+1));
    if IsExistingFilePlusTouch(eFileEXT)=false or IsExistingFilePlusTouch(eFileFAC)=false then
      break;
    fi;
    nbRec:=nbRec+1;
  od;
  return nbRec;
end;

# It looks possible that the invariant system using the economical md5 sum
# We make some assumptions here:
# --The full invariant is the one obtained by LinPolytope_Invariant
#   i.e. it contains number of occurence of values on the diagonal
#   and off the diagonal.
# --The md5 sums are the md5 sum of the above
#
CheckSystemOfInvariant:=function(BankPath, CompleteInvPath)
  local nbRec, ListInv, ListReducedINV, iRec, eFileINV, eInv, eFileINVcomplete, eFileEXT, eInfoEXT, eInvComplete, SetReducedINV, ListPairInconsistency, eRedINV, ListIdx, Part_ListINV, Part_ListInv, eIdx, len, i, j, iG, jG, eRecInv, ePairInconsistency;
  nbRec:=Bank_GetSize(BankPath);
  ListInv:=[];
  ListReducedINV:=[];
  for iRec in [1..nbRec]
  do
    eFileINV:=Concatenation(BankPath, "AccountINV_", String(iRec));
    eInv:=ReadAsFunction(eFileINV)();
    Add(ListInv, eInv);
    #
    eFileINVcomplete:=Concatenation(CompleteInvPath, "CompleteINV_", String(iRec));
    if IsExistingFilePlusTouch(eFileINVcomplete)=false then
      eFileEXT:=Concatenation(BankPath, "AccountEXT_", String(iRec));
      eInfoEXT:=ReadAsFunction(eFileEXT)();
      eInvComplete:=LinPolytope_Invariant(eInfoEXT.EXT);
      SaveDataToFilePlusTouch(eFileINVcomplete, eInvComplete);
    else
      eInvComplete:=ReadAsFunction(eFileINVcomplete)();
    fi;
    eRecInv:=rec(n:=eInvComplete.n, eDiag:=eInvComplete.ListNbDiag);
    Add(ListReducedINV, eRecInv);
  od;
  #
  SetReducedINV:=Set(ListReducedINV);
  ListPairInconsistency:=[];
  for eRedINV in SetReducedINV
  do
    ListIdx:=Filtered([1..nbRec], x->ListReducedINV[x]=eRedINV);
    if Length(ListIdx)>1 then
      Part_ListINV:=[];
      Part_ListInv:=[];
      for eIdx in ListIdx
      do
        Add(Part_ListInv, ListInv[eIdx]);
        eFileINVcomplete:=Concatenation(CompleteInvPath, "CompleteINV_", String(eIdx));
        eInvComplete:=ReadAsFunction(eFileINVcomplete)();
        Add(Part_ListINV, eInvComplete);
      od;
      len:=Length(ListIdx);
      for i in [1..len-1]
      do
        for j in [i+1..len]
        do
          if Part_ListINV[i]=Part_ListINV[j] then
            if Part_ListInv[i]<>Part_ListInv[j] then
              iG:=ListIdx[i];
              jG:=ListIdx[j];
              ePairInconsistency:=[iG, jG];
              Print("Find inconsistency between iG=", iG, " jG=", jG, "\n");
              Add(ListPairInconsistency, ePairInconsistency);
            fi;
          fi;
        od;
      od;
    fi;
  od;
  if Length(ListPairInconsistency)>0 then
    Error("We have some inconsistency in the invariant business\n");
  fi;
end;



# this is the program for Bank management
# it does not assume a fixed EXT set, so as to deal with
# polyhedral subdivision.
# FuncStabilizer take as argument EXT and ListInc and return a stabilizer
# of EXT. N
# FuncIsomorphy(EXT1,  EXT2) and return a
# false if there is no isomorphy and a permutation ePerm where the ith
# element is the position in ListInc2 of ListInc1[i].
#
# the system is not designed for a large number of accounts, just for
# a few hundreds accounts.
BankRecording:=function(DataBank, FuncStabilizer, FuncIsomorphy, FuncInvariant, GroupFormalism)
  local FuncRetrieveObject, FuncCreateAccount, FuncClearAccount, FuncStab, FileBankRecord, WRL, ListCompleteInformation, ListInvariant, eInv, MinNbVert, nbRec, iRec, FileNameEXT, FileNameINV, eInfoEXT, nbVert;
  if IsCorrectPath(DataBank.BankPath)=false then
    Print("Variable DataBank.BankPath=", DataBank.BankPath, " is incorrect\n");
    Error("It should finish with a /");
  fi;
  if IsDirectoryPath(DataBank.BankPath)=false and DataBank.Saving=true then
    Error("Directory DataBank.BankPath=", DataBank.BankPath, " is nonexistent");
  fi;
  if DataBank.Saving then
    nbRec:=Bank_GetSize(DataBank.BankPath);
  else
    nbRec:=0;
  fi;
#  Print("Setting up database. Right now nbRec=", nbRec, "\n");
  #
  MinNbVert:=-1;
  if DataBank.Saving then
    for iRec in [1..nbRec]
    do
      FileNameEXT:=Concatenation(DataBank.BankPath, "AccountEXT_", String(iRec));
      eInfoEXT:=ReadAsFunction(FileNameEXT)();
      nbVert:=Length(GroupFormalism.BankGetForIsom(eInfoEXT));
      if iRec=1 then
        MinNbVert:=nbVert;
      else
        MinNbVert:=Minimum(MinNbVert, nbVert);
      fi;
    od;
  else
    WRL:=[];
  fi;
#  Print("At database loading. MinNbVert=", MinNbVert, "\n");
  #
  if DataBank.Saving=false then
    ListCompleteInformation:=[];
  fi;
  #
  ListInvariant:=[];
  for iRec in [1..nbRec]
  do
    FileNameINV:=Concatenation(DataBank.BankPath, "AccountINV_", String(iRec));
    if IsExistingFilePlusTouch(FileNameINV) then
      eInv:=ReadAsFunction(FileNameINV)();
    else
      FileNameEXT:=Concatenation(DataBank.BankPath, "AccountEXT_", String(iRec));
      eInfoEXT:=ReadAsFunction(FileNameEXT)();
      eInv:=FuncInvariant(GroupFormalism.BankGetForIsom(eInfoEXT));
      SaveDataToFilePlusTouch(FileNameINV, eInv);
    fi;
    Add(ListInvariant, eInv);
  od;
#  Print("Invariants have been loaded\n");
  FuncRetrieveObject:=function(EXT, GivenSymmetry)
    local eChar, iAccount, eTransform, FileName, CompleteAccount, EXTaccount, ListObjectAccount, TransListObject, GRPaccount, TheGrp, NewGrp, eInc, RPL, eInvariant;
    if Length(EXT) < MinNbVert then
      return false;
    fi;
    eChar:=GroupFormalism.BankKeyInformation(EXT, GivenSymmetry);
    eInvariant:=FuncInvariant(EXT);
#    Print("Beginning search in |database|=", nbRec, "\n");
    for iAccount in [1..nbRec]
    do
      if eInvariant=ListInvariant[iAccount] then
        if DataBank.Saving=true then
          FileNameEXT:=Concatenation(DataBank.BankPath, "AccountEXT_", String(iAccount));
          eInfoEXT:=ReadAsFunction(FileNameEXT)();
        else
          eInfoEXT:=WRL[iAccount];
        fi;
        eTransform:=FuncIsomorphy(GroupFormalism.BankGetForIsom(eInfoEXT), GroupFormalism.BankGetForIsom(eChar));
        if eTransform<>false then
          if DataBank.Saving=true then
            FileName:=Concatenation(DataBank.BankPath, "AccountFAC_", String(iAccount));
            CompleteAccount:=ReadAsFunction(FileName)();
          else
            CompleteAccount:=ListCompleteInformation[iAccount];
          fi;
          EXTaccount:=GroupFormalism.BankGetVertexSet(eInfoEXT, CompleteAccount);
          ListObjectAccount:=GroupFormalism.BankGetListObject(CompleteAccount);
          TransListObject:=GroupFormalism.TransformIncidenceList(EXTaccount, EXT, eTransform, ListObjectAccount);
          GRPaccount:=GroupFormalism.BankGetGroup(eInfoEXT, CompleteAccount);
          TheGrp:=GroupFormalism.GroupConjugacy(GRPaccount, eTransform);
          if GroupFormalism.IsSubgroup(TheGrp, GivenSymmetry)=true then
            return rec(GRP:=TheGrp, ListOrbitFacet:=TransListObject);
          else
            NewGrp:=GroupFormalism.GroupUnion(TheGrp, GivenSymmetry);
            RPL:=GroupFormalism.OrbitGroupFormalism(EXT, NewGrp, "/irrelevant/", false);
            for eInc in TransListObject
            do
              RPL.FuncInsert(eInc);
            od;
            return rec(GRP:=NewGrp, ListOrbitFacet:=RPL.FuncListOrbitIncidence());
          fi;
        fi;
      fi;
    od;
#    Print("Ending search in database\n");
    return false;
  end;
  FuncCreateAccount:=function(EXT, GroupExt, ListObject)
    local FileNameFAC, FileNameEXT, FileNameINV, CompleteInfo, eInvariant, eInfoEXT, nbVert;
    eInfoEXT:=GroupFormalism.BankKeyInformation(EXT, GroupExt);
    nbVert:=Length(eInfoEXT.EXT);
    if nbRec=0 then
      MinNbVert:=nbVert;
    else
      MinNbVert:=Minimum(MinNbVert, nbVert);
    fi;
#    Print("We have eInfoEXT\n");
    eInvariant:=FuncInvariant(EXT);
#    Print("We have eInvariant\n");
    nbRec:=nbRec+1;
    #
    CompleteInfo:=GroupFormalism.BankCompleteInformation(EXT, GroupExt, ListObject);
    if DataBank.Saving then
      FileNameFAC:=Concatenation(DataBank.BankPath, "AccountFAC_", String(nbRec));
      SaveDataToFilePlusTouch(FileNameFAC, CompleteInfo);
    else
      Add(ListCompleteInformation, CompleteInfo);
    fi;
#    Print("After write FAC\n");
    #
    if DataBank.Saving then
      FileNameEXT:=Concatenation(DataBank.BankPath, "AccountEXT_", String(nbRec));
      SaveDataToFilePlusTouch(FileNameEXT, eInfoEXT);
    else
      Add(WRL, eInfoEXT);
    fi;
#    Print("After write EXT\n");
    #
    if DataBank.Saving then
      FileNameINV:=Concatenation(DataBank.BankPath, "AccountINV_", String(nbRec));
      SaveDataToFilePlusTouch(FileNameINV, eInvariant);
    fi;
    Add(ListInvariant, eInvariant);
#    Print("After write INV\n");
  end;
  FuncClearAccount:=function()
    local iRec, FileNameFAC, FileNameEXT, FileNameINV;
    if DataBank.Saving then
      for iRec in [1..nbRec]
      do
        FileNameFAC:=Concatenation(DataBank.BankPath, "AccountFAC_", String(iRec));
        FileNameEXT:=Concatenation(DataBank.BankPath, "AccountEXT_", String(iRec));
        FileNameINV:=Concatenation(DataBank.BankPath, "AccountINV_", String(iRec));
        RemoveFileIfExistPlusTouch(FileNameFAC);
        RemoveFileIfExistPlusTouch(FileNameEXT);
        RemoveFileIfExistPlusTouch(FileNameINV);
      od;
    else
      Unbind(WRL);
      Unbind(ListCompleteInformation);
    fi;
    Unbind(ListInvariant);
  end;
  return rec(FuncStabilizer:=FuncStabilizer, FuncCreateAccount:=FuncCreateAccount, FuncRetrieveObject:=FuncRetrieveObject, FuncClearAccount:=FuncClearAccount);
end;

Tmp_PresentResult:=function(EXT, GRP, ThePrefix)
  local iOrbit, nbFac, eOrd, eFile, eRec, eInc, eEXT, eOrdStab;
  iOrbit:=0;
  nbFac:=0;
  eOrd:=Order(GRP);
  while(true)
  do
    iOrbit:=iOrbit+1;
    eFile:=Concatenation(ThePrefix, "Orbit", String(iOrbit), "_1");
    if IsExistingFilePlusTouch(eFile)=false then
      break;
    fi;
    eRec:=ReadAsFunction(eFile)();
    eInc:=eRec.Inc;
    eEXT:=FindFacetInequality(EXT, eInc);
    nbFac:=nbFac+eRec.OrbSize;
    eOrdStab:=eOrd/eRec.OrbSize;
    if eRec.Status="NO" then
      Print("iOrbit=", iOrbit, " |inc|=", Length(eInc), " |stab|=", eOrdStab, "\n");
    fi;
  od;
  Print("nbFac=", nbFac, "\n");
end;



Bank_PresentResult:=function(ThePrefix)
  local nbRec, iRec, eFileEXT, eInfoEXT, ListSizes, TheColl, nbEnt, iEnt, eEnt;
  nbRec:=Bank_GetSize(ThePrefix);
  Print("nbRec=", nbRec, "\n");
  ListSizes:=[];
  for iRec in [1..nbRec]
  do
    eFileEXT:=Concatenation(ThePrefix, "AccountEXT_", String(iRec));
    eInfoEXT:=ReadAsFunction(eFileEXT)();
    Add(ListSizes, Length(eInfoEXT.EXT));
  od;
  TheColl:=Collected(ListSizes);
  nbEnt:=Length(TheColl);
  for iEnt in [1..nbEnt]
  do
    eEnt:=TheColl[iEnt];
    Print("Size ", eEnt[1], " attained ", eEnt[2], " times\n");
  od;
end;




Bank_ChangeStructure:=function(ThePrefix)
  local TheBankFile, ListRec, nbRec, iRec, eFileEXT, eFileFAC, eFile, TheCommand, TheInvFile, ListInv, eFileINV, eFileFACtouch;
  TheBankFile:=Concatenation(ThePrefix, "BankRecord");
  ListRec:=ReadAsFunction(TheBankFile)();
  nbRec:=Length(ListRec);
  Print("nbRec=", nbRec, "\n");
  for iRec in [1..nbRec]
  do
    eFileEXT:=Concatenation(ThePrefix, "AccountEXT_", String(iRec));
    SaveDataToFilePlusTouch(eFileEXT, ListRec[iRec]);
  od;
  Print("Individual EXT files created\n");
  #
  for iRec in [1..nbRec]
  do
    eFile:=Concatenation(ThePrefix, "Account_", String(iRec));
    eFileFAC:=Concatenation(ThePrefix, "AccountFAC_", String(iRec));
    TheCommand:=Concatenation("mv ", eFile, " ", eFileFAC);
    Exec(TheCommand);
    eFileFACtouch:=Concatenation(ThePrefix, "AccountFAC_", String(iRec), "_touch");
    SaveDataToFile(eFileFACtouch, 0);
  od;
  Print("Individual FAC files created\n");
  #
  TheInvFile:=Concatenation(ThePrefix, "ListInvariant");
  ListInv:=ReadAsFunction(TheInvFile)();
  for iRec in [1..nbRec]
  do
    eFileINV:=Concatenation(ThePrefix, "AccountINV_", String(iRec));
    SaveDataToFilePlusTouch(eFileINV, ListInv[iRec]);
  od;
  Print("Individual INV files created\n");
  RemoveFilePlusTouch(TheBankFile);
  RemoveFilePlusTouch(TheInvFile);
end;



Bank_Restructing:=function(ThePrefix, FuncKeep)
  local DoRemoval, DoMove, eInfoEXT, nbRec, ListStatus, iRec, nbVert, eVal, eFile, ListCorrIdx, nbCorr, iNew, iOld, TheInvFile, TheCommand, eFileEXT, eFileFAC, eFileINV;
  nbRec:=Bank_GetSize(ThePrefix);
  Print("nbRec=", nbRec, "\n");
  ListStatus:=[];
  for iRec in [1..nbRec]
  do
    eFileEXT:=Concatenation(ThePrefix, "AccountEXT_", String(iRec));
    eInfoEXT:=ReadAsFunction(eFileEXT)();
    nbVert:=Length(eInfoEXT.EXT);
    if FuncKeep(nbVert, iRec)=true then
      eVal:=1;
    else
      eVal:=0;
    fi;
    Add(ListStatus, eVal);
  od;
  for iRec in [1..nbRec]
  do
    if ListStatus[iRec]=0 then
      DoRemoval:=function(ePre)
        local eFile;
        eFile:=Concatenation(ThePrefix, ePre, String(iRec));
        Print("Removing file ", eFile, "\n");
        RemoveFile(eFile);
      end;
      DoRemoval("AccountFAC_");
      DoRemoval("AccountEXT_");
      DoRemoval("AccountINV_");
    fi;
  od;
  #
  ListCorrIdx:=Filtered([1..nbRec], x->ListStatus[x]=1);
  nbCorr:=Length(ListCorrIdx);
  Print("nbRec=", nbRec, " nbCorr=", nbCorr, "\n");
  for iNew in [1..nbCorr]
  do
    iOld:=ListCorrIdx[iNew];
    DoMove:=function(ePre)
      local eFileNew, eFileOld, TheCommand;
      eFileNew:=Concatenation(ThePrefix, ePre, String(iNew));
      eFileOld:=Concatenation(ThePrefix, ePre, String(iOld));
      TheCommand:=Concatenation("mv ", eFileOld, " ", eFileNew);
      Print("Moving file ", eFileOld, " to ", eFileNew, "\n");
      Exec(TheCommand);
    end;
    if iNew<>iOld then
      DoMove("AccountFAC_");
      DoMove("AccountEXT_");
      DoMove("AccountINV_");
    fi;
  od;
end;










# in this new version all incidences are encoded by sets.
__ProjectionLiftingFramework_Rational:=function(EXT, OneInc)
  local eSub, EXTproj, EXTproj2, FuncLift, RecReturn;
  eSub:=ProjectionFrame(EXT);
  EXTproj:=List(EXT, x->x{eSub});
  EXTproj2:=EXTproj{OneInc};
  # TheInc is a subset of [1..Length(OneInc)]
  RecReturn:=rec(EXT:=EXT, OneInc:=OneInc);
  if RankMat(EXT)=2 then
    FuncLift:=function(TheInc)
      return Difference([1..2], OneInc);
    end;
    RecReturn.FuncLift:=FuncLift;
    return RecReturn;
  fi;
  FuncLift:=function(TheInc)
    local LINCR, VMA, ListCase, eExt, VO, EXT1, iD, EXT2, det12, iElt, EXTN, det1N, det2N, LV, test, S, iV, eV, eInc, VCE;
    LINCR:=EXTproj2{TheInc};
    if TestConicness(EXTproj) then
      Add(LINCR, FacetOfInfinity(Length(LINCR[1])) );
    fi;
    VMA:=NullspaceMat(TransposedMat(LINCR));
    if Length(VMA)<>2 then
      Error("We have an incoherence in ProjectionLiftingFramework");
    fi;
    ListCase:=[];
    for eExt in EXTproj
    do
      VO:=[VMA[1]*eExt, VMA[2]*eExt];
      if VO<>[0,0] then
        Add(ListCase, VO);
      fi;
    od;
    EXT1:=ListCase[1];
    iD:=2;
    while(true)
    do
      EXT2:=ListCase[iD];
      det12:=EXT2[2]*EXT1[1]-EXT2[1]*EXT1[2];
      if (det12<>0) then
        break;
      fi;
      iD:=iD+1;
    od;
    for iElt in [iD+1..Length(ListCase)]
    do
      EXTN:=ListCase[iElt];
      det1N:=EXTN[2]*EXT1[1]-EXTN[1]*EXT1[2];
      det2N:=EXTN[2]*EXT2[1]-EXTN[1]*EXT2[2];
      if (det1N*det2N>0) then
        if (det12*det1N>0) then
          EXT2:=ShallowCopy(EXTN);
          det12:=det1N;
        else
          EXT1:=ShallowCopy(EXTN);
          det12:=-det2N;
        fi;
      fi;
    od;
    if (det12>0) then
      LV:=[[-EXT1[2], EXT1[1]], [EXT2[2], -EXT2[1]]];
    else
      LV:=[[EXT1[2], -EXT1[1]], [-EXT2[2], EXT2[1]]];
    fi;
    test:=[1,1];
    S:=[];
    for iV in [1,2]
    do
      eV:=LV[iV];
      S[iV]:=eV[1]*VMA[1]+eV[2]*VMA[2];
      for eInc in EXTproj2
      do
        if S[iV]*eInc<>0 then
          test[iV]:=0;
        fi;
      od;
    od;
    VCE:=S[Position(test, 0)];
    return Filtered([1..Length(EXTproj)], x->EXTproj[x]*VCE=0);
  end;
  RecReturn.FuncLift:=FuncLift;
  return RecReturn;
end;


__ProjectionLiftingFramework:=function(EXT, OneInc)
  local Nval;
  if IsMatrixRational(EXT)=true then
    return __ProjectionLiftingFramework_Rational(EXT, OneInc);
  fi;
  Error("You have to build your own arithmetic");
end;




#
# Data=rec(TheDepth:=...
#, ThePath:=..., IsBankSave:=false
#, IsBankSave:=...
#, IsRespawn:=...
#, GroupFormalism:=...
#, DualDescription:=...
#, Saving:=..., ThePathSave:=...
# This function computes the polyhedral description (given by incidences)
# of EXT and returns the orbits up to the symmetry group GivenSymmetry.
# GivenSymmetry should be used according to the group formalism specified in
#
# all tricks in the book are used:
# ---Bank formalism for storing used data
# ---Balinski theorem
# ---Recursive Adjacency decomposition method
# ---special symmetry groups of faces of the polytope
#
# saving system concerns only and exclusively the adjacency decomposition
# method itself, otherwise no save.
# the end result is that one can recover an interrupted computation
# with no error.
__ListFacetByAdjacencyDecompositionMethod:=function(EXT, GivenSymmetry, Data, BankFormalism)
  local RECListOrbit, IsFinished, eOrb, eInc, Ladj, SelectedOrbit, jOrb, MiniINCD, RPL, RPLift, testBank, OrdGRP, TheDim, WorkingSymGroup, LRES, NewData, RedStab, TheDate1, TheDate2, EllapsedTime, NewPathSave, TestNeedMoreSymmetry, ReturnedList, eSetUndone, nbUndone, testSym;
  if IsCorrectPath(Data.ThePathSave)=false then
    Print("Variable Data.ThePathSave=", Data.ThePathSave, " is incorrect\n");
    Error("It should finish with a /");
  fi;
  if IsDirectoryPath(Data.ThePathSave)=false and Data.Saving=true then
    Error("Directory Data.ThePathSave=", Data.ThePathSave, " is nonexistent");
  fi;
  if IsCorrectPath(Data.ThePath)=false then
    Print("Variable Data.ThePath=", Data.ThePath, " is incorrect\n");
    Error("It should finish with a /");
  fi;
  if IsDirectoryPath(Data.ThePath)=false then
    Error("Directory Data.ThePath=", Data.ThePath, " is nonexistent");
  fi;
#  Print("Before testBank\n");
  testBank:=BankFormalism.FuncRetrieveObject(EXT, GivenSymmetry);
#  Print("After testBank\n");
  if testBank<>false then
#    Print("Retrieve data from the bank\n");
    return Data.GroupFormalism.LiftingOrbits(EXT, testBank.ListOrbitFacet, GivenSymmetry, testBank.GRP);
  fi;
  TheDate1:=GetDate();
  # we would like to use IsBankSave but it is not possible with EllaspedTime
#  Print("Before TestNeedMoreSymmetry\n");
  TestNeedMoreSymmetry:=function(EXT)
    if Length(EXT)> RankMat(EXT)+4 then
      return true;
    else
      return false;
    fi;
  end;
  if IsBound(Data.TestNeedMoreSymmetry)=true then
    testSym:=Data.TestNeedMoreSymmetry(EXT);
  else
    testSym:=TestNeedMoreSymmetry(EXT);
  fi;
#  Print("After TestNeedMoreSymmetry\n");
  if testSym=true then
    WorkingSymGroup:=Data.GroupFormalism.GroupUnion(BankFormalism.FuncStabilizer(EXT), GivenSymmetry);
  else
    WorkingSymGroup:=GivenSymmetry;
  fi;
  OrdGRP:=Data.GroupFormalism.Order(WorkingSymGroup);
#  Print("OrdGRP=", OrdGRP, "\n");
  if Data.IsRespawn(OrdGRP, EXT, Data.TheDepth)=false then
    ReturnedList:=Data.DualDescriptionFunction(EXT, Data.GroupFormalism.ToPermGroup(EXT, GivenSymmetry), Data.ThePath);
    TheDate2:=GetDate();
    EllapsedTime:=TheDate2-TheDate1;
    if EllapsedTime > 10 then
      Print("EllapsedTime=", EllapsedTime, "\n");
    fi;
    if Data.IsBankSave(EllapsedTime, OrdGRP, EXT, Data.TheDepth)=true then
      Print("Before FuncCreateAccount\n");
      BankFormalism.FuncCreateAccount(EXT, GivenSymmetry, ReturnedList);
      Print("After FuncCreateAccount\n");
    fi;
  else
    TheDim:=RankMat(EXT)-1;
    Print("RESPAWN a new ADM computation |GRP|=", OrdGRP, " TheDim=", TheDim, " |EXT|=", Length(EXT), "\n");
#    FileSaveEXT:=Concatenation("EXT", String(Length(EXT)));
#    SaveDataToFile(FileSaveEXT, EXT);
    RPL:=Data.GroupFormalism.OrbitGroupFormalism(EXT, WorkingSymGroup, Data.ThePathSave, Data.Saving);
    Print("nbOrbit=", RPL.FuncNumberOrbit(), "\n");
    if RPL.FuncNumberOrbit()=0 then
      for eInc in Data.GetInitialRays(EXT, 10)
      do
        RPL.FuncInsert(eInc);
      od;
    fi;
    Print("Running the adjacency method recursively\n");
    while(true)
    do
      MiniINCD:=Length(EXT);
      SelectedOrbit:=-1;
      for jOrb in [1..RPL.FuncNumberOrbit()]
      do
        eOrb:=RPL.FuncRecord(jOrb);
        if eOrb.Status="NO" then
          if Length(eOrb.Inc)<MiniINCD then
            MiniINCD:=Length(eOrb.Inc);
            SelectedOrbit:=jOrb;
          fi;
        fi;
      od;
      eSetUndone:=RPL.ComputeIntersectionUndone();
      nbUndone:=RPL.FuncNumberUndone();
      if RPL.FuncNumberOrbitDone()>0 then
        if nbUndone<=TheDim-1 or Length(eSetUndone)>0 then
          Print("End of computation, nbObj=", RPL.FuncNumber(), " nbUndone=", nbUndone, " |eSetUndone|=", Length(eSetUndone), " Depth=", Data.TheDepth, " |EXT|=", Length(EXT), "\n");
          break;
        fi;
      fi;
      eOrb:=RPL.FuncRecord(SelectedOrbit);
      Print("\n");
      RedStab:=Data.GroupFormalism.Stabilizer(EXT, WorkingSymGroup, eOrb.Inc);
      Print("Considering orbit ", SelectedOrbit, " |inc|=", Length(eOrb.Inc), " Depth=", Data.TheDepth, " |stab|=", Order(RedStab), " dim=", TheDim, "\n");
      RPLift:=__ProjectionLiftingFramework(EXT, eOrb.Inc);
      NewPathSave:=Concatenation(Data.ThePathSave, "OrbitRespawn", String(SelectedOrbit), "/");
      CreateDirectoryPlusTest(NewPathSave, Data.Saving);
      NewData:=ShallowCopy(Data);
      NewData.TheDepth:=NewData.TheDepth+1;
      NewData.ThePathSave:=NewPathSave;
      Ladj:=__ListFacetByAdjacencyDecompositionMethod(EXT{eOrb.Inc}, RedStab, NewData, BankFormalism);
      Print("We treat ", Length(Ladj), " orbits\n");
      RemoveDirectoryPlusTest(NewPathSave, Data.Saving);
      for eInc in Ladj
      do
        RPL.FuncInsert(RPLift.FuncLift(eInc));
      od;
      RPL.FuncPutOrbitAsDone(SelectedOrbit);
      nbUndone:=RPL.FuncNumberUndone();
      Print("We have ", RPL.FuncNumberOrbit(), " orbits");
      Print("  Nr treated=", RPL.FuncNumberOrbitDone(), " orbits");
      Print("  nbUndone=", nbUndone);
      Print("\n");
    od;
    LRES:=RPL.FuncListOrbitIncidence();
    ReturnedList:=Data.GroupFormalism.LiftingOrbits(EXT, LRES, GivenSymmetry, WorkingSymGroup);
    TheDate2:=GetDate();
    EllapsedTime:=TheDate2-TheDate1;
    if EllapsedTime > 10 then
      Print("EllapsedTime=", EllapsedTime, "\n");
    fi;
    if Data.IsBankSave(EllapsedTime, OrdGRP, EXT, Data.TheDepth)=true then
      Print("Before FuncCreateAccount\n");
      BankFormalism.FuncCreateAccount(EXT, WorkingSymGroup, LRES);
      Print("After FuncCreateAccount\n");
    fi;
  fi;
  return ReturnedList;
end;



# A common set of functions for isomorphism
# in case of large polytopes
GetIAI_FromEXT_GRP:=function(EXT, GRP, TheLimit)
  local WorkingDim, FuncStabilizer, FuncIsomorphy, FuncInvariant;
  WorkingDim:=RankMat(EXT);
  FuncStabilizer:=function(EXTask)
    local GRPloc, ListGen, eGen, ListInc;
    if Length(EXTask) > TheLimit then
      ListInc:=Set(List(EXTask, x->Position(EXT, x)));
      if Length(ListInc) < WorkingDim+15 then
        return Group(());
      fi;
      GRPloc:=Stabilizer(GRP, ListInc, OnSets);
      ListGen:=[];
      for eGen in GeneratorsOfGroup(GRPloc)
      do
        Add(ListGen, PermList(List(ListInc, x->Position(ListInc, OnPoints(x, eGen)))));
      od;
      return PersoGroupPerm(ListGen);
    fi;
    return LinPolytope_Automorphism(EXTask);
  end;
  FuncIsomorphy:=function(EXT1, EXT2)
    local ePerm, ListInc1, ListInc2, TheReply;
    if Length(EXT1)<>Length(EXT2) then
      return false;
    fi;
    if Length(EXT1)>TheLimit or Length(EXT1) < WorkingDim+7 then
      ListInc1:=Set(List(EXT1, x->Position(EXT, x)));
      ListInc2:=Set(List(EXT2, x->Position(EXT, x)));
      ePerm:=RepresentativeAction(GRP, ListInc1, ListInc2, OnSets);
      if ePerm=fail then
        return false;
      else
        return PermList(List(ListInc1, x->Position(ListInc2, OnPoints(x, ePerm))));
      fi;
    fi;
    Print(" |EXT1|=", Length(EXT1), " |EXT2|=", Length(EXT2), "\n");
    TheReply:=LinPolytope_Isomorphism(EXT1, EXT2);
    if TheReply=false then
      return false;
    else
      return PermList(TheReply);
    fi;
  end;
  FuncInvariant:=function(EXT)
    local eInv;
    eInv:=LinPolytope_Invariant(EXT, TheLimit);
    return eInv;
  end;
  return rec(FuncInvariant:=FuncInvariant,
             FuncIsomorphy:=FuncIsomorphy,
             FuncStabilizer:=FuncStabilizer);
end;




GetStandardFCT_DualDescriptionStandard:=function(EXT, PermGRP)
  local IsRespawn, IsBankSave, WorkingDim, TmpDir, DataPolyhedral, FuncStabilizer, FuncIsomorphy, FuncInvariant, MyDualDescription, BF, IsMatch, Nval, NvalCopy, TheLimit, eRecIAI;
  if Length(Set(EXT))<>Length(EXT) then
    Error("you have illegal repetition of elements");
  fi;
  #
  WorkingDim:=RankMat(EXT);
  TheLimit:=500;
  eRecIAI:=GetIAI_FromEXT_GRP(EXT, PermGRP, TheLimit);
  FuncStabilizer:=eRecIAI.FuncStabilizer;
  FuncIsomorphy:=eRecIAI.FuncIsomorphy;
  FuncInvariant:=eRecIAI.FuncInvariant;
  IsRespawn:=function(OrdGRP, EXT, TheDepth)
    if OrdGRP>=50000 and TheDepth<=2 then
      return true;
    fi;
    if Length(EXT)<WorkingDim+7 then
      return false;
    fi;
    if OrdGRP<100 then
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
        ThePathSave:="/irrelevant/",
        GetInitialRays:=GetInitialRays_LinProg,
        ThePath:=TmpDir,
        GroupFormalism:=OnSetsGroupFormalism(500));
  DataPolyhedral.DualDescriptionFunction:=poly_private@DualDescriptionLRS_Reduction;
  DataPolyhedral.GetInitialRays:=GetInitialRays_LinProg;
  return rec(FuncStabilizer:=FuncStabilizer,
             FuncIsomorphy:=FuncIsomorphy,
             FuncInvariant:=FuncInvariant,
             DataPolyhedral:=DataPolyhedral);
end;


DualDescriptionStandard:=function(EXT, PermGRP)
  local BF, eRecGeneral;
  eRecGeneral:=GetStandardFCT_DualDescriptionStandard(EXT, PermGRP);
  BF:=BankRecording(rec(Saving:=false, BankPath:="/irrelevant/"), eRecGeneral.FuncStabilizer, eRecGeneral.FuncIsomorphy, eRecGeneral.FuncInvariant, OnSetsGroupFormalism(500));
  return __ListFacetByAdjacencyDecompositionMethod(EXT, PermGRP, eRecGeneral.DataPolyhedral, BF);
end;


ListAdjacentOrbitwise_Incidence:=function(EXT, TheStab, ListInc, Data, BankFormalism)
  local RPLift, Ladj;
  RPLift:=Data.ProjectionLiftingFramework(EXT, ListInc);
  Ladj:=__ListFacetByAdjacencyDecompositionMethod(EXT{ListInc}, SecondReduceGroupAction(TheStab, ListInc), Data, BankFormalism);
  return List(Ladj, RPLift.FuncLift);
end;


ListAdjacentOrbitwise_Facet:=function(EXT, TheStab, ListInc, Data, BankFormalism)
  local RPLift, Ladj;
  RPLift:=__ProjectionLiftingFramework(EXT, ListInc);
  Ladj:=__ListFacetByAdjacencyDecompositionMethod(EXT{ListInc}, SecondReduceGroupAction(TheStab, ListInc), Data, BankFormalism);
  return List(Ladj, x->FindFacetInequality(EXT, RPLift.FuncLift(x)));
end;


SamplingGroupFormalism:=function()
  local __LiftingOrbits, OnSetsRepresentativeAction, OnSetsStabilizer, GroupUnion, ToPermGroup, TheOrder, OnSetsIsSubgroup, OnSetsGroupConjugacy, OnSetsTransformIncidenceList, MyOrbitGroupFormalism, BankKeyInformation, BankCompleteInformation, BankGetVertexSet, BankGetGroup, BankGetListObject, BankGetForIsom, GetOrbitIntersection;
  __LiftingOrbits:=function(EXT, ListInc, SmallGroup, BigGroup)
    return ListInc;
  end;
  OnSetsStabilizer:=function(EXT, GRP, eInc)
    return SecondReduceGroupAction(Stabilizer(GRP, eInc, OnSets), eInc);
  end;
  GroupUnion:=function(Grp1, Grp2)
    return PersoGroupPerm(SmallGeneratingSet(Group(Union(GeneratorsOfGroup(Grp1), GeneratorsOfGroup(Grp2)))));
  end;
  ToPermGroup:=function(EXT, Grp)
    return Grp;
  end;
  TheOrder:=function(GRP)
    return Order(GRP);
  end;
  OnSetsIsSubgroup:=function(GRP1, GRP2)
    return IsSubgroup(GRP1, GRP2);
  end;
  OnSetsGroupConjugacy:=function(GRP, eElt)
    local NewGens, eGen;
    NewGens:=[];
    for eGen in GeneratorsOfGroup(GRP)
    do
      Add(NewGens, eElt^(-1)*eGen*eElt);
    od;
    return PersoGroupPerm(NewGens);
  end;
  OnSetsTransformIncidenceList:=function(ListEXT1, ListEXT2, TheEquiv, ListListInc)
    return List(ListListInc, x->OnSets(x, TheEquiv));
  end;
  MyOrbitGroupFormalism:=function(EXT, TheGroup, Prefix, SavingTrigger)
    local FuncInvariant, FuncIsomorphy, FuncInvariantUpdate, OrderLincStabilizer, FuncGetInitialDisc;
    FuncGetInitialDisc:=function()
      return [];
    end;
    FuncInvariant:=function(Odisc, Linc)
      return Length(Linc);
    end;
    FuncIsomorphy:=function(Linc1, Linc2)
      return true;
    end;
    FuncInvariantUpdate:=function(OdiscPrev, nbCall)
      return [];
    end;
    OrderLincStabilizer:=function(Linc)
      return Order(Stabilizer(TheGroup, Linc, OnSets));
    end;
    GetOrbitIntersection:=function(eSet)
      return [];
    end;
    return OrbitGroupFormalism(EXT, TheGroup, Prefix, SavingTrigger,
        rec(FuncGetInitialDisc:=FuncGetInitialDisc,
            FuncInvariant:=FuncInvariant,
            FuncIsomorphy:=FuncIsomorphy,
            GroupOrder:=Order(TheGroup),
            OrderLincStabilizer:=OrderLincStabilizer,
            GetOrbitIntersection:=GetOrbitIntersection,
            FuncInvariantUpdate:=FuncInvariantUpdate));
  end;
  BankKeyInformation:=function(EXT, GroupExt)
    return rec(EXT:=EXT, Group:=GroupExt);
#    return EXT; I was right not to be sure.
  end;
  BankCompleteInformation:=function(EXT, GroupExt, ListObject)
    return ListObject;
  end;
  BankGetVertexSet:=function(TheKey, TheComplete)
    return TheKey.EXT;
  end;
  BankGetGroup:=function(TheKey, TheComplete)
    return TheKey.Group;
  end;
  BankGetListObject:=function(TheComplete)
    return TheComplete;
  end;
  BankGetForIsom:=function(TheKey)
    return TheKey.EXT;
  end;
  return rec(
    Stabilizer:=OnSetsStabilizer,
    LiftingOrbits:=__LiftingOrbits,
    GroupUnion:=GroupUnion,
    ToPermGroup:=ToPermGroup,
    Order:=TheOrder,
    IsSubgroup:=OnSetsIsSubgroup,
    GroupConjugacy:=OnSetsGroupConjugacy,
    TransformIncidenceList:=OnSetsTransformIncidenceList,
    OrbitGroupFormalism:=MyOrbitGroupFormalism,
    BankKeyInformation:=BankKeyInformation,
    BankCompleteInformation:=BankCompleteInformation,
    BankGetForIsom:=BankGetForIsom,
    BankGetVertexSet:=BankGetVertexSet,
    BankGetGroup:=BankGetGroup,
    BankGetListObject:=BankGetListObject);
end;



GetStandardFCT_SamplingFacets:=function(EXT, TheNB)
  local IsRespawn, IsBankSave, WorkingDim, TmpDir, DataPolyhedral, FuncStabilizer, FuncIsomorphy, FuncInvariant, MyDualDescription, BF, IsMatch, Nval, NvalCopy, TheFCT;
  if Length(Set(EXT))<>Length(EXT) then
    Error("you have illegal repetition of elements");
  fi;
  WorkingDim:=RankMat(EXT);
  #
  FuncStabilizer:=function(EXTask)
    return Group(());
  end;
  FuncIsomorphy:=function(EXT1, EXT2)
    return false;
  end;
  FuncInvariant:=function(EXT)
    return Length(EXT);
  end;
  #
  IsRespawn:=function(OrdGRP, EXT, TheDepth)
    if Length(EXT)<WorkingDim+TheNB then
      return false;
    fi;
    return true;
  end;
  IsBankSave:=function(EllapsedTime, OrdGRP, EXT, TheDepth)
    return false;
  end;
  TmpDir:=Filename(POLYHEDRAL_tmpdir, "");
  DataPolyhedral:=rec(IsBankSave:=IsBankSave,
        TheDepth:=0,
        IsRespawn:=IsRespawn,
        GetInitialRays:=GetInitialRays_LinProg,
        Saving:=false,
        ThePathSave:="/irrelevant/",
        ThePath:=TmpDir,
        GroupFormalism:=SamplingGroupFormalism());
  TheFCT:=function(EXT, GroupExt, ThePath)
    return GetInitialRays_LinProg(EXT, 20);
  end;
  if IsMatrixRational(EXT) then
    DataPolyhedral.DualDescriptionFunction:=TheFCT;
    DataPolyhedral.GetInitialRays:=GetInitialRays_LinProg;
  else
    Error("No code right now");
  fi;
  return rec(FuncStabilizer:=FuncStabilizer,
             FuncIsomorphy:=FuncIsomorphy,
             FuncInvariant:=FuncInvariant,
             DataPolyhedral:=DataPolyhedral);
end;

SamplingStandard:=function(EXT)
  local BF, eRecGeneral, PermGRP;
  eRecGeneral:=GetStandardFCT_SamplingFacets(EXT, 5);
  PermGRP:=Group(());
  BF:=BankRecording(rec(Saving:=false, BankPath:="/irrelevant/"), eRecGeneral.FuncStabilizer, eRecGeneral.FuncIsomorphy, eRecGeneral.FuncInvariant, OnSetsGroupFormalism(500));
  return __ListFacetByAdjacencyDecompositionMethod(EXT, PermGRP, eRecGeneral.DataPolyhedral, BF);
end;


SamplingStandardLevel:=function(EXT, TheLevel)
  local BF, eRecGeneral, PermGRP;
  eRecGeneral:=GetStandardFCT_SamplingFacets(EXT, TheLevel);
  PermGRP:=Group(());
  BF:=BankRecording(rec(Saving:=false, BankPath:="/irrelevant/"), eRecGeneral.FuncStabilizer, eRecGeneral.FuncIsomorphy, eRecGeneral.FuncInvariant, OnSetsGroupFormalism(500));
  return __ListFacetByAdjacencyDecompositionMethod(EXT, PermGRP, eRecGeneral.DataPolyhedral, BF);
end;






SamplingStandard_Group:=function(EXT, PermGRP)
  local ListOrbitLinProg, FuncInsert, eSet;
  ListOrbitLinProg:=[];
  FuncInsert:=function(eSet)
    local eOrbit;
    for eOrbit in ListOrbitLinProg
    do
      if RepresentativeAction(PermGRP, eSet, eOrbit, OnSets)<>fail then
        return;
      fi;
    od;
    Print("Find a new orbit of length ", Length(eSet), "\n");
    Add(ListOrbitLinProg, eSet);
  end;
  for eSet in SamplingStandard(EXT)
  do
    FuncInsert(eSet);
  od;
  return ListOrbitLinProg;
end;


# We have a polytope P defined by vertices, we have
# a vector v inside P.
# We return a facet F such that v is contained in the
# prism conv(F, Iso(P))
GetContainingPrism:=function(EXT, eVect)
  local eIso, nb, ListSet, eSet, EXTprism, ListVect, eRel, RPLift, fSet, gSet;
  eIso:=Isobarycenter(EXT);
  if Length(EXT[1])<>Length(eVect) then
    Error("Length inconsistency between EXT and eVect");
  fi;
  if SolutionMat(EXT, eVect)=fail then
    Error("The vector is not in the linear space spanned by the polytope");
  fi;
  if SearchPositiveRelationSimple(Concatenation(EXT, [-eVect]))=false then
    Error("The vector is outside of the polytope");
  fi;
  nb:=1;
  ListSet:=GetInitialRays_LinProg(EXT, nb);
  eSet:=ListSet[1];
  while(true)
  do
    EXTprism:=Concatenation(EXT{eSet}, [eIso]);
    ListVect:=Concatenation(EXTprism, [-eVect]);
    eRel:=SearchPositiveRelationSimple(ListVect);
    if eRel<>false then
      return eSet;
    fi;
    RPLift:=__ProjectionLiftingFramework(EXT, eSet);
    fSet:=GetViolatedFacet(EXTprism, eVect);
    if Position(fSet, Length(eSet)+1)=fail then
      Error("We just found a bug");
    fi;
    gSet:=Difference(fSet, [Length(eSet)+1]);
    eSet:=RPLift.FuncLift(gSet);
  od;
end;


GetContainingSimplex:=function(EXT, eVect)
  local TheDim, eSet, eIsoCell, eIso, eDiff, ListVect, eSol, eProjVect, i, TheRec, NewListVert, NewListSet;
  if Length(EXT)=1 then
    if IsProportionalVector(EXT[1], eVect)=false then
      Error("eVect should be equal to the single vertex");
    fi;
    return rec(ListVert:=[EXT[1]], ListSet:=[[1]]);
  fi;
  TheDim:=Length(EXT[1]);
  eSet:=GetContainingPrism(EXT, eVect);
  eIsoCell:=Isobarycenter(EXT{eSet});
  eIso:=Isobarycenter(EXT);
  eDiff:=eIso - eIsoCell;
  ListVect:=Concatenation(EXT{eSet}, [eDiff]);
  eSol:=SolutionMat(ListVect, eVect);
  eProjVect:=ListWithIdenticalEntries(TheDim,0);
  for i in [1..Length(eSet)]
  do
    eProjVect:=eProjVect + eSol[i]*EXT[eSet[i]];
  od;
  TheRec:=GetContainingSimplex(EXT{eSet}, eProjVect);
  NewListVert:=Concatenation(TheRec.ListVert, [eIso]);
  NewListSet:=Concatenation(List(TheRec.ListSet, x->eSet{x}), [[1..Length(EXT)]]);
  return rec(ListVert:=NewListVert, ListSet:=NewListSet);
end;
