FileSympolOrbitFacePolytopeLP:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"Temp_StandaloneOrbitFacePolytopeLP");
FileFaceLattice:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"POLY_FaceLatticeDirect");



GetCompleteListFaces:=function(EXT, FAC)
  local FileI, FileO, FileErr, output, TheCommand, eSymbol;
  FileI:=Filename(POLYHEDRAL_tmpdir, "FileIn");
  FileO:=Filename(POLYHEDRAL_tmpdir, "FileOut");
  FileErr:=Filename(POLYHEDRAL_tmpdir, "FileErr");
  output:=OutputTextFile(FileI, true);
  AppendTo(output, Length(EXT), " ", Length(EXT[1]), "\n");
  WriteMatrix(output, EXT);
  AppendTo(output, Length(FAC), " ", Length(FAC[1]), "\n");
  WriteMatrix(output, FAC);
  CloseStream(output);
  #
  TheCommand:=Concatenation(FileFaceLattice, " ", FileI, " ", FileO, " 2> ", FileErr);
  Exec(TheCommand);
  #
  eSymbol:=ReadAsFunction(FileO)();
  RemoveFileIfExist(FileI);
  RemoveFileIfExist(FileO);
  RemoveFileIfExist(FileErr);
  return eSymbol;
end;



#
# given a flag, we move the element in position i by changing it,
# while remaining a flag. Only one solution to the problem possibility.
FlagDisplacement:=function(FlagEXT, EXT, FAC, iMov)
  local FlagEXTnew, LFAC, iFac, test, ListSET, ListLFAC, jMov, LSE, LS1, LS2, eList;
  FlagEXTnew:=ShallowCopy(FlagEXT);
  if iMov=1 then
    FlagEXTnew[1]:=[Difference(FlagEXT[2],FlagEXT[1])[1]];
    return FlagEXTnew;
  fi;
  if iMov=Length(FlagEXT) then
    LFAC:=[];
    for iFac in [1..Length(FAC)]
    do
      test:=First(FlagEXT[iMov-1], x->EXT[x]*FAC[iFac]<>0);
      if test=fail then
        Add(LFAC, iFac);
      fi;
    od;
    LS1:=Filtered([1..Length(EXT)], x->EXT[x]*FAC[LFAC[1]]=0);
    LS2:=Filtered([1..Length(EXT)], x->EXT[x]*FAC[LFAC[2]]=0);
    ListSET:=[LS1, LS2];
    if FlagEXT[iMov]=ListSET[1] then
      FlagEXTnew[iMov]:=ListSET[2];
      return FlagEXTnew;
    fi;
    if FlagEXT[iMov]=ListSET[2] then
      FlagEXTnew[iMov]:=ListSET[1];
      return FlagEXTnew;
    fi;
  fi;
  ListLFAC:=[];
  for jMov in [1..2]
  do
    eList:=[];
    for iFac in [1..Length(FAC)]
    do
      test:=First(FlagEXT[jMov+iMov-2], x->EXT[x]*FAC[iFac]<>0);
      if test=fail then
        Add(eList, iFac);
      fi;
    od;
    Add(ListLFAC, eList);
  od;
  for iFac in Difference(ListLFAC[1], ListLFAC[2])
  do
    LSE:=Filtered(FlagEXT[iMov+1], x->EXT[x]*FAC[iFac]=0);
    if LSE<>FlagEXT[iMov-1] then
      FlagEXTnew[iMov]:=LSE;
      return FlagEXTnew;
    fi;
  od;
end;



SPAN_face_Redcheck:=function(face, Stabface, ListFacets)
  local RelIFace, NSP, ListChar, iFace, eFace, CharVect, SetChar, ListGroup, eChar, ListIdx, AddZeroChar, TheRed, ListNewFaces, iGR, SetFunc, FuncInsert;
  NSP:=NullspaceMat(TransposedMat(ListFacets{face}));
  ListChar:=[];
  RelIFace:=Difference([1..Length(ListFacets)], face);
  for iFace in RelIFace
  do
    eFace:=ListFacets[iFace];
    CharVect:=RemoveFraction(eFace*TransposedMat(NSP));
    Add(ListChar, CharVect);
  od;
  SetChar:=Set(ListChar);
  ListGroup:=[];
  for eChar in SetChar
  do
    ListIdx:=Filtered([1..Length(ListChar)], x->ListChar[x]=eChar);
    Add(ListGroup, RelIFace{ListIdx});
  od;
  AddZeroChar:=List(SetChar, x->Concatenation([0], x));
  TheRed:=RedundancyCheck(AddZeroChar);
  ListNewFaces:=[];
  SetFunc:=OnSetsFunctions(Stabface);
  FuncInsert:=function(eSet)
    local eInv, eOrb;
    eInv:=SetFunc.FuncInvariant(eSet);
    for eOrb in ListNewFaces
    do
      if eOrb.eInv=eInv then
        if SetFunc.FuncIsomorphy(eOrb.eSet, eSet)=true then
          return;
        fi;
      fi;
    od;
    Add(ListNewFaces, rec(eInv:=eInv, eSet:=eSet));
  end;
  for iGR in TheRed
  do
    FuncInsert(Union(face, Set(ListGroup[iGR])));
  od;
  return List(ListNewFaces, x->x.eSet);
end;


DetermineFacetsAmongList:=function(ListInequalities, PermGRP)
  local  nbV, ListFacets, O, eO, pos, ListInputVect, ListStrictPos, ListPos, iVect, TheConstraint, test;
  nbV:=Length(ListInequalities);
  ListFacets:=[];
  O:=Orbits(PermGRP, [1..nbV], OnPoints);
  for eO in O
  do
    pos:=eO[1];
    ListInputVect:=[];
    ListStrictPos:=[];
    ListPos:=[];
    for iVect in [1..nbV]
    do
      if iVect=pos then
        Add(ListInputVect, -ListInequalities[iVect]);
        Add(ListStrictPos, iVect);
      else
        Add(ListInputVect, ListInequalities[iVect]);
        Add(ListPos, iVect);
      fi;
    od;
    TheConstraint:=rec(ListStrictlyPositive:=ListStrictPos, ListPositive:=ListPos, ListSetStrictPositive:=[]);
    test:=SearchPositiveRelation(ListInputVect, TheConstraint);
    if test=false then
      Append(ListFacets, eO);
    fi;
  od;
  return ListFacets;
end;


#
# This function has given me lots and lots of trouble.
# The idea is that if a face F is defined by vertices v1, ... vp
# among all vertices v1, ....., vn
# then there does not exist lambda1, ...., lambdaN
# with lambdaI >=0 and sum lambdaI > 0
# and
# mu1, ...., muP  with muJ >=0
# such that
# lambda1 v1 + .... lambdaN vn = mu1 v1 + .... + muP vP
# Any other formulation is WRONG.
SPAN_face_LinearProgramming:=function(face, Stabface, ListFacets, GroupFac, BoundingSet)
  local Treated, iFac, ListFacetsFace, u, ListSpannedFaces, jFac, test, ListCandidates, iKRN, TestMat, KRN, ListVectors, A, VSum, VSum2, DeterSet, RED, reply, eSet, TheDim, ListSelect, TheStab, TheSum, O1, eO1, O2, eO2, eSetSe, TheConstraint, ListConstPos, TheSumAve, eSetProj, BasisSpann, ListVectSpann, TheTot, eSol, SetListVectors, nbVectSet, eCand;
  Treated:=ListWithIdenticalEntries(Length(ListFacets), 0);
  Treated{face}:=ListWithIdenticalEntries(Length(face), 1);
  ListFacetsFace:=ListFacets{face};
  TheDim:=Length(ListFacets[1]);
  ListSpannedFaces:=[];
  for iFac in [1..Length(ListFacets)]
  do
    if Treated[iFac]=0 then
      TestMat:=Union(ListFacetsFace, [ListFacets[iFac]]);
      KRN:=NullspaceMat(TransposedMat(TestMat));
      eCand:=[];
      VSum:=0;
      for jFac in [1..Length(ListFacets)]
      do
        test:=First(KRN, x->x*ListFacets[jFac]<>0);
        if test=fail then
          Add(eCand, jFac);
          VSum:=VSum+ListFacets[jFac];
        fi;
      od;
      for eSet in Orbit(Stabface, eCand, OnSets)
      do
        Treated{eSet}:=ListWithIdenticalEntries(Length(eSet),1);
      od;
      DeterSet:=Filtered(BoundingSet, x->VSum*x=0);
      if Length(DeterSet)=0 then
        VSum2:=ListWithIdenticalEntries(TheDim,0);
      else
        VSum2:=Sum(DeterSet);
      fi;
      TheStab:=Stabilizer(GroupFac, eCand, OnSets);
      ListVectors:=[];
      ListConstPos:=[];
      O1:=Orbits(TheStab, eCand, OnPoints);
      ListVectSpann:=[];
      for eO1 in O1
      do
        TheSum:=ListWithIdenticalEntries(TheDim,0);
        for jFac in eO1
        do
          TheSum:=TheSum-ListFacets[jFac];
        od;
        TheSumAve:=TheSum/Length(eO1);
        Add(ListVectSpann, TheSumAve);
      od;
      BasisSpann:=RowReduction(ListVectSpann).EXT;
      TheTot:=RowReduction(Concatenation(BasisSpann, IdentityMat(TheDim))).EXT;
      eSetProj:=[1+Length(BasisSpann)..Length(TheTot)];
      ListSelect:=Filtered(Difference([1..Length(ListFacets)], eCand), x->VSum2*ListFacets[x]=0);
      O2:=Orbits(TheStab, ListSelect, OnPoints);
      for eO2 in O2
      do
        TheSum:=ListWithIdenticalEntries(TheDim,0);
        for jFac in eO2
        do
          TheSum:=TheSum+ListFacets[jFac];
        od;
        eSol:=SolutionMat(TheTot, TheSum/Length(eO2));
        Add(ListVectors, RemoveFraction(eSol{eSetProj}));
      od;
      SetListVectors:=Set(ListVectors);
      nbVectSet:=Length(SetListVectors);
      ListConstPos:=[1..nbVectSet];
      eSetSe:=[1..nbVectSet];
      TheConstraint:=rec(ListStrictlyPositive:=[], ListPositive:=ListConstPos, ListSetStrictPositive:=[eSetSe]);
      if Length(SetListVectors)=0 then
        test:=false;
      else
        test:=SearchPositiveRelation(SetListVectors, TheConstraint);
      fi;
      if test=false then
        Add(ListSpannedFaces, eCand);
      fi;
    fi;
  od;
  return ListSpannedFaces;
end;



#
# given a k-dimensional face given as intersection of facets, this procedure
# returns the list of all k-1 dimensional faces contained in it.
# face is a list of indexes for FAC
SPAN_face_ExtremeRay:=function(FaceFAC, Stabface, FAC, EXT)
  local eExt, ListInc, iFac, test, k, Treated, u, LIST, TestMat, VCT, eInc, jFac, PropList, iInc, TestRank, eSet;
  # selection of the list of incidents
  ListInc:=[];
  for eExt in EXT
  do
    if First(FaceFAC, x->FAC[x]*eExt<>0)=fail then
      Add(ListInc, eExt);
    fi;
  od;
  k:=ZeroRankMat(ListInc);
  Treated:=ListWithIdenticalEntries(Length(FAC),0);
  Treated{FaceFAC}:=ListWithIdenticalEntries(Length(FaceFAC), 1);
  LIST:=[];
  TestRank:=function(TheMat)
    if Length(TheMat)>=k-1 then
      return RankMat(TheMat)=k-1;
    fi;
    return false;
  end;
  for iFac in [1..Length(FAC)]
  do
    if Treated[iFac]=0 then
      TestMat:=Filtered(ListInc, x->x*FAC[iFac]=0);
      if TestRank(TestMat)=true then
        PropList:=[];
        for jFac in [1..Length(FAC)]
        do
          if First(TestMat, x->x*FAC[jFac]<>0)=fail then
            Add(PropList, jFac);
          fi;
        od;
        for eSet in Orbit(Stabface, PropList, OnSets)
        do
          Treated{eSet}:=ListWithIdenticalEntries(Length(eSet),1);
        od;
        Add(LIST, PropList);
      fi;
    fi;
  od;
  return LIST;
end;


SPAN_face_TotalChecks:=function(face, Stabface, ListFacets, GroupFac, BoundingSet)
  local TheSpannLP, TheSpannEXT, EXT, nbOrbLP, nbOrbEXT, iOrb, jOrb, eRepr, ListFound, ListFoundSub;
  TheSpannLP:=SPAN_face_LinearProgramming(face, Stabface, ListFacets, GroupFac, []);
  EXT:=DualDescription(ListFacets);
  TheSpannEXT:=SPAN_face_ExtremeRay(face, Stabface, ListFacets, EXT);
  nbOrbLP:=Length(TheSpannLP);
  nbOrbEXT:=Length(TheSpannEXT);
  if nbOrbLP<>nbOrbEXT then
    Error("We do not find same number of orbit by two methods, BUG");
  fi;
  for iOrb in [1..nbOrbLP-1]
  do
    for jOrb in [iOrb+1..nbOrbLP]
    do
      eRepr:=RepresentativeAction(Stabface, TheSpannLP[iOrb], TheSpannLP[jOrb], OnSets);
      if eRepr<>fail then
        Error("Please panic, we have equivalence problem 1");
      fi;
      eRepr:=RepresentativeAction(Stabface, TheSpannEXT[iOrb], TheSpannEXT[jOrb], OnSets);
      if eRepr<>fail then
        Error("Please panic, we have equivalence problem 2");
      fi;
    od;
  od;
  ListFound:=[];
  for iOrb in [1..nbOrbLP]
  do
    ListFoundSub:=[];
    for jOrb in [1..nbOrbLP]
    do
      eRepr:=RepresentativeAction(Stabface, TheSpannLP[iOrb], TheSpannEXT[jOrb], OnSets);
      if eRepr<>fail then
        Add(ListFoundSub, jOrb);
      fi;
    od;
    if Length(ListFoundSub)<>1 then
      Error("We have inconsistency in orbit finding, please panic");
    fi;
    Add(ListFound, ListFoundSub[1]);
  od;
  return TheSpannLP;
end;


IsFlag:=function(EXT, eFlagEXT)
  local len, i, eSet1, eSet2, EXTrel, eRecRed, EXTrelRed, eSetTest, testineq;
  len:=Length(eFlagEXT);
  for i in [1..len]
  do
    eSet1:=eFlagEXT[i];
    if i<len then
      eSet2:=eFlagEXT[i+1];
    else
      eSet2:=[1..Length(EXT)];
    fi;
    EXTrel:=EXT{eSet2};
    eRecRed:=ColumnReduction(EXTrel);
    EXTrelRed:=List(EXTrel, x->x{eRecRed.Select});
    eSetTest:=List(eSet1, x->Position(eSet2, x));
    testineq:=FindFacetInequalityAndTest(EXTrelRed, eSetTest);
    if testineq.success=false then
      return false;
    fi;
  od;
  return true;
end;


ListFlagOrbit:=function(GroupExt, EXT, FAC)
  local O, ListOrbitPrec, i, dimension, ListOrbitNew, eOrbPrec, eface, FlagNew, TheStab;
  if TestConicness(FAC)=true then
    dimension:=Length(FAC[1])-2;
  else
    dimension:=Length(FAC[1])-1;
  fi;
  O:=Orbits(GroupExt, [1..Length(EXT)]);
  ListOrbitPrec:=List(O, x->[  [x[1]]  ]);
  Print("For i=1  one finds ", Length(ListOrbitPrec), " orbits\n");
  for i in [2..dimension]
  do
    ListOrbitNew:=[];
    for eOrbPrec in ListOrbitPrec
    do
      TheStab:=OnTuplesSetsStabilizer(GroupExt, eOrbPrec);
      for eface in SPAN_face_ExtremeRay(eOrbPrec[i-1], TheStab, EXT, FAC)
      do
        FlagNew:=Concatenation(eOrbPrec, [eface]);
        AddSet(ListOrbitNew, OnTuplesSetsCanonicalization(GroupExt, FlagNew));
      od;
    od;
    ListOrbitPrec:=ShallowCopy(ListOrbitNew);
    Print("For i=", i, "  one finds ", Length(ListOrbitPrec), " orbits\n");
  od;
  return ListOrbitNew;
end;



#
# extract the orbits from ListElt and give datas on it.
ExtractOrbit:=function(G, ListElt, Action)
  local U, ListO, ListSizes, ListAppear, ListOrbits, Orb, OrbC;
  U:=ShallowCopy(ListElt);
  ListO:=[];
  ListSizes:=[];
  ListAppear:=[];
  ListOrbits:=[];
  while(Length(U)>0)
  do
    Orb:=Orbit(G, U[1], Action);
    OrbC:=Set(Orb);
    Add(ListO, Minimum(Orb));
    Add(ListSizes, Length(Orb));
    Add(ListAppear, Length(Intersection(U,OrbC)));
    Add(ListOrbits, OrbC);
    U:=Difference(U, OrbC);
  od;
  return rec(OrbitRepresentent:=ListO, OrbitSizes:=ListSizes, Appearance:=ListAppear, Orbits:=ListOrbits);
end;




#this procedure span a list of orbits of faces of dimension k-1
#from a list of orbits of faces of dimension k
#SPAN_K_Faces:=function(GroupFac, ListFace, FAC, SPAN_function)
#  local iFace, iOrb, iO, ListO, ListSizes, ListAppear, ListTotal, OSAO, pos;
#  ListO:=[];
#  ListSizes:=[];
#  ListAppear:=[];
#  ListTotal:=[];
#  for iFace in [1..Length(ListFace)]
#  do
#    OSAO:=ExtractOrbit(GroupFac, SPAN_function(ListFace[iFace], FAC), OnSets);
#    for iOrb in [1..Length(OSAO.OrbitRepresentent)]
#    do
#      pos:=0;
#      for iO in [1..Length(ListO)]
#      do
#        if OSAO.OrbitRepresentent[iOrb]=ListO[iO] then
#          pos:=iO;
#        fi;
#      od;
#      if pos=0 then
#        Add(ListO, OSAO.OrbitRepresentent[iOrb]);
#        Add(ListSizes, OSAO.OrbitSizes[iOrb]);
#        Add(ListAppear, [[iFace,OSAO.Appearance[iOrb]]]);
#        Add(ListTotal, OSAO.Orbits[iOrb]);
#      else
#        Add(ListAppear[pos], [iFace, OSAO.Appearance[iOrb]]);
#      fi;
#    od;
#  od;
#  return rec(OrbitRepresentent:=ListO, OrbitSizes:=ListSizes, Preceding:=ListAppear, Orbits:=ListTotal);
#end;


SPAN_K_Faces:=function(GroupFac, ListFace, FAC, SPAN_function)
  local TheFormal, TheSpann, RPL, iFace, eFAC, iOrb, TheRecord, ListSizes, ListRepresentent, nbFace, TheStab, ListStabilizer;
  TheFormal:=OnSetsGroupFormalism(500);
  RPL:=TheFormal.OrbitGroupFormalism(FAC, GroupFac, "/irrelevant/", false);
  for iFace in [1..Length(ListFace)]
  do
    TheStab:=Stabilizer(GroupFac, ListFace[iFace], OnSets);
    TheSpann:=SPAN_function(ListFace[iFace], TheStab, FAC);
    for eFAC in TheSpann
    do
      RPL.FuncInsert(eFAC);
    od;
  od;
  ListRepresentent:=[];
  ListSizes:=[];
  ListStabilizer:=[];
  for iOrb in [1..RPL.FuncNumberOrbit()]
  do
    TheRecord:=RPL.FuncRecord(iOrb);
    Add(ListRepresentent, TheRecord.Inc);
    Add(ListSizes, TheRecord.OrbSize);
    TheStab:=Stabilizer(GroupFac, TheRecord.Inc, OnSets);
    Add(ListStabilizer, TheStab);
  od;
  nbFace:=RPL.FuncNumber();
  return rec(ListRepresentent:=ListRepresentent, ListStabilizer:=ListStabilizer, ListSizes:=ListSizes, nbFace:=nbFace);
end;

#
# create the list of all k_skelettons together with their sizes, listappear
KernelSkeletonSearch:=function(GroupFac, FAC, LevSearch, SPAN_function)
  local ListOrbit, ListInfos, iK, ListOrbitRepr, ListSizes, ListStabilizer;
  ListOrbit:=Orbits(GroupFac, Combinations([1..Length(FAC)], 1), OnSets);
  ListOrbitRepr:=List(ListOrbit, x->x[1]);
  ListStabilizer:=List(ListOrbitRepr, x->Stabilizer(GroupFac, x, OnSets));
  ListSizes:=List(ListOrbit, Length);
  ListInfos:=[rec(ListRepresentent:=ListOrbitRepr, ListSizes:=ListSizes, ListStabilizer:=ListStabilizer, nbFace:=Sum(ListSizes))];
  Print("Step 1  |Orbit|=", Length(ListSizes), "  nbFace=", Sum(ListSizes), "\n");
  for iK in [2..LevSearch]
  do
    Add(ListInfos, SPAN_K_Faces(GroupFac, ListInfos[iK-1].ListRepresentent, FAC, SPAN_function));
    Print("Step ", iK, "  |Orbit|=", Length(ListInfos[iK].ListSizes), "  nbFace=", Sum(ListInfos[iK].ListSizes), "\n");
  od;
  return ListInfos;
end;



CreateK_skeletton:=function(GroupFac, FAC, EXT)
  local LevSearch, SPAN_function;
  LevSearch:=RankMat(FAC)-1;
  SPAN_function:=function(face, TheStab, FAC)
    return SPAN_face_ExtremeRay(face, TheStab, FAC, EXT);
  end;
  return KernelSkeletonSearch(GroupFac, FAC, LevSearch, SPAN_function);
end;



IncompleteSkeletonSearch:=function(GroupFac, FAC, BoundingSet, LevSearch)
  local SPAN_function;
  SPAN_function:=function(face, TheStab, FAC)
    return SPAN_face_LinearProgramming(face, TheStab, FAC, GroupFac, BoundingSet);
  end;
  return KernelSkeletonSearch(GroupFac, FAC, LevSearch, SPAN_function);
end;

SYMPOL_IncompleteSkeletonSearch:=function(GroupFac, FAC, LevSearch)
  local FileFAC, FileGRP, FileOUT, nbFAC, TheCommand, ListListRepr;
  FileFAC:=Filename(POLYHEDRAL_tmpdir,"Desc.fac");
  FileGRP:=Filename(POLYHEDRAL_tmpdir,"Desc.grp");
  FileOUT:=Filename(POLYHEDRAL_tmpdir,"Desc.out");
  nbFAC:=Length(FAC);
  SYMPOL_PrintMatrix(FileFAC, FAC);
  SYMPOL_PrintGroup(FileGRP, nbFAC, GroupFac);
  #
  TheCommand:=Concatenation(FileSympolOrbitFacePolytopeLP, " ", FileFAC, " ", FileGRP, " ", String(LevSearch-1), " ", FileOUT);
  Print("TheCommand=", TheCommand, "\n");
  Exec(TheCommand);
  #
  ListListRepr:=ReadAsFunction(FileOUT)();
  RemoveFileIfExist(FileFAC);
  RemoveFileIfExist(FileGRP);
  RemoveFileIfExist(FileOUT);
  return ListListRepr;
end;





UntangleAllSigns:=function(ListOccuringCases, nbVar)
  local nbEqs, VectorSign, AssignVector, UsedStatus, nbUnusedEq, iCase, eCase, ListIdx, ListSign, TheSum, TheVal, RefIdx, OthIdx;
  nbEqs:=Length(ListOccuringCases);
  VectorSign:=ListWithIdenticalEntries(nbVar, 0);
  VectorSign[1]:=1;
  AssignVector:=ListWithIdenticalEntries(nbVar, 0);
  AssignVector[1]:=1;
  UsedStatus:=ListWithIdenticalEntries(nbEqs, 0);
  while(true)
  do
    nbUnusedEq:=0;
    for iCase in [1..nbEqs]
    do
      eCase:=ListOccuringCases[iCase];
      if Length(eCase)<>2 then
        Print("Not possible to have a number of item different from 2.\n");
        Print("  Here it is ", Length(eCase), " items\n");
        Error("Please correct");
      fi;
      ListIdx:=List(eCase, x->x.idx);
      ListSign:=List(eCase, x->x.Sign);
      TheSum:=AssignVector[ListIdx[1]]+AssignVector[ListIdx[2]];
      if UsedStatus[iCase]=0 and TheSum>0 then
        nbUnusedEq:=nbUnusedEq+1;
        if TheSum=2 then
          TheVal:=ListSign[1]*VectorSign[ListIdx[1]]+ListSign[2]*VectorSign[ListIdx[2]];
          if TheVal<>0 then
            Error("We have inconsistency in the signs");
          fi;
        else
          if AssignVector[ListIdx[1]]=1 then
            RefIdx:=ListIdx[1];
            OthIdx:=ListIdx[2];
          else
            RefIdx:=ListIdx[2];
            OthIdx:=ListIdx[1];
          fi;
          VectorSign[OthIdx]:=-ListSign[1]*ListSign[2]*VectorSign[RefIdx];
          AssignVector[OthIdx]:=1;
        fi;
        UsedStatus[iCase]:=1;
      fi;
    od;
    if nbUnusedEq=0 then
      break;
    fi;
  od;
  if First(VectorSign, x->Position([1,-1], x)=fail)<>fail then
    Error("The VectorSign should have only 1 and -1");
  fi;
  return VectorSign;
end;


FuncRandomDirection:=function(n, siz)
  local eList, i;
  eList:=[0];
  for i in [1..n]
  do
    Add(eList, Random([-siz..siz]));
  od;
  return eList;
end;



__ContractingHomotopyDirectAttack:=function(FuncSignatureDet, GroupEXT, EXT, kDimension, TheCycle, ListOrbitByRank)
  local ListKFacesSet, ListKFacesElt, ListKFacesSizes, eOrb, ListGen, Fk, ListKp1FacesSet, ListKp1FacesElt, ListKp1FacesSizes, TheMatrix, eLine, pos, iElt, eSet, fSet, iFace, eSign, fElt, TheCycleVector, ListVal, ListElt, iVal, TheSol, TheReturn, iOrbit, eVector, eElt, iBound, iCol;
  ListKFacesSet:=[];
  ListKFacesElt:=[];
  ListKFacesSizes:=[];
  for eOrb in ListOrbitByRank[kDimension+2]
  do
    ListGen:=OrbitWithAction(GroupEXT, eOrb.eSet, OnSets);
    Add(ListKFacesSet, ListGen.ListCoset);
    Add(ListKFacesElt, ListGen.ListElement);
    Add(ListKFacesSizes, Length(ListGen.ListElement));
  od;
  Fk:=Length(ListKFacesSet);
  ListKp1FacesSet:=[];
  ListKp1FacesElt:=[];
  ListKp1FacesSizes:=[];
  TheMatrix:=[];
  for eOrb in ListOrbitByRank[kDimension+3]
  do
    ListGen:=OrbitWithAction(GroupEXT, eOrb.eSet, OnSets);
    for iElt in [1..Length(ListGen.ListElement)]
    do
      eLine:=ListWithIdenticalEntries(Fk, 0);
      eElt:=ListGen.ListElement[iElt];
      for iBound in [1..Length(eOrb.BoundaryImage.ListIFace)]
      do
        iFace:=eOrb.BoundaryImage.ListIFace[iBound];
        eSign:=eOrb.BoundaryImage.ListSign[iBound];
        fElt:=eOrb.BoundaryImage.ListElt[iBound]*eElt;
        eSet:=ListOrbitByRank[kDimension+2][iFace].eSet;
        fSet:=Image(eSet, fElt);
        pos:=Position(ListKFacesSet[iFace], fSet);
        eLine[pos]:=eSign*FuncSignatureDet(EXT, eSet, fElt*ListKFacesSet[iFace][pos]^(-1));
      od;
      Add(TheMatrix, eLine);
    od;
    Add(ListKp1FacesSizes, Length(ListGen.ListElement));
  od;
  TheCycleVector:=[];
  for iCol in [1..Length(TheCycle)]
  do
    eVector:=ListWithIdenticalEntries(ListKFacesSizes[iCol], 0);
    for iVal in [1..Length(TheCycle[iCol].ListVal)]
    do
      eSet:=ListOrbitByRank[kDimension+2][iCol].eSet;
      fSet:=Image(eSet, TheCycle[iCol].ListElt[iVal]);
      pos:=Position(ListKFacesSet[iCol], fSet);
      eVector[pos]:=eVector[pos]+TheCycle[iCol].ListVal[iVal]*FuncSignatureDet(EXT, eSet, TheCycle[iCol].ListElt[iVal]*ListKFacesSet[iCol][pos]^(-1));
    od;
    Append(TheCycleVector, eVector);
  od;
  TheSol:=SolutionIntMat(TheMatrix, TheCycleVector);
  TheReturn:=[];
  pos:=0;
  for iOrbit in [1..Length(ListOrbitByRank[kDimension+3])]
  do
    ListVal:=[];
    ListElt:=[];
    for iCol in [1..ListKp1FacesSizes[iOrbit]]
    do
      pos:=pos+1;
      if TheSol[pos]<>0 then
        Add(ListVal, TheSol[pos]);
        Add(ListElt, ListKp1FacesElt[iCol]);
      fi;
    od;
    Add(TheReturn, rec(ListVal:=ListVal, ListElt:=ListElt));
  od;
  return TheReturn;
end;





BoundaryOperatorsCellularDecompositionPolytope:=function(GroupEXT, EXT, kSought)
  local rnk, ListOrbitByRank, iRank, TheComputedList, FuncInsert, iFace, eFace, NewListOrbit, eOrbit, ListSetsM2, ListOccuringCoefficients, idx, eOrbitSmall, TheBoundary, eElt, iBound, pos, ListSign, TheRetOrbit, ListIFace, ListElt, TheReturnBoundary, iFaceSelect, IdxSel, eMulSign, eAddElt, ListElementM2, nbBound, iFaceM2, iFaceM1, eSign, eEltM2, ListOrbVertices, TheRec, eO, O, iOrbit, TheSpann, eSpann, eSet, TheStab, IsInKernel, TheContractingHomotopy, MyFuncSignatureDet, FuncSignatureDet, eRotSubgroup, phi, ListSignGens, eStab, GRPsym, eDet, ListMatrGens, iOrb, nbOrb, eGen, EXTwork, eSelect, eRecSel, BoundingSet, nbFace;
  rnk:=RankMat(EXT);
  Print("Computing cellular decomposition with |EXT|=", Length(EXT), " |GRP|=", Order(GroupEXT), " k=", kSought, " rnk=", rnk, "\n");
  if TestForRepetition(EXT) then
    Error("The input has some repetition");
  fi;
  BoundingSet:=[];
  eRecSel:=ColumnReduction(EXT);
  EXTwork:=List(EXT, x->x{eRecSel.Select});
  MyFuncSignatureDet:=function(eSet, eElt)
    local TheBasis, TheRed, eMat, iExt;
    TheRed:=RowReduction(EXTwork{eSet});
    TheBasis:=TheRed.EXT;
    eMat:=[];
    for iExt in TheRed.Select
    do
      Add(eMat, SolutionMat(TheBasis, EXTwork[OnPoints(eSet[iExt],eElt)]));
    od;
    return DeterminantMat(eMat);
  end;
  FuncSignatureDet:=function(iRank, iOrb, eElt)
    eSet:=ListOrbitByRank[iRank+2][iOrb].eSet;
    return MyFuncSignatureDet(eSet, eElt);
  end;
  ListOrbitByRank:=[];
  ListOrbitByRank[1]:=[rec(EXT:=[], TheStab:="irrelevant", BoundaryImage:="irrelevant", TheDel:="irrelevant")];
  O:=Orbits(GroupEXT, [1..Length(EXTwork)], OnPoints);
  ListOrbVertices:=[];
  for eO in O
  do
    TheStab:=Stabilizer(GroupEXT, eO[1], OnPoints);
    TheRec:=rec(eSet:=[eO[1]], TheSpa:=[eO[1]], TheStab:=TheStab, BoundaryImage:=rec(ListIFace:=[1], ListSign:=[1], ListElt:=[()]));
    Add(ListOrbVertices, TheRec);
  od;
  Print("We have ", Length(O), " orbits of vertices\n");
  Add(ListOrbitByRank, ListOrbVertices);
  for iRank in [1..kSought+1]
  do
    TheComputedList:=[];
    nbFace:=0;
    FuncInsert:=function(eSetSmall, iFace, eSpann1)
      local iOrbit2, eOrbit2, eEquiv, eSetSmallImg, TheOrbSmall, NewListElement, TheStab, eOrbit1;
      for iOrbit2 in [1..Length(TheComputedList)]
      do
        eOrbit2:=TheComputedList[iOrbit2];
        eEquiv:=RepresentativeAction(GroupEXT, eSpann1, eOrbit2.eSet, OnSets);
        if eEquiv<>fail then
          eSetSmallImg:=OnSets(eSetSmall, eEquiv);
          TheOrbSmall:=OrbitWithAction(eOrbit2.TheStab, eSetSmallImg, OnSets);
          NewListElement:=List(TheOrbSmall.ListElement, x->eEquiv*x);
          Add(TheComputedList[iOrbit2].ListOrbitSmall, rec(iFace:=iFace, ListElement:=NewListElement));
          return;
        fi;
      od;
      TheStab:=Stabilizer(GroupEXT, eSpann1, OnSets);
      nbFace:=nbFace+Order(GroupEXT)/Order(TheStab);
      TheOrbSmall:=OrbitWithAction(TheStab, eSetSmall, OnSets);
      eOrbit1:=rec(eSet:=eSpann1, TheStab:=TheStab,
                   ListOrbitSmall:=[rec(iFace:=iFace, ListElement:=TheOrbSmall.ListElement)]);
      Add(TheComputedList, eOrbit1);
    end;
    Print("Computing faces of dimension ", iRank);
    for iFace in [1..Length(ListOrbitByRank[iRank+1])]
    do
      eFace:=ListOrbitByRank[iRank+1][iFace];
      TheSpann:=SPAN_face_LinearProgramming(eFace.eSet, eFace.TheStab, EXTwork, GroupEXT, BoundingSet);
      for eSpann in TheSpann
      do
        FuncInsert(eFace.eSet, iFace, eSpann);
      od;
    od;
    Print("   |O|=", Length(TheComputedList), " nbFace=", nbFace, "\n");
    NewListOrbit:=[];
    for eOrbit in TheComputedList
    do
      ListSetsM2:=[];
      ListElementM2:=[];
      ListIFace:=[];
      ListElt:=[];
      ListOccuringCoefficients:=[];
      idx:=0;
      for eOrbitSmall in eOrbit.ListOrbitSmall
      do
        iFaceM1:=eOrbitSmall.iFace;
        TheBoundary:=ListOrbitByRank[iRank+1][iFaceM1].BoundaryImage;
        for eElt in eOrbitSmall.ListElement
        do
          idx:=idx+1;
          Add(ListIFace, iFaceM1);
          Add(ListElt, eElt);
          nbBound:=Length(TheBoundary.ListIFace);
          for iBound in [1..nbBound]
          do
            iFaceM2:=TheBoundary.ListIFace[iBound];
            eSign:=TheBoundary.ListSign[iBound];
            eEltM2:=TheBoundary.ListElt[iBound];
            eAddElt:=eEltM2*eElt;
            if iRank=1 then
              eSet:="bckl";
            else
              eSet:=OnSets(ListOrbitByRank[iRank][iFaceM2].eSet, eAddElt);
            fi;
            pos:=Position(ListSetsM2, eSet);
            if pos=fail then
              Add(ListSetsM2, eSet);
              Add(ListElementM2, eAddElt);
              Add(ListOccuringCoefficients, [rec(Sign:=eSign, idx:=idx)]);
            else
              if iRank<=2 then
                eMulSign:=1;
              else
                eMulSign:=MyFuncSignatureDet(ListOrbitByRank[iRank][iFaceM2].eSet, ListElementM2[pos]*eAddElt^(-1));
              fi;
              Add(ListOccuringCoefficients[pos], rec(Sign:=eMulSign*eSign, idx:=idx));
            fi;
          od;
        od;
      od;
      ListSign:=UntangleAllSigns(ListOccuringCoefficients, idx);
      TheReturnBoundary:=rec(ListIFace:=ListIFace, ListSign:=ListSign, ListElt:=ListElt);
      TheRetOrbit:=rec(eSet:=eOrbit.eSet, TheSpa:=eOrbit.eSet, TheStab:=eOrbit.TheStab, BoundaryImage:=TheReturnBoundary);
      Add(NewListOrbit, TheRetOrbit);
    od;
    #
    Add(ListOrbitByRank, NewListOrbit);
  od;
  for iRank in [0..kSought+1]
  do
    nbOrb:=Length(ListOrbitByRank[iRank+2]);
    for iOrb in [1..nbOrb]
    do
      eStab:=ListOrbitByRank[iRank+2][iOrb].TheStab;
      ListMatrGens:=GeneratorsOfGroup(eStab);
      ListSignGens:=[];
      for eGen in ListMatrGens
      do
        eDet:=MyFuncSignatureDet(ListOrbitByRank[iRank+2][iOrb].eSet, eGen);
        if eDet=-1 then
          Add(ListSignGens, (1,2));
        else
          Add(ListSignGens, ());
        fi;
      od;
      GRPsym:=Group([(1,2)]);
      eRotSubgroup:=GetKernelOfMapping(eStab, GRPsym, ListMatrGens, ListSignGens);
      ListOrbitByRank[iRank+2][iOrb].RotationSubgroup:=eRotSubgroup;
    od;
  od;
  IsInKernel:=function(TheRank, Gvector)
    local ListSetsRankM1, ListElts, ListVals, FuncInsert, iFace, TheBound, iVal, iBound, eElt, eVal, eSet, iSet, eSum, iC;
    ListSetsRankM1:=[];
    ListElts:=[];
    ListVals:=[];
    FuncInsert:=function(eSet, eElt, eVal)
      local pos;
      pos:=Position(ListSetsRankM1, eSet);
      if pos=fail then
        Add(ListSetsRankM1, eSet);
        Add(ListElts, [eElt]);
        Add(ListVals, [eVal]);
      else
        Add(ListElts[pos], eElt);
        Add(ListVals[pos], eVal);
      fi;
    end;
    for iFace in [1..Length(ListOrbitByRank[TheRank+2])]
    do
      TheBound:=ListOrbitByRank[TheRank+2][iFace].BoundaryImage;
      for iVal in [1..Length(Gvector[iFace].ListVal)]
      do
        for iBound in [1..Length(TheBound)]
        do
          eElt:=TheBound.ListElt[iBound]*Gvector[iFace].ListElt[iVal];
          eVal:=TheBound.ListSign[iBound]*Gvector[iFace].ListVal[iVal];
          if TheRank=0 then
            eSet:="bckl";
          else
            eSet:=OnSets(ListOrbitByRank[TheRank+1][TheBound.ListIFace[iBound]].eSet, eElt);
          fi;
          FuncInsert(eSet, eElt, eVal);
        od;
      od;
    od;
    for iSet in [1..Length(ListSetsRankM1)]
    do
      eSum:=0;
      for iC in [1..Length(ListElts[iSet])]
      do
        eSum:=eSum+ListVals[iC]*MyFuncSignatureDet(ListOrbitByRank[iRank][iFaceM2].eSet, ListElts[iSet][iC]*ListElts[iSet][1]^(-1));
      od;
      if eSum<>0 then
        return false;
      fi;
    od;
    return true;
  end;
  TheContractingHomotopy:=function(TheVector, TheRank)
    local test, TheV, ListCenter, ListElts, ListVals, FuncInsert;
    test:=IsInKernel(TheRank, TheVector);
    if test=false then
      Error("Sorry cannot operate if not cycle");
    fi;
    while(true)
    do
      TheV:=FuncRandomDirection(Length(EXTwork[1]), 10);
      # now we really need the centers
      ListCenter:=[];
      ListElts:=[];
      ListVals:=[];
      FuncInsert:=function(eCent, eElt, eVal)
        local pos;
        pos:=Position(ListCenter, eSet);
        if pos=fail then
          Add(ListCenter, eSet);
          Add(ListElts, [eElt]);
          Add(ListVals, [eVal]);
        else
          Add(ListElts[pos], eElt);
          Add(ListVals[pos], eVal);
        fi;
      end;
    od;
  end;
  return rec(ListOrbitByRank:=ListOrbitByRank, IsInKernel:=IsInKernel,
             TheContractingHomotopy:=TheContractingHomotopy);
end;








CreateSAU:=function(GroupFac, FAC, EXT)
  local HK, SEQE, iRank, LS, eOrb, ListAbove, ListAB, iFac, jFac, ListFound, ListUnder;
  HK:=CreateK_skeletton(GroupFac, FAC, EXT);
  SEQE:=[];
  for iRank in [1..Length(HK)]
  do
    LS:=[];
    for eOrb in HK[iRank].ListRepresentent
    do
      Append(LS, Orbit(GroupFac, eOrb, OnSets));
    od;
    Add(SEQE, Set(LS));
  od;
  ListAbove:=[];
  for iRank in [1..Length(HK)-1]
  do
    ListAB:=[];
    for iFac in [1..Length(SEQE[iRank])]
    do
      ListFound:=[];
      for jFac in [1..Length(SEQE[iRank+1])]
      do
        if IsSubset(SEQE[iRank+1][jFac], SEQE[iRank][iFac])=true then
          Add(ListFound, jFac);
        fi;
      od;
      Add(ListAB, ListFound);
    od;
    Add(ListAbove, ListAB);
  od;
  ListUnder:=[];
  for iRank in [1..Length(HK)-1]
  do
    ListAB:=[];
    for iFac in [1..Length(SEQE[iRank+1])]
    do
      ListFound:=[];
      for jFac in [1..Length(SEQE[iRank])]
      do
        if IsSubset(SEQE[iRank+1][iFac], SEQE[iRank][jFac])=true then
          Add(ListFound, jFac);
        fi;
      od;
      Add(ListAB, ListFound);
    od;
    Add(ListUnder, ListAB);
  od;
  return rec(SEQE:=SEQE, ListAbove:=ListAbove, ListUnder:=ListUnder);
end;



CreateHasseList:=function(GroupFac, FAC, EXT)
  local HK, dimension, ListFace, iDim, FixDim, ORB, eElt, pos, HasseList, iElt, jElt;
  HK:=CreateK_skeletton(GroupFac, FAC, EXT);
  dimension:=Length(HK);
  ListFace:=[];
  for iDim in [1..dimension]
  do
    FixDim:=[];
    for eElt in HK[iDim].ListRepresentent
    do
      ORB:=Orbit(GroupFac, eElt, OnSets);
      FixDim:=Union(FixDim, ORB);
    od;
    ListFace[iDim]:=FixDim;
  od;
  #
  #
  pos:=0;
  HasseList:=[];
  for iElt in [1..Length(ListFace[1])]
  do
    Add(HasseList, [0, iElt]);
  od;
  for iDim in [1..dimension-1]
  do
    for iElt in [1..Length(ListFace[iDim])]
    do
      for jElt in [1..Length(ListFace[iDim+1])]
      do
        if IsSubset(ListFace[iDim+1][jElt], ListFace[iDim][iElt])=true then
          Add(HasseList, [pos+iElt, pos+Length(ListFace[iDim])+jElt]);
        fi;
      od;
    od;
    pos:=pos+Length(ListFace[iDim]);
  od;
  for iElt in [1..Length(ListFace[dimension])]
  do
    Add(HasseList, [pos+iElt, pos+Length(ListFace[dimension])+1]);
  od;
  return HasseList;
end;

#
# Test if a set determine a face of the polytope
# By doing linear programming
TestDefinitionFace:=function(ListVect, eSet)
  local ListVectRed, NSP, dimNSP, nbVect, ListIneq, eIdx, eVectRed, eIneq, iNSP, eNSP, eScal, fIneq, ToBeMinimized, TheLP, TheSolutionRed, TheSolution, eEnt;
  if Length(eSet)=Length(ListVect) then
    return true;
  fi;
  ListVectRed:=ColumnReduction(ListVect).EXT;
  NSP:=NullspaceMat(TransposedMat(ListVectRed{eSet}));
  dimNSP:=Length(NSP);
  nbVect:=Length(ListVectRed);
  ListIneq:=[];
  for eIdx in Difference([1..nbVect],eSet)
  do
    eVectRed:=ListVectRed[eIdx];
    eIneq:=ListWithIdenticalEntries(2+dimNSP,0);
    eIneq[1]:=-1;
    for iNSP in [1..dimNSP]
    do
      eNSP:=NSP[iNSP];
      eScal:=eNSP*eVectRed;
      eIneq[1+iNSP]:=eScal;
    od;
    Add(ListIneq, eIneq);
  od;
  for iNSP in [1..dimNSP]
  do
    eIneq:=ListWithIdenticalEntries(2+dimNSP,0);
    eIneq[1+iNSP]:=1;
    eIneq[2+dimNSP]:=1;
    Add(ListIneq, eIneq);
    fIneq:=ListWithIdenticalEntries(2+dimNSP,0);
    fIneq[1+iNSP]:=-1;
    fIneq[2+dimNSP]:=1;
    Add(ListIneq, fIneq);
  od;
  ToBeMinimized:=ListWithIdenticalEntries(2+dimNSP,0);
  ToBeMinimized[2+dimNSP]:=1;
  TheLP:=LinearProgramming(ListIneq, ToBeMinimized);
  if IsBound(TheLP.primal_solution) then
    TheSolutionRed:=ListWithIdenticalEntries(dimNSP, 0);
    for eEnt in TheLP.primal_solution
    do
      TheSolutionRed[eEnt[1]]:=eEnt[2];
    od;
    TheSolution:=TheSolutionRed*NSP;
    for eIdx in eSet
    do
      if TheSolution*ListVectRed[eIdx]<>0 then
        Error("It should be zero");
      fi;
    od;
    for eIdx in Difference([1..nbVect],eSet)
    do
      if TheSolution*ListVectRed[eIdx]<=0 then
        Error("It should be strictly positive");
      fi;
    od;
    return true;
  else
    return false;
  fi;
end;



#
# Given a set, we return the smallest face containing it
FaceSaturation:=function(ListVect, eSet)
  local ListVectRed, NSP, nbVect, dimNSP, ListIneq, eIdx, eVectRed, eIneq, TheSpace, retSet, IsCorr, eVectSpace, eLinear;
  if Length(ListVect)=Length(eSet) then
    return eSet;
  fi;
  ListVectRed:=ColumnReduction(ListVect).EXT;
  NSP:=NullspaceMat(TransposedMat(ListVectRed{eSet}));
  if Length(NSP)=0 then
    return [1..Length(ListVect)];
  fi;
  nbVect:=Length(ListVect);
  dimNSP:=Length(NSP);
  ListIneq:=[];
  for eIdx in Difference([1..nbVect], eSet)
  do
    eVectRed:=ListVectRed[eIdx];
    eIneq:=List(NSP, x->x*eVectRed);
    Add(ListIneq, eIneq);
  od;
  TheSpace:=LinearDeterminedByInequalities(ListIneq);
  retSet:=[];
  for eIdx in [1..nbVect]
  do
    eVectRed:=ListVectRed[eIdx];
    IsCorr:=true;
    for eVectSpace in TheSpace
    do
      eLinear:=eVectSpace*NSP;
      if eLinear*eVectRed<>0 then
        IsCorr:=false;
      fi;
    od;
    if IsCorr then
      Add(retSet, eIdx);
    fi;
  od;
  return retSet;
end;


#
#
# this procedure will test if two given Kfaces are adjacent in the K-skeletton
# graph using the Kminus and Kplus graph. These faces are described as list of
# facets giving their description.
# for the extreme case K=1 put [] for Kminus and for K=dimension-1 put Kplus=[]
TestAdjKskeletton:=function(eFace1, eFace2, K, dimension, Kminus, Kplus)
  local test1, R, iFace;
  test1:=0;
  if K=1 then
    test1:=1;
  else
    if Intersection(eFace1, eFace2) in Kminus then
      test1:=1;
    fi;
  fi;
  if test1=1 then
    if K=dimension-1 then
      return true;
    else
      R:=Union(eFace1, eFace2);
      iFace:=1;
      while(iFace<=Length(Kplus))
      do
        if IsSubset(Kplus[iFace],R) then
          return true;
        fi;
        iFace:=iFace+1;
      od;
      return false;
    fi;
  else
    return false;
  fi;
end;


TestAdjSkeletonUseSymmetry:=function(eFace1, eFace2, K, dimension, EXT, FAC, GRPext, ListRepresententKminus, ListRepresententKplus)
  local test1, Runion, iFace, eRepr, TheInt, TheSumEXT, TheSumFAC, SetInc;
  test1:=0;
  if K=1 then
    test1:=1;
  else
    TheInt:=Intersection(eFace1, eFace2);
    test1:=0;
    for eRepr in ListRepresententKminus
    do
      if test1=0 then
        if RepresentativeAction(GRPext, TheInt, eRepr, OnSets)<>fail then
          test1:=1;
        fi;
      fi;
    od;
  fi;
  if test1=1 then
    if K=dimension-1 then
      return true;
    else
      Runion:=Union(eFace1, eFace2);
      TheSumEXT:=Sum(List(Runion, x->EXT[x]));
      TheSumFAC:=Sum(Filtered(FAC, x->x*TheSumEXT=0));
      SetInc:=Filtered([1..Length(EXT)], x->EXT[x]*TheSumFAC=0);
      for eRepr in ListRepresententKplus
      do
        if RepresentativeAction(GRPext, SetInc, eRepr, OnSets)<>fail then
          return true;
        fi;
      od;
      return false;
    fi;
  else
    return false;
  fi;
end;

# GroupFac is a group of permutation acting on the list of all facets
# Kminus and Kplus are list of faces of dimension K-1 and K+1 written as
# intersection of facets
# LISTORB is the list of all orbits of faces of dimension k.
# each such orbit is presented as list
CreateK_graph:=function(GroupFac, K, dimension, Kminus, LISTORB, Kplus)
  local FuncAdj;
  FuncAdj:=function(S1,S2)
    return TestAdjKskeletton(S1, S2, K, dimension, Kminus, Kplus);
  end;
  return EquivariantSkeleton(GroupFac, LISTORB, FuncAdj, OnSets);
end;

#
# F-vector and H-vector theory
Fvector:=function(HK)
  local F, iCol;
  F:=[];
  for iCol in [1..Length(HK)]
  do
    F[iCol]:=Length(Union(HK[iCol].Orbits));
  od;
  return F;
end;
