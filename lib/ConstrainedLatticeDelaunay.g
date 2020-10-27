#
# We have a polytope polytope1 defined by the inequality set FAC1
# and polytope2 defined by inequality set FAC2
#
# The difference polytope1 - polytope2 is not necessarily a polytope
# but this function will express as a finite union of polytopes.
# All polytopes considered are full dimensional.
DifferencePolytope:=function(FAC1, FAC2)
  local ListFAC, nbFAC2, iFac2, TheFAC, i;
  ListFAC:=[];
  nbFAC2:=Length(FAC2);
  for iFac2 in [1..nbFAC2]
  do
    TheFAC:=[];
    for i in [1..iFac2-1]
    do
      Add(TheFAC, FAC2[i]);
    od;
    Add(TheFAC, -FAC2[iFac2]);
    Append(TheFAC, FAC1);
    if IsSpaceFullDimensional(TheFAC) then
      Add(ListFAC, TheFAC);
    fi;
  od;
  return ListFAC;
end;



TestPolytopeCovering:=function(ListEXT, EXT)
  local OverlappingMatrix, TotalListPolytope, EliminateEntry, FuncInsertPolytope, OneEXT, OneFAC, PairFacExt, PolyContainment, GetContainedPair, PairFound, UpdateOverlappingMatrix, GetCollisionPair, BreakdownPolytope, TotVol, ListVol;
  OverlappingMatrix:=[];
  TotalListPolytope:=[];
  EliminateEntry:=function(idx)
    local len, eDiff;
    len:=Length(TotalListPolytope);
    eDiff:=Difference([1..len], [idx]);
    TotalListPolytope:=TotalListPolytope{eDiff};
    OverlappingMatrix:=List(OverlappingMatrix{eDiff}, x->x{eDiff});
  end;
  FuncInsertPolytope:=function(ePoly)
    local len, i;
    len:=Length(TotalListPolytope);
    Add(TotalListPolytope, ePoly);
    for i in [1..len]
    do
      Add(OverlappingMatrix[i], "unset");
    od;
    Add(OverlappingMatrix, ListWithIdenticalEntries(len+1, "unset"));
  end;
  #
  # 1: Direct insertion of polytopes
  #
  for OneEXT in ListEXT
  do
    OneFAC:=DualDescription(OneEXT);
    PairFacExt:=rec(FAC:=OneFAC, EXT:=OneEXT);
    FuncInsertPolytope(PairFacExt);
  od;
  #
  # 2: Elimination of contained polytopes
  # 
  PolyContainment:=function(PairFacExt1, PairFacExt2)
    local eEXT;
    for eEXT in PairFacExt2.EXT
    do
      if First(PairFacExt1.FAC, x->x*eEXT<0)<>fail then
        return false;
      fi;
    od;
    return true;
  end;
  GetContainedPair:=function()
    local nbPoly, iPoly, jPoly;
    nbPoly:=Length(OverlappingMatrix);
    for iPoly in [1..nbPoly]
    do
      for jPoly in [1..nbPoly]
      do
        if iPoly<>jPoly then
          if PolyContainment(OverlappingMatrix[iPoly], OverlappingMatrix[jPoly]) then
	    return [iPoly, jPoly];
          fi;
        fi;
      od;
    od;
    return fail;
  end;
  while(true)
  do
    PairFound:=GetContainedPair();
    if PairFound=fail then
      break;
    fi;
    EliminateEntry(PairFound[2]);
  od;
  #
  # 3: Computing the OverlappingMatrix
  # 
  UpdateOverlappingMatrix:=function()
    local nbPoly, iPoly, jPoly, FACmerge, test;
    nbPoly:=Length(TotalListPolytope);
    for iPoly in [1..nbPoly]
    do
      for jPoly in [iPoly+1..nbPoly]
      do
        if OverlappingMatrix[iPoly][jPoly]="unset" then
          FACmerge:=Concatenation(TotalListPolytope[iPoly].FAC, TotalListPolytope[jPoly].FAC);
          test:=IsSpaceFullDimensional(FACmerge);
          OverlappingMatrix[iPoly][jPoly]:=test;
          OverlappingMatrix[jPoly][iPoly]:=test;
        fi;
      od;
    od;
  end;
  UpdateOverlappingMatrix();
  #
  # 4: Now iterating over all the entries and break overlapping polytopes
  #
  GetCollisionPair:=function()
    local nbPoly, iPoly, jPoly;
    nbPoly:=Length(OverlappingMatrix);
    for iPoly in [1..nbPoly]
    do
      for jPoly in [iPoly+1..nbPoly]
      do
        if OverlappingMatrix[iPoly][jPoly] then
	  return [iPoly,jPoly];
	fi;
      od;
    od;
    return fail;
  end;
  BreakdownPolytope:=function(iPoly, jPoly)
    local ListDiffFAC, PrevLen, nbDiff, eDiffFAC, eDiffEXT, PairFacExt, iDiff, jDiff, kPoly;
    ListDiffFAC:=DifferencePolytope(TotalListPolytope[iPoly].FAC, TotalListPolytope[jPoly].FAC);
    PrevLen:=Length(TotalListPolytope);
    nbDiff:=Length(ListDiffFAC);
    for eDiffFAC in ListDiffFAC
    do
      eDiffEXT:=DualDescription(eDiffFAC);
      PairFacExt:=rec(FAC:=eDiffFAC, EXT:=eDiffEXT);
      FuncInsertPolytope(PairFacExt);
    od;
    for iDiff in [1..nbDiff]
    do
      for jDiff in [1..nbDiff]
      do
        if iDiff<>jDiff then
          OverlappingMatrix[PrevLen+iDiff][PrevLen+iDiff]:=false;
        fi;
      od;
    od;
    for iDiff in [1..nbDiff]
    do
      OverlappingMatrix[jPoly][PrevLen+iDiff]:=false;
      OverlappingMatrix[PrevLen+iDiff][jPoly]:=false;
    od;
    for kPoly in [1..PrevLen]
    do
      if kPoly<>iPoly and jPoly<>jPoly then
        if OverlappingMatrix[kPoly][iPoly]=false then
          for iDiff in [1..nbDiff]
          do
            OverlappingMatrix[kPoly][PrevLen+iDiff]:=false;
            OverlappingMatrix[PrevLen+iDiff][kPoly]:=false;
          od;
	fi;
      fi;
    od;
    EliminateEntry(iPoly);
    UpdateOverlappingMatrix();
  end;
  while(true)
  do
    PairFound:=GetCollisionPair();
    if PairFound=fail then
      break;
    fi;
    BreakdownPolytope(PairFound[1], PairFound[2]);
  od;
  #
  # 5: Now deciding with volume
  #
  TotVol:=VolumeComputationPolytope(EXT);
  ListVol:=List(TotalListPolytope, x->VolumeComputationPolytope(x.EXT));
  if Sum(ListVol)=TotVol then
    return true;
  fi;
  return false;
end;



# From the outset, we assume that the translationclassespolytope intersect
# the polytope in a nice way. Otherwise, no need for this complex procedure.
#
IsVisibleFromPolytope:=function(TranslationClassesPolytope, PairFacExt, eEXT)
  local n, IdMat, EXTcont, FACcont, FACcone, TheMainFAC, ListValue, eMinValue, NSP, eFirst, eVert, PartialBasis, eNSP, eNSPred, ProjectVert, FACprojFull, EXTprojFull, EXTproj, ListIntPoint, ListRelPolytopes, eIntPoint, eTransClassPolytope, eDiff, eDiffRed, eBigMat, FACimg, FACmerge, EXTmerge, EXTmergeProj, testCov;
  if First(PairFacExt.FAC, x->x*eEXT<0)=fail then
    return true;
  fi;
  n:=Length(eEXT) - 1;
  IdMat:=IdentityMat(n);
  #
  # Construction of the conv(P, v)
  # and related projection
  #
  EXTcont:=Concatenation(PairFacExt.EXT, [eEXT]);
  FACcont:=DualDescription(EXTcont);
  FACcone:=Filtered(FACcont, x->x*eEXT=0);
  #
  # Construction of additional plane
  # plus the basis
  #
  TheMainFAC:=-Sum(FACcone);
  ListValue:=List(EXTcont, x->x*TheMainFAC);
  eMinValue:=Minimum(ListValue);
  TheMainFAC[1]:=TheMainFAC[1] + eMinValue;
  NSP:=NullspaceMat(TransposedMat([TheMainFAC]));
  eFirst:=First(NSP, x->x[1]<>0);
  eVert:=eFirst/eFirst[1];
  PartialBasis:=[];
  for eNSP in NSP
  do
    if eNSP<>eFirst then
      eNSPred:=eNSP - eNSP[1]*eVert;
      Add(PartialBasis, eNSPred);
    fi;
  od;
  ProjectVert:=function(eVert)
    local eDiff, TheFull, eSol;
    eDiff:=eVert - eEXT;
    TheFull:=Concatenation([eVert], PartialBasis, eDiff);
    eSol:=SolutionMat(TheFull, eEXT);
    return eSol{[1..n]};
  end;
  FACprojFull:=Concatenation(FACcone, [TheMainFAC]);
  EXTprojFull:=DualDescription(FACprojFull);
  EXTproj:=List(EXTprojFull, ProjectVert);
  #
  #
  
  ListIntPoint:=GetIntegralPointsIteration_Kernel(FACcont, EXTcont);
  ListRelPolytopes:=[];
  for eIntPoint in ListIntPoint
  do
    for eTransClassPolytope in TranslationClassesPolytope
    do
      for eEXT in eTransClassPolytope
      do
        eDiff:=eIntPoint - eEXT;
        eDiffRed:=eDiff{[2..n+1]};
        eBigMat:=FuncCreateBigMatrix(eDiffRed, IdMat);
        FACimg:=eTransClassPolytope.FAC*CongrMap(eBigMat);
        FACmerge:=Concatenation(FACimg, FACcont);
        if IsSpaceFullDimensional(FACmerge) then
          EXTmerge:=DualDescription(FACmerge);
          EXTmergeProj:=List(EXTmerge, ProjectVert);
          Add(ListRelPolytopes, EXTmergeProj);
        fi;
      od;
    od;
  od;
  testCov:=TestPolytopeCovering(ListRelPolytopes, EXTproj);
  if testCov then
    return false;
  else
    return true;
  fi;
end;



IsAdmissibleConstrainedDelaunay:=function(TranslationClassesPolytope, TheGramMat, TheEXT)
  local n, TheFAC, PairFacExt, CP, eCent, TheDist, reply, replyRed, ListDisc, eVect, eVectExt, eDiff, eDist, eDisc, ePerm, replyImg, eEXT;
  n:=Length(TheGramMat);
  TheFAC:=DualDescription(TheEXT);
  PairFacExt:=rec(FAC:=TheFAC, EXT:=TheEXT);
  CP:=CenterRadiusDelaunayPolytopeGeneral(TheGramMat, TheEXT);
  eCent:=CP.Center{[2..n+1]};
  TheDist:=CP.SquareRadius;
  reply:=ClosestAtDistanceVallentinProgram(TheGramMat, eCent, TheDist);
  replyRed:=[];
  ListDisc:=[];
  for eVect in reply
  do
    eVectExt:=Concatenation([1], eVect);
    if Position(TheEXT, eVect)=fail then
      Add(replyRed, eVectExt);
      eDiff:=eVect - eCent;
      eDist:=eDiff*TheGramMat*eDiff;
      eDisc:=1/eDist;
      Add(ListDisc, eDisc);
    fi;
  od;
  ePerm:=SortingPerm(ListDisc);
  replyImg:=Permuted(replyRed, ePerm);
  for eEXT in replyImg
  do
    if IsVisibleFromPolytope(TranslationClassesPolytope, PairFacExt, eEXT) then
      return false;
    fi;
  od;
  return true;
end;


FindAdjacentConstrainedDelaunay:=function(TranslationClassesPolytope, TheGramMat, RecFacet)
  Error("Missing code");
end;