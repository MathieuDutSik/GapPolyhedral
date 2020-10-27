# We are dealing with triangulation that are periodic
# along Z^n but not necessarily centrally symmetric
# Also not necessarily Delaunay triangulation
# And not necessarily regular (induced by an height function)
TRIG_FindTriangles:=function(ListTrig, EXTset)
  local n, nbTrig, ListReturn, iTrig, eTrig, eVert, eEXT, eDiffV, eDiffRed, eTrigImg, eRecReturn, eBigMat, TotalEXTset;
  n:=Length(ListTrig[1][1])-1;
  nbTrig:=Length(ListTrig);
  ListReturn:=[];
  TotalEXTset:=Set(EXTset);
  for iTrig in [1..nbTrig]
  do
    eTrig:=ListTrig[iTrig];
    eEXT:=EXTset[1];
    for eVert in eTrig
    do
      eDiffV:=eEXT - eVert;
      eTrigImg:=List(eTrig, x->x + eDiffV);
      if IsSubset(Set(eTrigImg), TotalEXTset) then
        eDiffRed:=eDiffV{[2..n+1]};
        eBigMat:=FuncCreateBigMatrix(eDiffRed, IdentityMat(n));
        eRecReturn:=rec(iTrig:=iTrig, eDiffRed:=eDiffRed, eBigMat:=eBigMat, eTrig:=eTrigImg);
        Add(ListReturn, eRecReturn);
      fi;
    od;
  od;
  return ListReturn;
end;


# Check if a family of triangles in ListTrig is contained
# after mapping by eBigMat into ListTrig2
TRIG_IsCorrectSymmetry:=function(ListTrig1, ListTrig2, eBigMat)
  local eTrig, fTrig, ListCont;
  for eTrig in ListTrig1
  do
    fTrig:=eTrig*eBigMat;
    ListCont:=TRIG_FindTriangles(ListTrig2, fTrig);
    if Length(ListCont)=0 then
      return false;
    fi;
  od;
  return true;
end;


TRIG_IsTranslationallyEquivalent:=function(ListTrig1, ListTrig2)
  local eTrig, ListCont;
  for eTrig in ListTrig1
  do
    ListCont:=TRIG_FindTriangles(ListTrig2, eTrig);
    if Length(ListCont)<>1 then
      return false;
    fi;
  od;
  return true;
end;



# eFace in contained into a triangle
# we returned a canonical representative under translation.
# Idea is to consider all points to be at 0
# and select the minimum of all possible representatives
TRIG_CanonicalizeFace:=function(eFace)
  local n, ListCandMin, i, eDiff, eFaceB;
  n:=Length(eFace[1])-1;
  ListCandMin:=[];
  for i in [1..Length(eFace)]
  do
    eDiff:=Concatenation([0], -eFace[i]{[2..n+1]});
    eFaceB:=List(eFace, x->x + eDiff);
    Add(ListCandMin, Set(eFaceB));
  od;
  return Set(ListCandMin)[1];
end;



# Return an invariant of a family of triangles.
# The invariant is under arithmetic equivalence.
TRIG_Invariant:=function(ListTrig)
  local ListVolume, eTrig, n, ListColl, k, ListFaces, ListMult, FuncInsert, ListFaceTrig, eFace, eFaceCan;
  ListVolume:=List(ListTrig, x->AbsInt(DeterminantMat(x)));
  eTrig:=ListTrig[1];
  n:=Length(eTrig[1])-1;
  ListColl:=[];
  for k in [2..n-2]
  do
    ListFaces:=[];
    ListMult:=[];
    FuncInsert:=function(eFace)
      local pos;
      pos:=Position(ListFaces, eFace);
      if pos=fail then
        Add(ListFaces, eFace);
        Add(ListMult, 1);
      else
        ListMult[pos]:=ListMult[pos]+1;
      fi;
    end;
    for eTrig in ListTrig
    do
      ListFaceTrig:=Combinations(eTrig, k);
      for eFace in ListFaceTrig
      do
        eFaceCan:=TRIG_CanonicalizeFace(eFace);
        FuncInsert(eFaceCan);
      od;
    od;
    Add(ListColl, Collected(ListMult));
  od;
  return rec(InvVol:=Collected(ListVolume),
             ListColl:=ListColl);
end;

# Test if ListTrig is translationally equivalent to ListTrigCan
# with ListTrigCan being in canonicalized form.
TRIG_TestEqualityCanonicalize:=function(ListTrig, ListTrigCan)
  local eTrig, n, ListCanTrig, ListCandMin, i, eDiff, eTrigB, eTrigMin;
  eTrig:=ListTrig[1];
  n:=Length(eTrig[1])-1;
  ListCanTrig:=[];
  for eTrig in ListTrig
  do
    ListCandMin:=[];
    for i in [1..n+1]
    do
      eDiff:=Concatenation([0], -eTrig[i]{[2..n+1]});
      eTrigB:=List(eTrig, x->x + eDiff);
      Add(ListCandMin, Set(eTrigB));
    od;
    eTrigMin:=Set(ListCandMin)[1];
    if Position(ListTrigCan, eTrigMin)=fail then
      return false;
    fi;
  od;
  return true;
end;




# The triangles are determined up to translation
# Sometimes, it is better to canonicalize their
# expression for isomorphism tests.
TRIG_CanonicalizeExpression:=function(ListTrig)
  local eTrig, n, ListCanTrig, ListCandMin, i, eDiff, eTrigB, eTrigMin;
  eTrig:=ListTrig[1];
  n:=Length(eTrig[1])-1;
  ListCanTrig:=[];
  for eTrig in ListTrig
  do
    ListCandMin:=[];
    for i in [1..n+1]
    do
      eDiff:=Concatenation([0], -eTrig[i]{[2..n+1]});
      eTrigB:=List(eTrig, x->x + eDiff);
      Add(ListCandMin, Set(eTrigB));
    od;
    eTrigMin:=Set(ListCandMin)[1];
    Add(ListCanTrig, eTrigMin);
  od;
  return Set(ListCanTrig);
end;


# Generate the family for the paper and check if it satisfies
# what we say in the theorem it is.
TRIG_PartialInfiniteSeries_Dim5:=function(n)
  local ptO, ptX, ptA, ptB, ptC, ptD, eSimp1, ptXprime, eSimp2, eSol, det1, det2;
  ptO:=[0,0,0,0,0];
  ptX:=[-1,0,0,0,0];
  ptA:=[0,1,0,0,0];
  ptB:=[0,0,1,0,0];
  ptC:=[0,0,0,1,0];
  ptD:=[0,0,0,0,1];
  eSimp1:=List([ptO, ptA, ptB, ptC, ptD, ptX], x->Concatenation([1], x));
  ptXprime:=[1,1,1,1,n+1];
  eSimp2:=List([ptO, ptA, ptB, ptC, ptD, ptXprime], x->Concatenation([1], x));
  #
  eSol:=SolutionMat(eSimp1, Concatenation([1],ptXprime));
  det1:=DeterminantMat(eSimp1);
  det2:=DeterminantMat(eSimp2);
  Print("det1=", det1, " det2=", det2, " eSol=", eSol, "\n");
  return [eSimp1, eSimp2];
end;









# Get the group of arithmetic transformation of GLn(Z)
# that preserves the triangulation.
TRIG_GetSymmetryGroupTriangulation:=function(ListTrig)
  local ListTrigCan, n, eV, ListGen, TheGroup, FuncInsertGenerator, eTrig, eTrigInv, nbTrig, iTrig, fTrig, eSym, eBigMat, eMat, ImgListTrig, ListTrans, eExpl;
  ListTrigCan:=TRIG_CanonicalizeExpression(ListTrig);
  n:=Length(ListTrigCan[1])-1;
  ListGen:=[];
  TheGroup:=Group([IdentityMat(n)]);
  FuncInsertGenerator:=function(eMat)
    if eMat in TheGroup then
      return;
    fi;
    Add(ListGen, eMat);
    TheGroup:=Group(ListGen);
  end;
  eTrig:=ListTrigCan[1];
  eTrigInv:=Inverse(eTrig);
  nbTrig:=Length(ListTrigCan);
  ListTrans:=[];
  for iTrig in [1..nbTrig]
  do
    fTrig:=ListTrigCan[iTrig];
    for eSym in SymmetricGroup(n+1)
    do
      eBigMat:=eTrigInv*Permuted(fTrig, eSym);
      ImgListTrig:=List(ListTrigCan, x->x*eBigMat);
      if TRIG_TestEqualityCanonicalize(ImgListTrig, ListTrigCan) then
        eExpl:=FuncExplodeBigMatrix(eBigMat);
        eMat:=eExpl.MatrixTransformation;
	Add(ListTrans, VectorMod1(eExpl.eTrans));
        FuncInsertGenerator(eMat);
      fi;
    od;
  od;
  return rec(eGRP:=TheGroup, ord:=Order(TheGroup), ListTrans:=Set(ListTrans));
end;




# Test if two triangulations are equivalent by an arithmetic
# equivalence.
TRIG_IsEquivalentTriangulation:=function(ListTrig1, ListTrig2)
  local n, eTrig, eTrigInv, nbTrig, iTrig, fTrig, eSym, eBigMat;
  if Length(ListTrig1)<>Length(ListTrig2) then
    return false;
  fi;
  n:=Length(ListTrig1[1])-1;
  eTrig:=ListTrig1[1];
  eTrigInv:=Inverse(eTrig);
  nbTrig:=Length(ListTrig1);
  for iTrig in [1..nbTrig]
  do
    fTrig:=ListTrig2[iTrig];
    for eSym in SymmetricGroup(n+1)
    do
      eBigMat:=eTrigInv*Permuted(fTrig, eSym);
      if TRIG_IsCorrectSymmetry(ListTrig1, ListTrig2, eBigMat) then
        return eBigMat;
      fi;
    od;
  od;
  return false;
end;



TRIG_IsEquivalentTriangulationCanonic:=function(ListTrig1, ListTrigCan2)
  local n, eTrig, eTrigInv, nbTrig, iTrig, fTrig, eSym, eBigMat, ImgListTrig1, ImgListTrigCan1;
  if Length(ListTrig1)<>Length(ListTrigCan2) then
    return false;
  fi;
  n:=Length(ListTrig1[1])-1;
  eTrig:=ListTrig1[1];
  eTrigInv:=Inverse(eTrig);
  nbTrig:=Length(ListTrig1);
  for iTrig in [1..nbTrig]
  do
    fTrig:=ListTrigCan2[iTrig];
    for eSym in SymmetricGroup(n+1)
    do
      eBigMat:=eTrigInv*Permuted(fTrig, eSym);
      ImgListTrig1:=List(ListTrig1, x->x*eBigMat);
#      ImgListTrigCan1:=TRIG_CanonicalizeExpression(ImgListTrig1);
#      if ImgListTrigCan1 = ListTrigCan2 then
      if TRIG_TestEqualityCanonicalize(ImgListTrig1, ListTrigCan2) then
        return eBigMat;
      fi;
    od;
  od;
  return false;
end;





# Test if the transformation x ---> -x
# preserves the triangulation itself.
TRIG_CheckCentralSymmetry:=function(ListTrig)
  local n, eBigMat, i, eTrig, fTrig, ListCont;
  n:=Length(ListTrig[1])-1;
  eBigMat:=IdentityMat(n+1);
  for i in [1..n]
  do
    eBigMat[i+1][i+1]:=-1;
  od;
  for eTrig in ListTrig
  do
    fTrig:=eTrig*eBigMat;
    ListCont:=TRIG_FindTriangles(ListTrig, fTrig);
    if Length(ListCont)=0 then
      return false;
    fi;
  od;
  return true;
end;


# Compited the value of the GARBER function.
GARBER_ComputeFunction:=function(eVect, ListVal)
  local eVal, n, i;
  eVal:=1;
  n:=Length(eVect);
  for i in [1..n]
  do
    eVal:=eVal*ListVal[i]^(eVect[i]);
  od;
  return eVal;
end;


# Returns the first n prime numbers.
TRIG_GetPrimeSequence:=function(n)
  local eSeq, eVal;
  eSeq:=[];
  eVal:=1;
  while(true)
  do
    if IsPrime(eVal) then
      Add(eSeq, eVal);
    fi;
    if Length(eSeq)=n then
      return eSeq;
    fi;
    eVal:=eVal+1;
  od;
end;


# Computes the tiling from the Garber exponential idea.
TRIG_GetGarberCubeTiling:=function(d)
  local ListVal, EXT, eEXT, eVal, nEXT, ListTrig, TheSet, TheDim, eFAC, eSet, eTrig, FAC, eVol, ListVol, SumVol;
  ListVal:=TRIG_GetPrimeSequence(d);
  EXT:=[];
  TheSet:=BuildSet(d,[0,1]);
  for eEXT in TheSet
  do
    eVal:=GARBER_ComputeFunction(eEXT, ListVal);
    nEXT:=Concatenation([1], eEXT, [eVal]);
    Add(EXT, nEXT);
  od;
  TheDim:=d+2;
  FAC:=DualDescription(EXT);
  ListTrig:=[];
  ListVol:=[];
  for eFAC in FAC
  do
    if eFAC[TheDim]>0 then
      eSet:=Filtered([1..Length(TheSet)], x->EXT[x]*eFAC=0);
      eTrig:=List(TheSet{eSet}, x->Concatenation([1], x));
      eVol:=VolumeComputationPolytope(eTrig);
      Add(ListTrig, eTrig);
      Add(ListVol, eVol);
    fi;
  od;
  SumVol:=Sum(ListVol);
  return rec(FAC:=FAC,
             ListVol:=ListVol,
             SumVol:=SumVol,
             ListTrig:=ListTrig);
end;





# From the triangulation find a facet that is not adjacent
# to another simplex.
TRIG_FindUnmatchedFacet:=function(ListTrig)
  local eTrig, FAC, eFAC, eSet, EXTfac, ListRecFind;
  for eTrig in ListTrig
  do
    FAC:=DualDescription(eTrig);
    for eFAC in FAC
    do
      eSet:=Filtered([1..Length(eTrig)], x->eTrig[x]*eFAC=0);
      EXTfac:=eTrig{eSet};
      ListRecFind:=TRIG_FindTriangles(ListTrig, EXTfac);
      if Length(ListRecFind)=1 then
        return rec(EXT:=eTrig, eInc:=eSet, eIneq:=-eFAC);
      fi;
    od;
  od;
  return fail;
end;


# Computes the Adjacency informatioin of a triangulation.
# In input is just the list of simplices.
# In output we also have a list of record
# rec(iDelaunay:=...  , eBigMat:=.... , eInc:=...)
# with
# ---iDelaunay the index of the adjacent simplex.
# ---eBigMat the matrix that maps the representative to the one
#    immediately adjacent.
# ---eInc the set of incident point in the facet that describe it.
# This data format is named so as to match functionality for
# Delaunay tesselations.
TRIG_GetAdjacencyInformationOfTriangulation:=function(ListTrig)
  local n, nbTrig, ListSimplices_FormalDelaunay, iTrig, Adjacencies, EXT, iVert, eDiff, EXTdiff, eRecFind, eBigMat, eAdjInfo, ListRecFind, eRecSimplex, eInt, eTrigImg;
  n:=Length(ListTrig[1])-1;
  nbTrig:=Length(ListTrig);
  ListSimplices_FormalDelaunay:=[];
  for iTrig in [1..nbTrig]
  do
    Adjacencies:=[];
    EXT:=ListTrig[iTrig];
    for iVert in [1..n+1]
    do
      eDiff:=Difference([1..n+1], [iVert]);
      EXTdiff:=EXT{eDiff};
      ListRecFind:=TRIG_FindTriangles(ListTrig, EXTdiff);
      if Length(ListRecFind)<>2 then
        Error("We should have 2 triangles");
      fi;
      if First(ListRecFind, x->x.iTrig=iTrig)=fail then
        Error("One of the triangle must be iTrig");
      fi;
      eRecFind:=First(ListRecFind, x->x.iTrig<>iTrig);
      eTrigImg:=ListTrig[eRecFind.iTrig]*eRecFind.eBigMat;
      eInt:=Intersection(Set(EXT), Set(eTrigImg));
      if Length(eInt)<>n then
        Error("eInt is not of right size");
      fi;
      eAdjInfo:=rec(iDelaunay:=eRecFind.iTrig, eBigMat:=eRecFind.eBigMat, eInc:=eDiff);
      Add(Adjacencies, eAdjInfo);
    od;
    eRecSimplex:=rec(EXT:=EXT, Adjacencies:=Adjacencies);
    Add(ListSimplices_FormalDelaunay, eRecSimplex);
  od;
  return rec(n:=n,
             ListTrig:=ListTrig,
             ListSimplices_FormalDelaunay:=ListSimplices_FormalDelaunay);
end;



# Check that each facet is really adjacent to another facet.
# In dimension 3, we can have two simplices both of which have
# facet which made together are a square.
# On the other side, we could have another subdivision of this
# square.
# This function checks that this phenomenon does not occur.
TRIG_CheckFaceToFaceTiling:=function(ListTrig)
  local n, nbTrig, iTrig, EXT, iVert, eDiff, EXTdiff, eRecFind, eBigMat, eAdjInfo, ListRecFind, eRecSimplex, eInt, eTrigImg;
  n:=Length(ListTrig[1])-1;
  nbTrig:=Length(ListTrig);
  for iTrig in [1..nbTrig]
  do
    EXT:=ListTrig[iTrig];
    for iVert in [1..n+1]
    do
      eDiff:=Difference([1..n+1], [iVert]);
      EXTdiff:=EXT{eDiff};
      ListRecFind:=TRIG_FindTriangles(ListTrig, EXTdiff);
      if Length(ListRecFind)<>2 then
        return false;
      fi;
    od;
  od;
  return true;
end;


# Test that the triangulation is defined by a quadratic form and returns
# the triangulation if it is found.
TRIG_TestDelaunayNessOfPeriodicTriangulation:=function(RecPeriodicTriang)
  local n, eCase, eRecIneq, ListIneq, TheSpace, TheDim, eTrig, TheAnswer, eInterior, eGramMat, i, FindClosestElement, LFC, RecTransClass, iDelaunay, eDelaunay, ListCont, iTrig;
  n:=RecPeriodicTriang.n;
  eCase:=GetStandardIntegralVoronoiSpace(n);
  eRecIneq:=WriteFaceInequalities(RecPeriodicTriang.ListSimplices_FormalDelaunay, eCase);
  TheDim:=Length(eCase.Basis);
  ListIneq:=List(eRecIneq.ListInequalities, x->x{[2..TheDim+1]});
  TheSpace:=LinearDeterminedByInequalities(ListIneq);
  if Length(TheSpace)<>TheDim then
    return rec(Answer:=false);
  fi;
  eInterior:=GetSpaceInteriorPoint_NoGroup(ListIneq);
  eGramMat:=NullMat(n,n);
  for i in [1..TheDim]
  do
    eGramMat:=eGramMat + eInterior[i]*eCase.Basis[i];
  od;
  FindClosestElement:=function(eVect)
    return CVPVallentinProgram(eGramMat, eVect);
  end;
  for eTrig in RecPeriodicTriang.ListTrig
  do
    TheAnswer:=CheckCoherencySingleDelaunay(eGramMat, eTrig, FindClosestElement);
    if TheAnswer.reply=false then
      return rec(Answer:=false);
    fi;
  od;
  LFC:=DelaunayComputationStandardFunctions(eGramMat);
  RecTransClass:=LFC.GetAllTranslationClassesDelaunay();
  Print("|RecTransClass.TotalListDelaunay|=", Length(RecTransClass.TotalListDelaunay), "\n");
  PrintArray(eGramMat);
  for iDelaunay in [1..Length(RecTransClass.TotalListDelaunay)]
  do
    eDelaunay:=RecTransClass.TotalListDelaunay[iDelaunay];
    ListCont:=TRIG_FindTriangles(RecPeriodicTriang.ListTrig, eDelaunay);
    if Length(ListCont)<>1 then
      Error("Inconsistency in the checks for Delaunayness 1");
    fi;
  od;
  for iTrig in [1..Length(RecPeriodicTriang.ListTrig)]
  do
    eTrig:=RecPeriodicTriang.ListTrig[iTrig];
    ListCont:=TRIG_FindTriangles(RecTransClass.TotalListDelaunay, eTrig);
    if Length(ListCont)<>1 then
      Error("Inconsistency in the checks for Delaunayness 2");
    fi;
  od;
  return rec(Answer:=true, GramMat:=eGramMat, RecTransClass:=RecTransClass);
end;



# Get the triangulation from the L-type
TRIG_GetTriangulationFromLtype:=function(eLtype)
  local n, eBigMat, ListTrig, eRec, i;
  n:=Length(eLtype[1].EXT)-1;
  eBigMat:=IdentityMat(n+1);
  for i in [1..n]
  do
    eBigMat[i+1][i+1]:=-1;
  od;
  ListTrig:=[];
  for eRec in eLtype
  do
    Add(ListTrig, eRec.EXT);
    Add(ListTrig, eRec.EXT*eBigMat);
  od;
  return ListTrig;
end;


# First versioin of the testing of regularity of a triagnulation
TRIG_General_PartialTestRegularity_V1:=function(RecPeriodicTriang, ListVert, RecAssignmentVertices)
  local n, nbTrig, TotalListTrig, iTrig, eTrig, ListSetMultiple, i, ListVal, MinIdx, MaxIdx, eSet, eVect, eBigMat, SetVert, ListTrigSet, eRecTrig, nSet, nbRecTrig, GRA, jTrig, eAdjInfo, iRecTrig, fBigMat, pos, mSet, ListConn, ListSizeConn, MaxSizeConn, eConn, RelSet, SetVertRed, SetVertAppear, ListTrigSetRed, TheFirst, TheDiffFirst, ListIneq, nbVar, hSet, eTrigRef, fTrig, TotalListTrigRed, iSet, eDiff, eAdjVert, eSol, eIneq, ToBeMinimized, TheLP, TheHeightFunction, ListScal, ListDiff, rSet, iVar, eMin, eMax, eRecMM, ListRangeIndices, nbAss, SetAssigned, ListValAssigned, eVal, iVert, eVert, posB;
  n:=RecPeriodicTriang.n;
  nbTrig:=Length(RecPeriodicTriang.ListTrig);
  TotalListTrig:=[];
  ListRangeIndices:=[];
  for i in [1..n]
  do
    eMin:=Minimum(List(eTrig, x->x[i+1]));
    eMax:=Maximum(List(eTrig, x->x[i+1]));
    eRecMM:=rec(eMin:=eMin, eMax:=eMax);
    Add(ListRangeIndices, eRecMM);
  od;
  SetVert:=Set(ListVert);
  Print("|ListVert|=", Length(ListVert), " |SetVert|=", Length(SetVert), "\n");
  for iTrig in [1..nbTrig]
  do
    eTrig:=RecPeriodicTriang.ListTrig[iTrig];
    ListSetMultiple:=[];
    for i in [1..n]
    do
      ListVal:=List(eTrig, x->x[i+1]);
      MinIdx:=ListRangeIndices[i].eMin - Minimum(ListVal);
      MaxIdx:=ListRangeIndices[i].eMax - Maximum(ListVal);
      eSet:=[MinIdx..MaxIdx];
      Add(ListSetMultiple, eSet);
    od;
    for eVect in BuildSetMultiple(ListSetMultiple)
    do
      eBigMat:=FuncCreateBigMatrix(eVect, IdentityMat(n));
      if IsSubset(SetVert, Set(eTrig*eBigMat)) then
        eRecTrig:=rec(iTrig:=iTrig, eVect:=eVect);
        Add(TotalListTrig, eRecTrig);
      fi;
    od;
  od;
  Print("|TotalListTrig|=", Length(TotalListTrig), "\n");
  #
  ListTrigSet:=[];
  for eRecTrig in TotalListTrig
  do
    eBigMat:=FuncCreateBigMatrix(eRecTrig.eVect, IdentityMat(n));
    eTrig:=RecPeriodicTriang.ListTrig[eRecTrig.iTrig]*eBigMat;
    nSet:=Set(List(eTrig, x->Position(SetVert, x)));
    Add(ListTrigSet, nSet);
  od;
  Print("We have ListTrigSet\n");
  #
  nbRecTrig:=Length(ListTrigSet);
  GRA:=NullGraph(Group(()), nbRecTrig);
  for iRecTrig in [1..nbRecTrig]
  do
    eRecTrig:=TotalListTrig[iRecTrig];
    eBigMat:=FuncCreateBigMatrix(eRecTrig.eVect, IdentityMat(n));
    eTrig:=RecPeriodicTriang.ListTrig[eRecTrig.iTrig]*eBigMat;
    for eAdjInfo in RecPeriodicTriang.ListSimplices_FormalDelaunay[eRecTrig.iTrig].Adjacencies
    do
      jTrig:=eAdjInfo.iDelaunay;
      fBigMat:=eAdjInfo.eBigMat*FuncCreateBigMatrix(eRecTrig.eVect, IdentityMat(n));
      fTrig:=RecPeriodicTriang.ListTrig[jTrig]*fBigMat;
      mSet:=Set(List(fTrig, x->Position(SetVert, x)));
      if Position(mSet, fail)=fail then
        pos:=Position(ListTrigSet, mSet);
        if pos=fail then
          Error("It should not be");
        fi;
        if pos=iRecTrig then
          Error("debug from that point");
        fi;
        AddEdgeOrbit(GRA, [iRecTrig, pos]);
      fi;
    od;
  od;
  Print("We have GRA\n");
  #
  ListConn:=ConnectedComponents(GRA);
  Print("|ListConn|=", Length(ListConn), "\n");
  ListSizeConn:=List(ListConn, Length);
  Print("ListSizeConn=", ListSizeConn, "\n");
  MaxSizeConn:=Maximum(ListSizeConn);
  pos:=Position(ListSizeConn, MaxSizeConn);
  eConn:=ListConn[pos];
  #
  RelSet:=[];
  for iSet in eConn
  do
    Append(RelSet, ListTrigSet[iSet]);
  od;
  SetVertAppear:=Set(RelSet);
  #
  TotalListTrigRed:=TotalListTrig{eConn};
  SetVertRed:=SetVert{SetVertAppear};
  ListTrigSetRed:=[];
  for iSet in eConn
  do
    nSet:=List(ListTrigSet[iSet], x->Position(SetVertAppear, x));
    Add(ListTrigSetRed, nSet);
  od;
  #
  SetAssigned:=[];
  ListValAssigned:=[];
  for iVert in [1..Length(RecAssignmentVertices.ListVert)]
  do
    eVert:=RecAssignmentVertices.ListVert[iVert];
    eVal:=RecAssignmentVertices.ListHeight[iVert];
    pos:=Position(SetVertRed, eVert);
    if pos<>fail then
      Add(SetAssigned, pos);
      Add(ListValAssigned, eVal);
    fi;
  od;
  TheDiffFirst:=Difference([1..Length(SetVertAppear)],SetAssigned);
  ListIneq:=[];
  nbVar:=Length(SetVertAppear) - Length(SetAssigned);
  for iRecTrig in [1..Length(eConn)]
  do
    hSet:=ListTrigSetRed[iRecTrig];
    eRecTrig:=TotalListTrig[iRecTrig];
    eBigMat:=FuncCreateBigMatrix(eRecTrig.eVect, IdentityMat(n));
    eTrig:=RecPeriodicTriang.ListTrig[eRecTrig.iTrig]*eBigMat;
    eTrigRef:=SetVertRed{hSet};
    if Set(eTrigRef)<>Set(eTrig) then
      Error("Not consistent");
    fi;
    for eAdjInfo in RecPeriodicTriang.ListSimplices_FormalDelaunay[eRecTrig.iTrig].Adjacencies
    do
      jTrig:=eAdjInfo.iDelaunay;
      fBigMat:=eAdjInfo.eBigMat*FuncCreateBigMatrix(eRecTrig.eVect, IdentityMat(n));
      fTrig:=RecPeriodicTriang.ListTrig[jTrig]*fBigMat;
      mSet:=Set(List(fTrig, x->Position(SetVertRed, x)));
      if Position(mSet, fail)=fail then
        pos:=Position(ListTrigSetRed, mSet);
        if pos=fail then
          Error("It should not be");
        fi;
        eDiff:=Difference(mSet, hSet);
        if Length(eDiff)<>1 then
          Error("Wrong eDiff size");
        fi;
        eAdjVert:=eDiff[1];
        eSol:=SolutionMat(eTrigRef, SetVertRed[eAdjVert]);
        eIneq:=ListWithIdenticalEntries(nbVar+1,0);
        eIneq[1]:=-1;
        pos:=Position(TheDiffFirst, eAdjVert);
        nbAss:=0;
        if pos<>fail then
          eIneq[pos+1]:=1;
          nbAss:=nbAss+1;
        else
          posB:=Position(SetAssigned, eAdjVert);
          eIneq[1]:=eIneq[1] + ListValAssigned[posB];
        fi;
        for i in [1..n+1]
        do
          pos:=Position(TheDiffFirst, hSet[i]);
          if pos<>fail then
            eIneq[pos+1]:=-eSol[i];
            nbAss:=nbAss+1;
          else
            posB:=Position(SetAssigned, hSet[i]);
            eIneq[1]:=eIneq[1] - ListValAssigned[posB];
          fi;
        od;
        if nbAss=0 then
          if eIneq[1]<0 then
            return rec(Answer:=false, reason:="The assigned values are not coherent");
          fi;
        else
          Add(ListIneq, eIneq);
        fi;
      fi;
    od;
  od;
  ToBeMinimized:=ListWithIdenticalEntries(nbVar+1,0);
  for iVar in [1..nbVar]
  do
    ToBeMinimized[iVar+1]:=1;
  od;
  Print("Linear programming has been build\n");
  Print("|ListIneq|=", Length(ListIneq), " nbVar=", nbVar, "\n");
#  TheLP:=LinearProgramming(ListIneq, ToBeMinimized);
  TheLP:=GLPK_LinearProgramming(ListIneq, ToBeMinimized);
  if IsBound(TheLP.eVect)=false then
    return rec(Answer:=false, reason:="Failed LP solution");
  fi;
  TheHeightFunction:=ListWithIdenticalEntries(Length(SetVertAppear),0);
  TheHeightFunction{TheDiffFirst}:=TheLP.eVect;
  for iRecTrig in [1..Length(eConn)]
  do
    hSet:=ListTrigSetRed[iRecTrig];
    eTrigRef:=SetVertRed{hSet};
    eSol:=SolutionMat(TransposedMat(eTrigRef), TheHeightFunction{hSet});
    ListScal:=List(SetVertRed, x->x*eSol);
    ListDiff:=TheHeightFunction - ListScal;
    if Minimum(ListDiff)<0 then
      return rec(Answer:=false, reason:="Failed non-negativity for the function");
    fi;
    rSet:=Filtered([1..Length(SetVertAppear)], x->ListDiff[x]=0);
    if IsSubset(rSet, hSet)=false then
      Error("More bugs to be resolved");
    fi;
    if rSet<>hSet then
      return rec(Answer:=false, reason:="Failed positivity for the function");
    fi;
  od;
  return rec(Answer:=true, reason:="Qualified success for that region. Nothing definitive", TheHeightFunction:=TheHeightFunction, ListVert:=SetVertRed);
end;


# Checking if a triangulation is regular (on a finite set of points)
# This is done via linear programming
TRIG_General_PartialTestRegularity:=function(RecPeriodicTriang, ListVert, RecAssignmentVertices)
  local n, nbTrig, TotalListTrig, iTrig, eTrig, ListSetMultiple, i, ListVal, MinIdx, MaxIdx, eSet, eVect, eBigMat, SetVert, ListTrigSet, eRecTrig, nSet, nbRecTrig, GRA, jTrig, eAdjInfo, iRecTrig, fBigMat, pos, mSet, ListConn, ListSizeConn, MaxSizeConn, eConn, RelSet, SetVertRed, SetVertAppear, ListTrigSetRed, TheFirst, TheDiffFirst, ListIneq, nbVar, hSet, eTrigRef, fTrig, TotalListTrigRed, iSet, eDiff, eAdjVert, eSol, eIneq, ToBeMinimized, TheLP, TheHeightFunction, ListScal, ListDiff, rSet, iVar, eMin, eMax, eRecMM, ListRangeIndices, nbAss, SetAssigned, ListValAssigned, eVal, iVert, eVert, posB, LVert, SetVertNative, CompleteListTriangles, RecInfo;

  n:=RecPeriodicTriang.n;
  nbTrig:=Length(RecPeriodicTriang.ListTrig);
  TotalListTrig:=[];
  ListTrigSet:=[];
  SetVert:=Set(ListVert);
  Print("|ListVert|=", Length(ListVert), " |SetVert|=", Length(SetVert), "\n");
  for iTrig in [1..nbTrig]
  do
    eTrig:=RecPeriodicTriang.ListTrig[iTrig];
    for eVert in SetVert
    do
      eDiff:=eVert - eTrig[1];
      LVert:=List(eTrig, x->x + eDiff);
      nSet:=Set(List(LVert, x->Position(SetVert, x)));
      if Position(nSet, fail)=fail then
        eVect:=eDiff{[2..n+1]};
        eRecTrig:=rec(iTrig:=iTrig, eVect:=eVect);
        Add(TotalListTrig, eRecTrig);
        Add(ListTrigSet, nSet);
      fi;
    od;
  od;
  nbRecTrig:=Length(ListTrigSet);
  Print("|TotalListTrig|=", nbRecTrig, "\n");
  SetVertNative:=List(SetVert, x->x{[2..n+1]});
  CompleteListTriangles:=List(ListTrigSet, x->SetVertNative{x});
  #
  GRA:=NullGraph(Group(()), nbRecTrig);
  for iRecTrig in [1..nbRecTrig]
  do
    eRecTrig:=TotalListTrig[iRecTrig];
    eBigMat:=FuncCreateBigMatrix(eRecTrig.eVect, IdentityMat(n));
    eTrig:=RecPeriodicTriang.ListTrig[eRecTrig.iTrig]*eBigMat;
    for eAdjInfo in RecPeriodicTriang.ListSimplices_FormalDelaunay[eRecTrig.iTrig].Adjacencies
    do
      jTrig:=eAdjInfo.iDelaunay;
      fBigMat:=eAdjInfo.eBigMat*eBigMat;
      fTrig:=RecPeriodicTriang.ListTrig[jTrig]*fBigMat;
      mSet:=Set(List(fTrig, x->Position(SetVert, x)));
      if Position(mSet, fail)=fail then
        pos:=Position(ListTrigSet, mSet);
        if pos=fail then
          Error("It should not be");
        fi;
        if pos=iRecTrig then
          Error("debug from that point");
        fi;
        AddEdgeOrbit(GRA, [iRecTrig, pos]);
      fi;
    od;
  od;
  Print("We have GRA\n");
  #
  ListConn:=ConnectedComponents(GRA);
  Print("|ListConn|=", Length(ListConn), "\n");
  ListSizeConn:=List(ListConn, Length);
  Print("ListSizeConn=", ListSizeConn, "\n");
  MaxSizeConn:=Maximum(ListSizeConn);
  pos:=Position(ListSizeConn, MaxSizeConn);
  eConn:=ListConn[pos];
  #
  RelSet:=[];
  for iSet in eConn
  do
    Append(RelSet, ListTrigSet[iSet]);
  od;
  SetVertAppear:=Set(RelSet);
  Print("|SetVertAppear|=", Length(SetVertAppear), "\n");
  #
  TotalListTrigRed:=TotalListTrig{eConn};
  SetVertRed:=SetVert{SetVertAppear};
  ListTrigSetRed:=[];
  for iSet in eConn
  do
    nSet:=List(ListTrigSet[iSet], x->Position(SetVertAppear, x));
    Add(ListTrigSetRed, nSet);
  od;
  RecInfo:=rec(ListTrigSet:=ListTrigSet, SetVert:=SetVertRed, CompleteListTriangles:=CompleteListTriangles);
  #
  SetAssigned:=[];
  ListValAssigned:=[];
  for iVert in [1..Length(RecAssignmentVertices.ListVert)]
  do
    eVert:=RecAssignmentVertices.ListVert[iVert];
    eVal:=RecAssignmentVertices.ListHeight[iVert];
    pos:=Position(SetVertRed, eVert);
    if pos<>fail then
      Add(SetAssigned, pos);
      Add(ListValAssigned, eVal);
    fi;
  od;
  TheDiffFirst:=Difference([1..Length(SetVertAppear)], SetAssigned);
  ListIneq:=[];
  nbVar:=Length(SetVertAppear) - Length(SetAssigned);
  for iRecTrig in [1..Length(eConn)]
  do
    hSet:=ListTrigSetRed[iRecTrig];
    eRecTrig:=TotalListTrig[iRecTrig];
    eBigMat:=FuncCreateBigMatrix(eRecTrig.eVect, IdentityMat(n));
    eTrig:=RecPeriodicTriang.ListTrig[eRecTrig.iTrig]*eBigMat;
    eTrigRef:=SetVertRed{hSet};
    if Set(eTrigRef)<>Set(eTrig) then
      Error("Not consistent");
    fi;
    for eAdjInfo in RecPeriodicTriang.ListSimplices_FormalDelaunay[eRecTrig.iTrig].Adjacencies
    do
      jTrig:=eAdjInfo.iDelaunay;
      fBigMat:=eAdjInfo.eBigMat*FuncCreateBigMatrix(eRecTrig.eVect, IdentityMat(n));
      fTrig:=RecPeriodicTriang.ListTrig[jTrig]*fBigMat;
      mSet:=Set(List(fTrig, x->Position(SetVertRed, x)));
      if Position(mSet, fail)=fail then
        pos:=Position(ListTrigSetRed, mSet);
        if pos=fail then
          Error("It should not be");
        fi;
        eDiff:=Difference(mSet, hSet);
        if Length(eDiff)<>1 then
          Error("Wrong eDiff size");
        fi;
        eAdjVert:=eDiff[1];
        eSol:=SolutionMat(eTrigRef, SetVertRed[eAdjVert]);
        eIneq:=ListWithIdenticalEntries(nbVar+1,0);
        eIneq[1]:=-1;
        pos:=Position(TheDiffFirst, eAdjVert);
        nbAss:=0;
        if pos<>fail then
          eIneq[pos+1]:=1;
          nbAss:=nbAss+1;
        else
          posB:=Position(SetAssigned, eAdjVert);
          eIneq[1]:=eIneq[1] + ListValAssigned[posB];
        fi;
        for i in [1..n+1]
        do
          pos:=Position(TheDiffFirst, hSet[i]);
          if pos<>fail then
            eIneq[pos+1]:=-eSol[i];
            nbAss:=nbAss+1;
          else
            posB:=Position(SetAssigned, hSet[i]);
            eIneq[1]:=eIneq[1] - ListValAssigned[posB];
          fi;
        od;
        if nbAss=0 then
          if eIneq[1]<0 then
            return rec(Answer:=false, reason:="The assigned values are not coherent");
          fi;
        else
          Add(ListIneq, eIneq);
        fi;
      fi;
    od;
  od;
  ToBeMinimized:=ListWithIdenticalEntries(nbVar+1,0);
  for iVar in [1..nbVar]
  do
    ToBeMinimized[iVar+1]:=1;
  od;
  Print("Linear programming has been build\n");
  Print("|ListIneq|=", Length(ListIneq), " nbVar=", nbVar, "\n");
#  TheLP:=LinearProgramming(ListIneq, ToBeMinimized);
  TheLP:=GLPK_LinearProgramming(ListIneq, ToBeMinimized);
  if IsBound(TheLP.eVect)=false then
    return rec(Answer:=false, reason:="Failed LP solution");
  fi;
  TheHeightFunction:=ListWithIdenticalEntries(Length(SetVertAppear),0);
  TheHeightFunction{TheDiffFirst}:=TheLP.eVect;
  for iRecTrig in [1..Length(eConn)]
  do
    hSet:=ListTrigSetRed[iRecTrig];
    eTrigRef:=SetVertRed{hSet};
    eSol:=SolutionMat(TransposedMat(eTrigRef), TheHeightFunction{hSet});
    ListScal:=List(SetVertRed, x->x*eSol);
    ListDiff:=TheHeightFunction - ListScal;
    if Minimum(ListDiff)<0 then
      return rec(Answer:=false, reason:="Failed non-negativity for the function", RecInfo:=RecInfo);
    fi;
    rSet:=Filtered([1..Length(SetVertAppear)], x->ListDiff[x]=0);
    if IsSubset(rSet, hSet)=false then
      Error("More bugs to be resolved");
    fi;
    if rSet<>hSet then
      return rec(Answer:=false, reason:="Failed positivity for the function", RecInfo:=RecInfo);
    fi;
  od;
  return rec(Answer:=true, reason:="Qualified success for that region. Nothing definitive", TheHeightFunction:=TheHeightFunction, RecInfo:=RecInfo);
end;



# Checking if a triangulation is regular on a partial finite set of vertices.
# The set of indices is specified via ListRangeIndices
TRIG_PartialTestRegularity:=function(RecPeriodicTriang, ListRangeIndices)
  local n, ListSetMultiple, i, eMin, eMax, eInterval, ListVert, eVect, eVert, GetTriangle, RecAssignmentVertices;
  n:=Length(ListRangeIndices);
  ListSetMultiple:=[];
  for i in [1..n]
  do
    eMin:=ListRangeIndices[i].eMin;
    eMax:=ListRangeIndices[i].eMax;
    eInterval:=[eMin..eMax];
    Add(ListSetMultiple, eInterval);
  od;
  ListVert:=[];
  for eVect in BuildSetMultiple(ListSetMultiple)
  do
    eVert:=Concatenation([1], eVect);
    Add(ListVert, eVert);
  od;
  GetTriangle:=function()
    local nbTrig, SetVert, eTrig, eVert, eDiff, LVert, nSet;
    nbTrig:=Length(RecPeriodicTriang.ListTrig);
    SetVert:=Set(ListVert);
    for eTrig in RecPeriodicTriang.ListTrig
    do
      for eVert in SetVert
      do
        eDiff:=eVert - eTrig[1];
        LVert:=List(eTrig, x->x + eDiff);
        nSet:=Set(List(LVert, x->Position(SetVert, x)));
        if Position(nSet, fail)=fail then
          return LVert;
        fi;
      od;
    od;
    Error("We should not reach that stage");
  end;
  RecAssignmentVertices:=rec(ListVert:=GetTriangle(),
                             ListHeight:=ListWithIdenticalEntries(n+1,0));
  return TRIG_General_PartialTestRegularity(RecPeriodicTriang, ListVert, RecAssignmentVertices);
end;








# Check of regularity of a triangulation that also respect a point group
# preserving the origin.
TRIG_PartialTestRegularityEquivariant:=function(RecPeriodicTriang, ListRangeIndices, GRP)
  local ListSetM, ListVert, n, TheSaturation;
  ListSetM:=List(ListRangeIndices, x->[x.eMin..x.eMax]);
  ListVert:=BuildSetMultiple(ListSetM);
  n:=Length(ListRangeIndices);
  TheSaturation:=function(ListVert, GRP)
    local TotSet, nbVert, NewSet, eGen, eBigMat;
    TotSet:=List(ListVert, x->x);
    while(true)
    do
      nbVert:=Length(TotSet);
      NewSet:=[];
      Append(NewSet, TotSet);
      for eGen in GeneratorsOfGroup(GRP)
      do
        eBigMat:=FuncCreateBigMatrix(ListWithIdenticalEntries(n,0),eGen);
        Append(NewSet, TotSet*eBigMat);
      od;
      TotSet:=Set(NewSet);
      if Length(TotSet)=nbVert then
        break;
      fi;
    od;
    return TotSet;
  end;

end;




TRIG_GetRandomAntisymmetricPair:=function(RecPeriodicTriang)
  local nbTrig, n, iTrig, iAdj, eBigMat, i, EXT, ListCont, jTrig, eAdj, EXTfacetB, eSimplex, eSet, jAdj, fPairSwitch, ePairSwitch;
  nbTrig:=Length(RecPeriodicTriang.ListTrig);
  n:=Length(RecPeriodicTriang.ListTrig[1])-1;
  iTrig:=Random([1..nbTrig]);
  iAdj:=Random([1..n+1]);
  ePairSwitch:=rec(iTrig:=iTrig, iAdj:=iAdj);
  eBigMat:=IdentityMat(n+1);
  for i in [1..n]
  do
    eBigMat[i+1][i+1]:=-1;
  od;
  EXT:=RecPeriodicTriang.ListTrig[iTrig]*eBigMat;
  ListCont:=TRIG_FindTriangles(RecPeriodicTriang.ListTrig, EXT);
  if Length(ListCont)<>1 then
    Error("Most likely, it is not symmetry invariant");
  fi;
  jTrig:=ListCont[1].iTrig;
  eAdj:=RecPeriodicTriang.ListSimplices_FormalDelaunay[iTrig].Adjacencies[iAdj];
  EXTfacetB:=RecPeriodicTriang.ListTrig[iTrig]{eAdj.eInc}*eBigMat;
  eSimplex:=RecPeriodicTriang.ListTrig[jTrig]*ListCont[1].eBigMat;
  eSet:=Set(List(EXTfacetB, x->Position(eSimplex, x)));
  jAdj:=Difference([1..n+1], eSet)[1];
  fPairSwitch:=rec(iTrig:=jTrig, iAdj:=jAdj);
  return [ePairSwitch, fPairSwitch];
#  return [ePairSwitch];
end;


# Do a bistellair flip of a set of pairs of triangles.
TRIG_DoFlippingTriangulation:=function(RecPeriodicTriang, ListPairSwitch)
  local n, ListTrig, ListSimplexRemoval, TotalListNewSimplices, ePairSwitch, eAdj, EXT1, EXT2, EXTtot, ListExistingSimplices, ListNewSimplices, i, eSet, EXTsimp, iTrig, iAdj, ListCont, ListVol1, ListVol2, eDiff, NewListTrig, NSP, eNSP, eIntSet, ListNewSmall, EXTint, EXTcentral, ListGroupSmall, ListLen, eNewSmall, NewListSimplices, NewTrig, ListSmallFaces, ListGroupSimplices, eSmallFace, ListDifference, FuncInsert, eCont, eDiffUnion, ListDiffUnion, TotalListTrig, TotalEXT, TheUnion;
  n:=RecPeriodicTriang.n;
  ListTrig:=RecPeriodicTriang.ListTrig;
  ListSimplexRemoval:=[];
  TotalListNewSimplices:=[];
  for ePairSwitch in ListPairSwitch
  do
    iTrig:=ePairSwitch.iTrig;
    iAdj:=ePairSwitch.iAdj;
    if Position(ListSimplexRemoval, iTrig)=fail then
      EXT1:=ListTrig[iTrig];
      eAdj:=RecPeriodicTriang.ListSimplices_FormalDelaunay[iTrig].Adjacencies[iAdj];
      EXT2:=ListTrig[eAdj.iDelaunay]*eAdj.eBigMat;
      EXTtot:=Union(Set(EXT1), Set(EXT2));
      if Length(EXTtot)<>n+2 then
        Error("Wrong size of EXTtot");
      fi;
      NSP:=NullspaceMat(EXTtot);
      if Length(NSP)<>1 then
        Error("We do not have correct NSP");
      fi;
      eNSP:=NSP[1];
      eIntSet:=Filtered([1..Length(EXTtot)], x->eNSP[x]<>0);
      EXTcentral:=Set(EXTtot{eIntSet});
      #
      ListExistingSimplices:=[];
      ListSmallFaces:=[];
      ListNewSmall:=[];
      for i in [1..n+2]
      do
        eSet:=Difference([1..n+2],[i]);
        EXTsimp:=EXTtot{eSet};
        EXTint:=Intersection(EXTsimp, EXTcentral);
        if RankMat(EXTsimp)=n+1 then
          ListCont:=TRIG_FindTriangles(ListTrig, EXTsimp);
          if Length(ListCont)>1 then
            Print("Bad inconsistency");
          fi;
          if Length(ListCont)=1 then
            Add(ListExistingSimplices, EXTsimp);
            Add(ListSmallFaces, EXTint);
          else
            Add(ListNewSmall, EXTint);
          fi;
        fi;
      od;
      #
      ListDifference:=[];
      ListGroupSimplices:=[];
      ListGroupSmall:=[];
      FuncInsert:=function(eTrig, eSmallFace)
        local eDiff, pos;
        eDiff:=Difference(Set(eTrig), EXTcentral);
        if IsSubset(Set(eTrig), EXTcentral) then
          Error("We have an unexpected inclusion");
        fi;
        pos:=Position(ListDifference, eDiff);
        if pos=fail then
          Add(ListDifference, eDiff);
          Add(ListGroupSimplices, [eTrig]);
          Add(ListGroupSmall, [eSmallFace]);
        else
          Add(ListGroupSimplices[pos], eTrig);
          Add(ListGroupSmall[pos], eSmallFace);
        fi;
      end;
      ListDiffUnion:=[];
      TotalListTrig:=[];
      TotalEXT:=[];
      for eSmallFace in ListSmallFaces
      do
        ListCont:=TRIG_FindTriangles(ListTrig, eSmallFace);
        Print("|ListCont|=", Length(ListCont), "\n");
        TheUnion:=[];
        for eCont in ListCont
        do
          Add(ListSimplexRemoval, eCont.iTrig);
          Add(TotalListTrig, eCont.eTrig);
          TotalEXT:=Union(TotalEXT, Set(eCont.eTrig));
          FuncInsert(eCont.eTrig, eSmallFace);
          TheUnion:=Union(TheUnion, eCont.eTrig);
        od;
        eDiffUnion:=Difference(TheUnion, Set(eSmallFace));
        Add(ListDiffUnion, eDiffUnion);
      od;
      ListLen:=List(ListGroupSimplices, Length);
      if Length(Set(ListLen))<>1 then
        Error("The groups seems to be of different length. Not expected");
      fi;
      NewListSimplices:=[];
      for eDiff in ListDifference
      do
        for eNewSmall in ListNewSmall
        do
          NewTrig:=Concatenation(eDiff, eNewSmall);
          Add(NewListSimplices, NewTrig);
        od;
      od;
      Append(TotalListNewSimplices, NewListSimplices);
    fi;
  od;
  Print("ListSimplexRemoval=", ListSimplexRemoval, "\n");
  eDiff:=Difference([1..Length(ListTrig)], Set(ListSimplexRemoval));
  NewListTrig:=Concatenation(ListTrig{eDiff}, TotalListNewSimplices);
  return TRIG_GetAdjacencyInformationOfTriangulation(NewListTrig);
end;





TRIG_CentralTriangulationDelaunay:=function(RecTransClass, DelCO, EXTspec, L_ListTrigSpec)
  local ListTranslationClasses, ListIso, FindPositionTransClass, nbTrans, n, ListCases, pos, aBigMat, i, EXTspecAnti, eIsoSpecAnti, iTransClass, eTransClass, eIso, eDiff, GetFacetTriangulation, CheckCoherency, eRecFind, posB, ListTrigSpec, bBigMat, eBigMat, ListTrigImg, fTrig, gTrig, eEnt1, eEnt2, eTrig, ListEntries;
  ListTranslationClasses:=RecTransClass.TotalListDelaunay;
  ListIso:=List(ListTranslationClasses, Isobarycenter);
  nbTrans:=Length(ListTranslationClasses);
  FindPositionTransClass:=function(EXT)
    local eIso, eDiff, eBigMat;
    eIso:=Isobarycenter(EXT);
    for iTransClass in [1..nbTrans]
    do
      eDiff:=eIso{[2..n+1]} - ListIso[iTransClass]{[2..n+1]};
      if IsIntegralVector(eDiff) then
        eBigMat:=FuncCreateBigMatrix(eDiff, IdentityMat(n));
        return rec(iTransClass:=iTransClass, eDiff:=eDiff, eBigMat:=eBigMat);
      fi;
    od;
    Error("We did not find the matching translation class");
  end;
  n:=Length(ListTranslationClasses[1][1])-1;
  aBigMat:=IdentityMat(n+1,n+1);
  for i in [1..n]
  do
    aBigMat[1+i][1+i]:=-1;
  od;
  GetFacetTriangulation:=function(EXTfacet, ListTrigEXT)
    local rnk, ListTrigFacet, eTrigEXT, fTrigEXT, eTrigFace;
    rnk:=RankMat(EXTfacet);
    ListTrigFacet:=[];
    for eTrigEXT in ListTrigEXT
    do
      fTrigEXT:=Filtered(eTrigEXT, x->Position(EXTfacet, x)<>fail);
      if PersoRankMat(fTrigEXT)=rnk then
        eTrigFace:=Set(List(fTrigEXT, x->Position(EXTfacet, x)));
        Add(ListTrigFacet, eTrigFace);
      fi;
    od;
    return Set(ListTrigFacet);
  end;
  CheckCoherency:=function(ListEntries)
    local ListITrans, eRecEntry, iTransClass, EXTtransClass, iDelaunay, GRPperm, ListTrigEXT, eAdjInfo, Orec, ePerm, fInc, eMatClass, EXTfacet, eMat, fMat, EXTadjDelaunay, eRecFind, EXTtransClassAdj, ListTrigFacet, ListTrigFacetAdj, ListTrigEXTadj, pos;
    ListITrans:=List(ListEntries, x->x.iTransClass);
    for eRecEntry in ListEntries
    do
      iTransClass:=eRecEntry.iTransClass;
      EXTtransClass:=ListTranslationClasses[iTransClass];
      iDelaunay:=RecTransClass.ListRecInfos[iTransClass].iDelaunay;
      GRPperm:=DelCO[iDelaunay].TheStab.PermutationStabilizer;
      ListTrigEXT:=List(eRecEntry.ListTrig, x->EXTtransClass{x});
      for eAdjInfo in DelCO[iDelaunay].Adjacencies
      do
        Orec:=OrbitWithAction(GRPperm, eAdjInfo.eInc, OnSets);
        for ePerm in Orec.ListElement
        do
          fInc:=OnSets(eAdjInfo.eInc, ePerm);
          eMatClass:=RecTransClass.ListRecInfos[iTransClass].eBigMat;
          EXTfacet:=DelCO[iDelaunay].EXT{fInc}*eMatClass;
          eMat:=Image(DelCO[iDelaunay].TheStab.PhiPermMat, ePerm);
          fMat:=eAdjInfo.eBigMat*eMat*eMatClass;
          EXTadjDelaunay:=DelCO[eAdjInfo.iDelaunay].EXT*fMat;
          if Intersection(Set(EXTtransClass), Set(EXTadjDelaunay))<>Set(EXTfacet) then
            Error("Inconsistency in EXTfacet");
          fi;
          eRecFind:=FindPositionTransClass(EXTadjDelaunay);
          pos:=Position(ListITrans, eRecFind.iTransClass);
          EXTtransClassAdj:=ListTranslationClasses[eRecFind.iTransClass]*eRecFind.eBigMat;
          if Set(EXTtransClassAdj)<>Set(EXTadjDelaunay) then
            Error("Inconsistency in Representations");
          fi;
          if pos<>fail then
            ListTrigEXTadj:=List(ListEntries[pos].ListTrig, x->EXTtransClassAdj{x});
            ListTrigFacet:=GetFacetTriangulation(EXTfacet, ListTrigEXT);
            ListTrigFacetAdj:=GetFacetTriangulation(EXTfacet, ListTrigEXTadj);
            Print("ListTrigFacet=", ListTrigFacet, "\n");
            Print("ListTrigFacetAdj=", ListTrigFacetAdj, "\n");
            if ListTrigFacet<>ListTrigFacetAdj then
              return false;
            fi;
          fi;
        od;
      od;
    od;
    return true;
  end;
  EXTspecAnti:=EXTspec*aBigMat;
  eRecFind:=FindPositionTransClass(EXTspecAnti);
  posB:=eRecFind.iTransClass;
  bBigMat:=eRecFind.eBigMat;
  eBigMat:=aBigMat*bBigMat;
  ListCases:=[];
  pos:=Position(ListTranslationClasses, EXTspec);
#  Print("pos=", pos, "\n");
  for ListTrigSpec in L_ListTrigSpec
  do
    eEnt1:=rec(iTransClass:=pos, ListTrig:=ListTrigSpec);
#    Print("eEnt1=", eEnt1, "\n");
    ListTrigImg:=[];
    for eTrig in ListTrigSpec
    do
      fTrig:=EXTspec{eTrig}*eBigMat;
      gTrig:=Set(List(fTrig, x->Position(ListTranslationClasses[posB], x)));
      Add(ListTrigImg, gTrig);
    od;
    eEnt2:=rec(iTransClass:=posB, ListTrig:=ListTrigImg);
    ListEntries:=[eEnt1, eEnt2];
    if CheckCoherency(ListEntries) then
      Add(ListCases, ListEntries);
    fi;
  od;
  return ListCases;
end;


# Two simplices T1, and T2.
# Does there exist an integer translation vector v such that
# T1 intersects T2+v nontrivially ?
# Take F a facet of T1.
# If for some facet F of T1 we have F.(T2 + v) <= 0
# then things are ok and there is no intersection
# That is if for one facet F we have max(F.T2) + F.v < 0
# then things are ok.
# So, in order to search for offending v, we need to look
# at the integer v satisfying
# max(F.T2) + F.v >= 0
#
# Once we have that we need to look at the intersections
# T1 inter T2+v
# f(x) +c >= 0 for x in T2
# f(x+ v) - f(v) + c >=0 for x+v in T2+v
TRIG_TestIntersectionPairSimplices:=function(Trig1, Trig2)
  local n, FAC1, ListIneq, eFAC, eVect, ListVal, maxVal, eCst, eIneq, FAC2, RecSolve, nbCase, SolveIntersection, iCase, v, eReply;
  n:=Length(Trig1[1])-1;
  FAC1:=DualDescription(Trig1);
  ListIneq:=[];
  for eFAC in FAC1
  do
    ListVal:=List(Trig2, x->x*eFAC);
#    Print("ListVal=", ListVal, "\n");
    maxVal:=Maximum(ListVal);
    eCst:=maxVal;
    eVect:=eFAC{[2..n+1]};
    eIneq:=Concatenation([eCst], eVect);
    Add(ListIneq, eIneq);
  od;
  FAC2:=DualDescription(Trig2);
  RecSolve:=RunZsolve(ListIneq);
  if Length(RecSolve.TheHOM)>0 then
    Error("We should not have any solution");
  fi;
  nbCase:=Length(RecSolve.TheINH);
#  Print("|RecSolve.TheINH|=", nbCase, "\n");
  SolveIntersection:=function(v)
    local FAC2trans, EXT2, eFAC, eCst, nCst, nFAC, FACtotal, eRelation, eSpann, ListVect, posNZ, eFirstNZ, eVert, eVectSpann, eVect, NewBasis, FACred, EXTred, EXTint, eFirst1, eFirst2;
    FAC2trans:=[];
    EXT2:=List(Trig2, x->x + Concatenation([0], v));
    for eFAC in FAC2
    do
      eCst:=eFAC[1];
      eVect:=eFAC{[2..n+1]};
      nCst:=eCst - eVect*v;
      nFAC:=Concatenation([nCst], eVect);
      Add(FAC2trans, nFAC);
    od;
    if First(EXT2, x->First(FAC2trans, y->y*x<0)<>fail)<>fail then
      Error("EXT2 / FAC2trans are incoherent");
    fi;
    FACtotal:=Concatenation(FAC1, FAC2trans);
    eRelation:=SearchPositiveRelationSimple(FACtotal);
    if eRelation=false then
      return rec(Answer:=true, meaning:="Intersection found", vector:=v, FACtotal:=FACtotal);
    fi;
    eSpann:=LinearDeterminedByInequalities(FACtotal);
    if Length(eSpann) >=1 then
      posNZ:=First([1..Length(eSpann)], x->eSpann[x][1]<>0);
      eFirstNZ:=eSpann[posNZ];
      eVert:=eFirstNZ/eFirstNZ[1];
      ListVect:=[];
      for eVectSpann in eSpann{Difference([1..Length(eSpann)], [posNZ])}
      do
        eVect:=eVectSpann - eVectSpann[1]*eVert;
        Add(ListVect, eVect);
      od;
      if Length(eSpann)>=2 then
        if RankMat(ListVect)<>Length(ListVect) then
          Error("ListVect has the wrong rank");
        fi;
        NewBasis:=Concatenation([eVert], ListVect);
        FACred:=List(FACtotal, x->List(NewBasis, y->y*x));
        EXTred:=DualDescription(FACred);
        EXTint:=List(EXTred, x->x*NewBasis);
      else
        EXTint:=[eVert];
      fi;
      eFirst1:=First(EXTint, x->Position(Trig1, x)=fail);
      eFirst2:=First(EXTint, x->Position(EXT2, x)=fail);
      if eFirst1<>fail or eFirst2<>fail then
        return rec(Answer:=true,
                   vector:=v,
                   meaning:="Non facedness",
                   EXTint:=EXTint,
                   EXT1:=Trig1,
                   EXT2:=EXT2);
      fi;
    fi;
    return rec(Answer:=false);
  end;
  for iCase in [1..nbCase]
  do
#    Print("  iCase=", iCase, "/", nbCase, "\n");
    v:=RecSolve.TheINH[iCase];
    eReply:=SolveIntersection(v);
    if eReply.Answer=true then
      return eReply;
    fi;
  od;
  return rec(Answer:=false,
             meaning:="No intersection found",
             RecSolve:=RecSolve,
             SolveIntersection:=SolveIntersection);
end;



TRIG_SearchPartialExtension_Exhaustive:=function(PartTrig, RecFacet)
  local n, ListTreated, siz, IsCorrect, LVect, eVect, NewTrig, setPartTrig, eVectExt;
  n:=Length(PartTrig[1])-1;
  ListTreated:=[];
  setPartTrig:=List(PartTrig, Set);
  siz:=1;
  IsCorrect:=function(NewTrig)
    local TheVol, eTrig, RecTest;
    if First(NewTrig, x->RecFacet.eIneq*x < 0)<>fail then
      return false;
    fi;
    if RankMat(NewTrig)<>n+1 then
      return false;
    fi;
    if Position(setPartTrig, NewTrig)<>fail then
      return false;
    fi;
    TheVol:=AbsInt(DeterminantMat(NewTrig));
    Print("TheVol=", TheVol, "\n");
    for eTrig in PartTrig
    do
      RecTest:=TRIG_TestIntersectionPairSimplices(eTrig, NewTrig);
      if RecTest.Answer=true then
        return false;
      fi;
    od;
    return true;
  end;
  while(true)
  do
    LVect:=BuildSet(n, [-siz..siz]);
    for eVect in LVect
    do
      if Position(ListTreated, eVect)=fail then
        Print("Treating eVect=", eVect, " |PartTrig|=", Length(PartTrig), " |ListTreated|=", Length(ListTreated), "\n");
        Add(ListTreated, eVect);
        eVectExt:=Concatenation([1], eVect);
        NewTrig:=Set(Concatenation(RecFacet.EXT{RecFacet.eInc}, [eVectExt]));
        if IsCorrect(NewTrig) then
          return Concatenation(PartTrig, [NewTrig]);
        fi;
      fi;
    od;
    Print("siz=", siz, " |ListTreated|=", Length(ListTreated), "\n");
    siz:=siz+1;
  od;
end;


# A polytope ePoly is a constrained Delaunay polytope if for all the points that
# are inside the sphere, there is no straight path from this point to the inside
# of ePoly.
# This condition, while well stated, seems difficult to test algoritimically.
TRIG_IsAdmissible_ConstrainedDelaunay:=function(ListPoly, GramMat, ePoly)

end;



TRIG_SearchPartialExtension_ConstrainedDelaunay:=function(PartTrig, GramMat, RecFacet)
  local EXTadj;
  EXTadj:=FindAdjacentDelaunayPolytope(GramMat, RecFacet.EXT, RecFacet.eInc);
end;




# In principle this function should take a partial triangulation
# and extend it to a complete triangulation of the space.
# (Never teested to work)
TRIG_IterateToGlobalTriangulation:=function(PartTrig)
  local WorkListTrig, RecFacet, EXTdiff, ListVol, sumVol;
  WorkListTrig:=List(PartTrig, x->x);
  while(true)
  do
    RecFacet:=TRIG_FindUnmatchedFacet(WorkListTrig);
    if RecFacet=fail then
      return WorkListTrig;
    fi;
    WorkListTrig:=TRIG_SearchPartialExtension_Exhaustive(WorkListTrig, RecFacet);
    ListVol:=List(WorkListTrig, x->AbsInt(DeterminantMat(x)));
    sumVol:=Sum(ListVol);
    Print("nbTrig=", Length(WorkListTrig), " sumVol=", sumVol, "\n");
  od;
end;






# Given Two simplices T1 and T2
# we consider the minkowski difference T1 - T2 and enumerate
# the number of integral point in this difference.
TRIG_NumberIntegralPointsMinkowskiDifference:=function(Trig1, Trig2)
  local EXT, eVert1, eVert2, eDiff, NewVert, FAC, RecSolve, nbIntegralPoint;
  EXT:=[];
  for eVert1 in Trig1
  do
    for eVert2 in Trig2
    do
      eDiff:=eVert2 - Trig2[1];
      NewVert:=eVert1 - eDiff;
      Add(EXT, NewVert);
    od;
  od;
  FAC:=DualDescription(EXT);
  RecSolve:=RunZsolve(FAC);
  if Length(RecSolve.TheHOM)>0 then
    Error("We should not have any solution");
  fi;
  nbIntegralPoint:=Length(RecSolve.TheINH);
  return nbIntegralPoint;
end;



SearchMatchingPolytope:=function(fPolytope, ListPolytope)
  local n, nbPoly, SetPolytope, iPoly, ePolytope, eEXT, fEXT, eDiff, EXTimg, eDiffRed, eBigMat, eRecReturn;
  nbPoly:=Length(ListPolytope);
  SetPolytope:=Set(fPolytope);
  n:=Length(fPolytope[1])-1;
  for iPoly in [1..nbPoly]
  do
    ePolytope:=ListPolytope[iPoly];
    eEXT:=ePolytope[1];
    for fEXT in fPolytope
    do
      eDiff:=fEXT - eEXT;
      EXTimg:=List(ePolytope, x->x + eDiff);
      if Set(EXTimg)=SetPolytope then
        eDiffRed:=eDiff{[2..n+1]};
        eBigMat:=FuncCreateBigMatrix(-eDiffRed, IdentityMat(n));
        eRecReturn:=rec(iPoly:=iPoly, eBigMat:=eBigMat);
        return eRecReturn;
      fi;
    od;
  od;
  return fail;
end;


TRIG_ComputeAllFlipping:=function(RecPeriodicTriang, MatrGRP)
  local RecAdj, ListTrig, n, ListPossibilities, ListEXTcentral, FuncInsert, nbSimp, iSimp, eInfo1, eInfo2, eInfo, NSP, eNSP, eIntSet, eIntP, eIntN, eIntF, Collection_ListTrig, RelInt, eDiff, NewSimp, eAdj, i, ePossibility, iColl, ListCont, ListPos, pos, NewListTrig, ListMatchedSimplices, EXTcentral, eRepartitioning, eSimp, nbColl, idx, iCase, nbCase, ListEXTcentralCan, ListPermGens, eGen, eBigGen, eList, eEXTcentral, EXTcentralImg, EXTcentralImgCan, ePerm, GRPpermCentral, O, nbO, eO, iO;
  RecAdj:=RecPeriodicTriang.ListSimplices_FormalDelaunay;
  ListTrig:=RecPeriodicTriang.ListTrig;
  n:=Length(RecAdj[1].EXT)-1;
  ListPossibilities:=[];
  ListEXTcentral:=[];
  FuncInsert:=function(eInfo)
    local eInfo1, eInfo2, EXT1, EXT2, eInt, EXTtot, NSP, eNSP, eIntSet, EXTcentral, ListPos1, ListPos2, pos1, pos2, eSign, eCollSimplices, eDiff, eSimp, ListCont, eFind, NewREC, iPoss, eFindColl, iColl, ListSimplicesA, ListSimplicesB, eRepartitioning, i, NewCollSimplices, NewRepartitioning;
    eInfo1:=eInfo[1];
    eInfo2:=eInfo[2];
    EXT1:=ListTrig[eInfo1.iSimp]*eInfo1.eBigMat;
    EXT2:=ListTrig[eInfo2.iSimp]*eInfo2.eBigMat;
    eInt:=Intersection(Set(EXT1), Set(EXT2));
    if Length(eInt)<>n then
      Error("Consistency error for eInt");
    fi;
    eRepartitioning:=Union(Set(EXT1), Set(EXT2));
    NSP:=NullspaceMat(eRepartitioning);
    if Length(NSP)<>1 then
      Error("We do not have correct NSP");
    fi;
    eNSP:=NSP[1];
    eIntSet:=Filtered([1..Length(eRepartitioning)], x->eNSP[x]<>0);
    EXTcentral:=Set(eRepartitioning{eIntSet});
    ListPos1:=List(EXT1, x->Position(eRepartitioning, x));
    ListPos2:=List(EXT2, x->Position(eRepartitioning, x));
    pos1:=Difference([1..n+2], Set(ListPos1))[1];
    pos2:=Difference([1..n+2], Set(ListPos2))[1];
    if eNSP[pos1]=0 or eNSP[pos2]=0 then
      Error("Thinking error that is for sure");
    fi;
    if eNSP[pos1]*eNSP[pos2]<0 then
      Error("Signs are not correct");
    fi;
    eSign:=eNSP[pos1];
    eCollSimplices:=[];
    for i in [1..n+2]
    do
      if eNSP[i]*eSign>0 then
        eDiff:=Difference([1..n+2], [i]);
        eSimp:=eRepartitioning{eDiff};
        ListCont:=TRIG_FindTriangles(ListTrig, eSimp);
        # It can happen that those simplices do not occur
        if Length(ListCont)<>1 then
          return;
        fi;
        Add(eCollSimplices, eSimp);
      fi;
    od;
    eFind:=SearchMatchingPolytope(EXTcentral, ListEXTcentral);
    if eFind=fail then
      NewREC:=rec(EXTcentral:=EXTcentral, ListCollectionSimplices:=[eCollSimplices], ListRepartitioning:=[eRepartitioning]);
      Add(ListEXTcentral, EXTcentral);
      Add(ListPossibilities, NewREC);
      return;
    fi;
    iPoss:=eFind.iPoly;
    eFindColl:=SearchMatchingPolytope(eRepartitioning, ListPossibilities[iPoss].ListRepartitioning);
    if eFindColl=fail then
      if Set(EXTcentral*eFind.eBigMat)<>Set(ListEXTcentral[iPoss]) then
        Error("Consistency error for EXTcentral");
      fi;
      NewCollSimplices:=List(eCollSimplices, x->List(x, y->y*eFind.eBigMat));
      NewRepartitioning:=eRepartitioning*eFind.eBigMat;
      Add(ListPossibilities[iPoss].ListCollectionSimplices, NewCollSimplices);
      Add(ListPossibilities[iPoss].ListRepartitioning, NewRepartitioning);
      return;
    fi;
    iColl:=eFindColl.iPoly;
    ListSimplicesA:=List(eCollSimplices, x->Set(x*eFindColl.eBigMat));
    ListSimplicesB:=List(ListPossibilities[iPoss].ListCollectionSimplices[iColl], Set);
    if Set(ListSimplicesA)<>Set(ListSimplicesB) then
      Error("Inconsistency error for ListSimplicesA/B");
    fi;
  end;
  nbSimp:=Length(RecAdj);
  for iSimp in [1..nbSimp]
  do
    for i in [1..n+1]
    do
      eAdj:=RecAdj[iSimp].Adjacencies[i];
      eInfo1:=rec(iSimp:=iSimp, eBigMat:=IdentityMat(n+1));
      eInfo2:=rec(iSimp:=eAdj.iDelaunay, eBigMat:=eAdj.eBigMat);
      eInfo:=[eInfo1, eInfo2];
      FuncInsert(eInfo);
    od;
  od;
  Collection_ListTrig:=[];
  nbCase:=Length(ListPossibilities);
  ListEXTcentralCan:=List(ListPossibilities, x->TRIG_CanonicalizeFace(x.EXTcentral));
  ListPermGens:=[];
  for eGen in GeneratorsOfGroup(MatrGRP)
  do
    eBigGen:=FuncCreateBigMatrix(ListWithIdenticalEntries(n,0), eGen);
    eList:=[];
    for eEXTcentral in ListEXTcentralCan
    do
      EXTcentralImg:=eEXTcentral*eBigGen;
      EXTcentralImgCan:=TRIG_CanonicalizeFace(EXTcentralImg);
      pos:=Position(ListEXTcentralCan, EXTcentralImgCan);
      Add(eList, pos);
    od;
    ePerm:=PermList(eList);
    Add(ListPermGens, ePerm);
  od;
  GRPpermCentral:=Group(ListPermGens);
  O:=Orbits(GRPpermCentral, [1..nbCase], OnPoints);
  nbO:=Length(O);
  Print("|ListPossibilities|=", nbCase, " |O|=", nbO, "\n");
  for iO in [1..nbO]
  do
    Print("iO=", iO, "/", nbO, "\n");
    eO:=O[iO];
    iCase:=eO[1];
    ePossibility:=ListPossibilities[iCase];
    ListMatchedSimplices:=[];
    NewListTrig:=[];
    EXTcentral:=ePossibility.EXTcentral;
    nbColl:=Length(ePossibility.ListCollectionSimplices);
    for iColl in [1..nbColl]
    do
      eRepartitioning:=ePossibility.ListRepartitioning[iColl];
      NSP:=NullspaceMat(eRepartitioning);
      eNSP:=NSP[1];
      eIntSet:=Filtered([1..Length(eRepartitioning)], x->eNSP[x]<>0);
      eIntP:=Filtered([1..Length(eRepartitioning)], x->eNSP[x]>0);
      eIntN:=Filtered([1..Length(eRepartitioning)], x->eNSP[x]<0);
      eIntF:=[];
      for eSimp in ePossibility.ListCollectionSimplices[iColl]
      do
        ListCont:=TRIG_FindTriangles(ListTrig, eSimp);
        if Length(ListCont)<>1 then
          Error("We did not find the simplex");
        fi;
        Add(ListMatchedSimplices, ListCont[1].iTrig);
        ListPos:=List(eSimp, x->Position(eRepartitioning, x));
        pos:=Difference([1..n+2],ListPos)[1];
        Add(eIntF, pos);
      od;
      if Set(eIntF)<>Set(eIntP) and Set(eIntF)<>Set(eIntN) then
        Error("No finding position");
      fi;
      if Set(eIntF)=Set(eIntP) then
        RelInt:=eIntN;
      else
        RelInt:=eIntP;
      fi;
      for idx in RelInt
      do
        eDiff:=Difference([1..n+2], [idx]);
        NewSimp:=eRepartitioning{eDiff};
        Add(NewListTrig, NewSimp);
      od;
    od;
    eDiff:=Difference([1..nbSimp], Set(ListMatchedSimplices));
    Append(NewListTrig, ListTrig{eDiff});
    if TRIG_CheckFaceToFaceTiling(NewListTrig) then
      Add(Collection_ListTrig, NewListTrig);
    fi;
  od;
  return Collection_ListTrig;
end;


# We start with a standard triangulation
# and we consider all possible flippings.
# We finish when all the triangulations have been flipped.
# Algorithm works in dimension 4 and 5 but explodes beyond.
DoEnumerationByFlipping:=function(n)
  local GramMat, GramMatInv, LFC, ListTrig, List_ListTrig, ListStatus, FuncInsert, IsFinished, nbCase, iCase, RecPeriodicTriang, eNewListTrig, iListTrig, nbListTrig, ListInv, ListGRP, eInv, GRP, nbDone;
  GramMat:=LatticeAn(n).GramMat;
  GramMatInv:=Inverse(GramMat);
  LFC:=DelaunayComputationStandardFunctions(GramMatInv);
  ListTrig:=LFC.GetAllTranslationClassesDelaunay().TotalListDelaunay;
  List_ListTrig:=[];
  ListStatus:=[];
  ListInv:=[];
  ListGRP:=[];
  nbDone:=0;
  FuncInsert:=function(eListTrig)
    local eInv, fListTrig, test, fInv, jListTrig, eGRP;
    eInv:=TRIG_Invariant(eListTrig);
    for jListTrig in [1..Length(List_ListTrig)]
    do
      fListTrig:=List_ListTrig[jListTrig];
      fInv:=ListInv[jListTrig];
      if eInv=fInv then
        test:=TRIG_IsEquivalentTriangulationCanonic(eListTrig, fListTrig);
        if test<>false then
          return;
        fi;
      fi;
    od;
    Add(List_ListTrig, TRIG_CanonicalizeExpression(eListTrig));
    Add(ListStatus, 1);
    Add(ListInv, eInv);
    eGRP:=TRIG_GetSymmetryGroupTriangulation(eListTrig).eGRP;
    Add(ListGRP, eGRP);
    Print("Now we have |List_ListTrig|=", Length(List_ListTrig), "  nbDone=", nbDone, "\n");
  end;
  FuncInsert(ListTrig);
  while(true)
  do
    IsFinished:=true;
    nbListTrig:=Length(List_ListTrig);
    for iListTrig in [1..nbListTrig]
    do
      if ListStatus[iListTrig]=1 then
        Print("nbListTrig=", Length(List_ListTrig), " nbDone=", nbDone, "\n");
        ListStatus[iListTrig]:=0;
        IsFinished:=false;
        RecPeriodicTriang:=TRIG_GetAdjacencyInformationOfTriangulation(List_ListTrig[iListTrig]);
        GRP:=ListGRP[iListTrig];
        for eNewListTrig in TRIG_ComputeAllFlipping(RecPeriodicTriang, GRP)
        do
          FuncInsert(eNewListTrig);
        od;
        nbDone:=nbDone+1;
      fi;
    od;
    if IsFinished then
      break;
    fi;
  od;
  return List_ListTrig;
end;



TRIG_EnumeratePossiblePairsSimplicesVolumeOne:=function(n, MaxVal)
  local eSimp, i, eBasis, eVect, TheSpacePoss, ListPairs, ePoss, NewVert, NewSimp, eTest, NewPair, nbPoss, iPoss, ListMatrGens, GRP, ListCases, eGen, eMatr, TheAction, ListCandRepr, ListOrbitMatch, eCand, eBigMat, eRec, GRPmatr, ePoint, eHyp, GRPtot, ListGensTot, ListMatrGensTot, GRPmatrTot, phi, TotalListAdjacent, eInt, eSet, eRecO, nbEnt, iEnt, eSingleOrbitPoint, fBigMat, eOrbitSimplex, ListOrbitSimplices, nbIntegral, iCand, nbCand;
  eSimp:=NullMat(n+1,n+1);
  for i in [1..n+1]
  do
    eSimp[i][i]:=1;
    eSimp[i][1]:=1;
  od;
  eBasis:=[];
  for i in [1..n-1]
  do
    eVect:=eSimp[i+2]-eSimp[2];
    Add(eBasis, eVect);
  od;
  TheSpacePoss:=BuildSet(n-1, [-MaxVal..MaxVal]);
  nbPoss:=Length(TheSpacePoss);
  ListCases:=[];
  for iPoss in [1..nbPoss]
  do
    ePoss:=TheSpacePoss[iPoss];
    Print("iPoss = ", iPoss, " / ", nbPoss, "     ePoss=", ePoss, "\n");
    NewVert:=2*eSimp[2] - eSimp[1];
    for i in [1..n-1]
    do
      NewVert:=NewVert + ePoss[i]*eBasis[i];
    od;
    NewSimp:=Concatenation(eSimp{[2..n+1]}, [NewVert]);
    Add(ListCases, Set(NewSimp));
  od;
  GRP:=SymmetricGroup([2..n+1]);
  ListMatrGens:=[];
  for eGen in GeneratorsOfGroup(GRP)
  do
    eMatr:=FindTransformation(eSimp, eSimp, eGen);
    Add(ListMatrGens, eMatr);
  od;
  GRPmatr:=Group(ListMatrGens);
  #
  GRPtot:=SymmetricGroup([1..n+1]);
  ListGensTot:=GeneratorsOfGroup(GRPtot);
  ListMatrGensTot:=[];
  for eGen in ListGensTot
  do
    eMatr:=FindTransformation(eSimp, eSimp, eGen);
    Add(ListMatrGensTot, eMatr);
  od;
  GRPmatrTot:=Group(ListMatrGensTot);
  phi:=GroupHomomorphismByImagesNC(GRPtot, GRPmatrTot, ListGensTot, ListMatrGensTot);
  #
  TheAction:=function(x, g)
    return Set(x*g);
  end;
  ListCandRepr:=OrbitDecomposition(ListCases, GRPmatr, TheAction);
  ListOrbitMatch:=[];
  TotalListAdjacent:=[];
  nbCand:=Length(ListCandRepr);
  for iCand in [1..nbCand]
  do
    Print("  iCand=", iCand, "/", nbCand, "\n");
    eCand:=ListCandRepr[iCand];
    eTest:=TRIG_TestIntersectionPairSimplices(eSimp, eCand);
    if eTest.Answer=false then
      eBigMat:=Inverse(eSimp)*eCand;
      eInt:=Intersection(Set(eCand), Set(eSimp));
      eSet:=Set(List(eInt, x->Position(eSimp,x)));
      ePoint:=Difference(Set(eCand), Set(eSimp))[1];
      eHyp:=SolutionMat(eSimp, ePoint);
      nbIntegral:=TRIG_NumberIntegralPointsMinkowskiDifference(eSimp, eCand);
      eRec:=rec(iSimp:=1, eBigMat:=eBigMat, ePoint:=ePoint, eHyp:=eHyp, eSet:=eSet, nbIntegral:=nbIntegral);
      Add(ListOrbitMatch, eRec);
      eRecO:=OrbitWithAction(GRPmatr, eCand, TheAction);
      nbEnt:=Length(eRecO.ListCoset);
      for iEnt in [1..nbEnt]
      do
        fBigMat:=eBigMat*eRecO.ListElement[iEnt];
        eRec:=rec(iOrbitSimpl:=1, eBigMat:=fBigMat);
        Add(TotalListAdjacent, eRec);
      od;
    fi;
  od;
  eSingleOrbitPoint:=rec(iPoint:=1, ListOrbitMatch:=ListOrbitMatch, TotalListAdjacent:=TotalListAdjacent);
  eOrbitSimplex:=rec(ListOrbitPoint:=[eSingleOrbitPoint], PermGrp:=GRPtot, phi:=phi, ListOrbitRepresentative:=ListWithIdenticalEntries(n+1,1), eSimp:=eSimp);
  ListOrbitSimplices:=[eOrbitSimplex];
  return rec(n:=n, MaxVal:=MaxVal,
             ListOrbitSimplices:=ListOrbitSimplices);
end;


TRIG_EnumeratePossiblePairsSimplices_General:=function(TheSimplex, TheDist, SavePrefix)
  local n, TheGram, recGRP, TheAction, GetLowestRepresentation, nbVert, TheCent, ListAnswer_Pair, ListAnswer_realizability, nbEntry, TheFile, GetTestRealizability, GetReply, ListAcceptableAnswer, idx, eVext, ePair, ListVert, test, eV, TheLowest, iPoss, nbPoss, GetStringPair, eRec;
  n:=Length(TheSimplex[1])-1;
  TheGram:=RemoveFractionMatrix(SIMPLEX_GetCharacteristicGramMatrix(TheSimplex));
  recGRP:=SIMPLEX_Stabilizer(TheSimplex);
  TheAction:=function(x, g)
    return [x[1]*g, x[2]*g];
  end;
  GetLowestRepresentation:=function(ePair)
    local PairVert, O, TheMin, idxRet;
    PairVert:=[ePair.eVert, TheSimplex[ePair.idx]];
    O:=Orbit(recGRP.MatrGRP, PairVert, TheAction);
    TheMin:=Set(O)[1];
    idxRet:=Position(TheSimplex, TheMin[2]);
    return rec(eVert:=TheMin[1], idx:=idxRet);
  end;
  nbVert:=Length(TheSimplex);
  TheCent:=Isobarycenter(TheSimplex);
  ListAnswer_Pair:=[];
  ListAnswer_realizability:=[];
  nbEntry:=0;
  while(true)
  do
    TheFile:=Concatenation(SavePrefix, "Simplex_", String(nbEntry+1));
    if IsExistingFilePlusTouch(TheFile)=false then
      break;
    fi;
    eRec:=ReadAsFunction(TheFile)();
    Add(ListAnswer_Pair, eRec.ePair);
    Add(ListAnswer_realizability, eRec.realizable);
    nbEntry:=nbEntry+1;
  od;
  GetTestRealizability:=function(ePair)
    local TheDiff, NewSimplex, eTest;
    TheDiff:=Difference([1..nbVert], [ePair.idx]);
    NewSimplex:=Concatenation([ePair.eVert], TheSimplex{TheDiff});
    if RankMat(NewSimplex)<n+1 then
      return false;
    fi;
    eTest:=TRIG_TestIntersectionPairSimplices(NewSimplex, TheSimplex);
    if eTest.Answer=false then
      return true;
    else
      return false;
    fi;
  end;
  GetReply:=function(ePair)
    local pos, TheLowest, eAnswer, test, NewAnswer, TheFile;
    pos:=Position(ListAnswer_Pair, ePair);
    if pos<>fail then
      return ListAnswer_realizability[pos];
    fi;
    test:=GetTestRealizability(ePair);
    NewAnswer:=rec(ePair:=ePair, realizable:=test);
    nbEntry:=nbEntry+1;
    TheFile:=Concatenation(SavePrefix, "Simplex_", String(nbEntry));
    SaveDataToFilePlusTouch(TheFile, NewAnswer);
    return test;
  end;
  GetStringPair:=function(ePair)
    return Concatenation("(", String(ePair.eVert), " idx=", String(ePair.idx), ")");
  end;
  ListVert:=ClosestAtDistanceVallentinProgram(TheGram, TheCent, TheDist);
  nbPoss:=Length(ListVert);
  Print("|ListVert|=", nbPoss, "\n");
  ListAcceptableAnswer:=[];
  for iPoss in [1..nbPoss]
  do
    Print("iPoss=", iPoss, " / ", nbPoss, " |ListAcceptableAnswer|=", Length(ListAcceptableAnswer), "\n");
    eV:=ListVert[iPoss];
    eVext:=Concatenation([1], eV);
    if Position(TheSimplex, eVext)=fail then
      for idx in [1..n+1]
      do
        ePair:=rec(eVert:=eVext, idx:=idx);
        TheLowest:=GetLowestRepresentation(ePair);
        test:=GetReply(ePair);
        Print("  ePair=", GetStringPair(ePair), " TheLowest=", GetStringPair(TheLowest), " test=", test, "\n");
        if test then
          AddSet(ListAcceptableAnswer, TheLowest);
        fi;
      od;
    fi;
  od;
  return ListAcceptableAnswer;
end;



# Returns true if two simplices are translationanlly equivalent and
# false otherwise.
TRIG_TestTranslationalEquivalence:=function(eTrig, fTrig)
  local n, i, eVect, eTrigImg;
  n:=Length(eTrig[1])-1;
  for i in [1..n+1]
  do
    eVect:=fTrig[i] - eTrig[1];
    eTrigImg:=List(eTrig, x->x + eVect);
    if Set(eTrigImg)=Set(fTrig) then
      return true;
    fi;
  od;
  return false;
end;


# This function takes a partial description of a triangulation
# a simplex and returns another partial triangulation with this simplex
# being appended.
TRIG_AppendSimplex:=function(eCand, eSimplex)
  local n, NewCand, eRec, NewSimp, eTest, nbNewSimp, i, eDiff, EXTface, ListFind, ListITrig, pos, posB, iTrigFind, EXTimage, posPoint, findBigMat, eRecAdj, EXTadj, TestAdj, ListMiss, CopyRec;
#  Print("Begin TRIG_AppendSimplex\n");
  n:=Length(eSimplex.EXT[1])-1;
  CopyRec:=function(eRec)
    local RetEXT, i, j, ListFaceStatus, eRecAdj, eBigMat, nRecAdj;
    RetEXT:=NullMat(n+1,n+1);
    for i in [1..n+1]
    do
      for j in [1..n+1]
      do
        RetEXT[i][j]:=eRec.EXT[i][j];
      od;
    od;
    ListFaceStatus:=[];
    for eRecAdj in eRec.ListFaceStatus
    do
      if eRecAdj=0 then
        Add(ListFaceStatus, 0);
      else
        eBigMat:=NullMat(n+1,n+1);
        for i in [1..n+1]
        do
          for j in [1..n+1]
          do
            eBigMat[i][j]:=eRecAdj.eBigMat[i][j];
          od;
        od;
        nRecAdj:=rec(iDelaunay:=eRecAdj.iDelaunay, eBigMat:=eBigMat);
        Add(ListFaceStatus, nRecAdj);
      fi;
    od;
    eBigMat:=NullMat(n+1,n+1);
    for i in [1..n+1]
    do
      for j in [1..n+1]
      do
        eBigMat[i][j]:=eRec.eBigMat[i][j];
      od;
    od;
    return rec(iOrbitSimpl:=eRec.iOrbitSimpl, EXT:=RetEXT, ListFaceStatus:=ListFaceStatus, eBigMat:=eBigMat);
  end;
  NewCand:=[];
  for eRec in eCand
  do
    Add(NewCand, CopyRec(eRec));
  od;
  Add(NewCand, CopyRec(eSimplex));
  nbNewSimp:=Length(NewCand);
  TestAdj:=function(iSimpl, i)
    local eDiff, eRecAdj, EXTface, EXTadj;
    eDiff:=Difference([1..n+1],[i]);
    eRecAdj:=NewCand[iSimpl].ListFaceStatus[i];
    EXTface:=NewCand[iSimpl].EXT{eDiff};
    EXTadj:=NewCand[eRecAdj.iDelaunay].EXT*eRecAdj.eBigMat;
#    Print("iSimpl=", iSimpl, " i=", i, "\n");
#    Print("EXTface=", EXTface, "\n");
#    Print("EXTadj=", EXTadj, "\n");
#    Print("eRecAdj.iDelaunay=", eRecAdj.iDelaunay, "\n");
#    Print("eRecAdj.eBigMat=", eRecAdj.eBigMat, "\n");
#    Print("ListNewSimp[eRecAdj.iDelaunay]=", NewCand[eRecAdj.iDelaunay].EXT, "\n");
    if IsSubset(Set(EXTadj), Set(EXTface))=false then
      Error("Wrong adjacency detected in TestAdj");
    fi;
  end;
  for i in [1..n+1]
  do
    eDiff:=Difference([1..n+1], [i]);
    EXTface:=eSimplex.EXT{eDiff};
    ListFind:=TRIG_FindTriangles(List(NewCand, x->x.EXT), EXTface);
    ListITrig:=List(ListFind, x->x.iTrig);
    pos:=Position(ListITrig, nbNewSimp);
    if pos=fail then
      Error("Inconsistency error");
    fi;
#    Print("i=", i, "\n");
    if Length(ListITrig)=2 then
      posB:=3 - pos;
      iTrigFind:=ListFind[posB].iTrig;
      findBigMat:=ListFind[posB].eBigMat;
      EXTimage:=NewCand[iTrigFind].EXT*findBigMat;
      if IsSubset(Set(EXTimage), Set(EXTface))=false then
        Error("More errors");
      fi;
      ListMiss:=Filtered([1..Length(EXTimage)], x->Position(EXTface, EXTimage[x])=fail);
      if Length(ListMiss)<>1 then
        Error("ListMiss should be just one element");
      fi;
      posPoint:=ListMiss[1];
#      Print("Before bunch of settings\n");
      NewCand[iTrigFind].ListFaceStatus[posPoint]:=rec(iDelaunay:=nbNewSimp, eBigMat:=Inverse(findBigMat));
#      Print("Before test 1\n");
      TestAdj(iTrigFind, posPoint);
      NewCand[nbNewSimp].ListFaceStatus[i]:=rec(iDelaunay:=iTrigFind, eBigMat:=findBigMat);
#      Print("Before test 2\n");
      TestAdj(nbNewSimp, i);
#      Print("After tests, iTrigFind=", iTrigFind, " i=", i, " posPoint=", posPoint, "\n");
    fi;
  od;
  for eRec in NewCand
  do
    for i in [1..n+1]
    do
      eRecAdj:=eRec.ListFaceStatus[i];
      if eRecAdj<>0 then
        eDiff:=Difference([1..n+1],[i]);
        EXTface:=eRec.EXT{eDiff};
        EXTadj:=NewCand[eRecAdj.iDelaunay].EXT*eRecAdj.eBigMat;
        if IsSubset(Set(EXTadj), Set(EXTface))=false then
          Error("Adjacency info badly done");
        fi;
      fi;
    od;
  od;
  return NewCand;
end;



# This function uses partial data on possible adjacencies between
# simplices in order to build the possible tilings.
# The program works in dimension <= 4 for two reasons:
# 1) In those dimension we know the possible adjacencies between simplices
# 2) In dimension >= 5 it is known that there is an infinity of potential
#    possibilities.
TRIG_EnumerationFixedDimension:=function(DSPA)
  local n, nbOrbitSimplices, ListCand, iOrbitSimpl, ListC, IsFullStructure, ListFullStructure, ListMaximal, NewListCand, FuncInsertCand, eVolume, GetCandidatesExtension, eCand, eRec, eNewCand, TestInsertionSimplex, IsEquivalentPair, GetConclusionOnPair, ListConclusionOnPairs, nbIter, ListTrig, eTrig, TheListCand;
  # The TRIG_EnumerationFixedDimension functionality.
  # The DSPA is the list of possible adjacencies between simplices.
  # This has to be proved or supposed in advance of the computation.
  #
  # Those list of possible adjacencies are known only up to dimension 4.
  # In higher dimensions we do not know those.
  # An additional problem is that in dimension > 4 there are simplices
  # of volume higher than 1 and we do not even know if higher volumes
  # are possible.
  #
  # Therefore, there is just one orbit of simplices
  Print("Begin of TRIG_EnumerationFixedDimension\n");
  n:=DSPA.n;
  #
  # During the enumeration process we have to be able
  # to check if two different simplices overlap in their
  # translation classes.
  # There is an algorithm for doing this operation but
  # it is fairly slow as we are required to find integer
  # points in polytope and such fairly hard computations.
  #
  # Thus we use a memoization stratefy in order to keep
  # conclusions on equivalences.
  # This memoization uses arithmetic equivalence so that
  # if two pairs are equivalent then the same conclusion
  # can be derived on their overlappingness.
  ListConclusionOnPairs:=[];
  # This function returns true if the pair [eTrig1, fTrig1]
  # is arithmetically equivalent to the pair [eTrig2, fTrig2]
  IsEquivalentPair:=function(eTrig1, fTrig1, eTrig2, fTrig2)
    local eElt, eMatr, eTrig1img, fTrig1img;
    for eElt in SymmetricGroup([1..n+1])
    do
      eMatr:=FindTransformation(eTrig1, eTrig2, eElt);
      eTrig1img:=eTrig1*eMatr;
      if Set(eTrig1img)<>Set(eTrig2) then
        Error("Incoherency in the construction");
      fi;
      fTrig1img:=fTrig1*eMatr;
      if TRIG_TestTranslationalEquivalence(fTrig1img, fTrig2) then
        return true;
      fi;
    od;
    return false;
  end;
  # This function function returns true if both simplices
  # do not overlap in their translation classes and false
  # if they do overlap.
  # if the conclusion is known from previous computation
  # then it is used. If not then the conclusion is computed
  # and inserted into the list of conclusions for a subsequent
  # computation.
  GetConclusionOnPair:=function(eTrig1, fTrig1)
    local nbPair, iPair, i, eTest, test, NewConcl, eTrig2, fTrig2;
    nbPair:=Length(ListConclusionOnPairs);
    for iPair in [1..nbPair]
    do
      for i in [1..2]
      do
        if i=1 then
          eTrig2:=ListConclusionOnPairs[iPair].eTrig;
          fTrig2:=ListConclusionOnPairs[iPair].fTrig;
        else
          eTrig2:=ListConclusionOnPairs[iPair].fTrig;
          fTrig2:=ListConclusionOnPairs[iPair].eTrig;
        fi;
        test:=IsEquivalentPair(eTrig1, fTrig1, eTrig2, fTrig2);
        if test=true then
#          Print("Conclusion via database\n");
          return ListConclusionOnPairs[iPair].test;
        fi;
      od;
    od;
    # This is the expensive test.
    eTest:=TRIG_TestIntersectionPairSimplices(eTrig1, fTrig1);
#    Print("Conclusion via test\n");
    if eTest.Answer=true then
      test:=false;
    else
      test:=true;
    fi;
    # The conclusion that has been reached is now stored in the
    # databse.
    NewConcl:=rec(eTrig:=eTrig1, fTrig:=fTrig1, test:=test);
    Add(ListConclusionOnPairs, NewConcl);
    Print("Now |ListConclusionOnPairs|=", Length(ListConclusionOnPairs), "\n");
    return test;
  end;
  nbOrbitSimplices:=Length(DSPA.ListOrbitSimplices);
  ListCand:=[];
  #
  # The starting point: Just one simplex.
  # We iterate over the possible orbits of simplices.
  # In the database of packings we need to keep track of various aspects:
  # ---The complete list of simplices of such packing.
  # ---For each such simplex:
  #    ---the list of vertices
  #    ---the orbit of simplex in the initial list.
  #    ---For each facet the status of each facet:
  #       0: if no adjacent simplex has been determined.
  #       rec(iDelaunay:=..., eBigMat:=...): if the adjacent simplex is known.
  #       Then iDelaunay is the index of the simplex in the list
  #            eBigMat is the matrix that maps it to the one that is adjacent.
  #    ---eBigMat: This is the matrix that maps the simplex as in DSPA to the
  #       one of the list of simplices.
  # By keeping track of all data we are able to make conclusion and do the enumeration.
  for iOrbitSimpl in [1..nbOrbitSimplices]
  do
    ListC:=[rec(iOrbitSimpl:=iOrbitSimpl, EXT:=DSPA.ListOrbitSimplices[iOrbitSimpl].eSimp, ListFaceStatus:=ListWithIdenticalEntries(n+1,0), eBigMat:=IdentityMat(n+1))];
    Add(ListCand, ListC);
  od;
  # Returns true if all the simplices have somethng adjacent on each and
  # every facet. In other words if we have a periodic TILING of the space Z^n.
  IsFullStructure:=function(eCand)
    local eRec;
    for eRec in eCand
    do
      if Position(eRec.ListFaceStatus,0)<>fail then
        return false;
      fi;
    od;
    return true;
  end;
  # We check is a simplex can be inserted into the
  # list. Our method is to simply iterate over all
  # simplices that we already have and return true
  # if all the conclusions are ok.
  TestInsertionSimplex:=function(eCand, eSimplex)
    local eRec, eTest;
    for eRec in eCand
    do
      eTest:=GetConclusionOnPair(eRec.EXT, eSimplex.EXT);
      if eTest=false then
        return false;
      fi;
    od;
    return true;
  end;
  # This function returns all the possible simplices that
  # we can insert in our existing structure. The DSPA database
  # is used for finding which simplices are feasible to consider.
  # The idea is to find the first facet that is unmatched, looked
  # at the list of possibilities in the DSPA and consider all
  # possibilities that agree with the rest of the structure.
  GetCandidatesExtension:=function(eCand)
    local eRec, pos, iOrbitSimpl, iOrbitPoint, eSingleOrbitPoint, ePerm, eMatr, ListPossibilities, eListAdjacent, eBigMat, eSimplex, eTest, eDiff, EXTsimp, EXTface, EXTadjSimp;
    for eRec in eCand
    do
      pos:=Position(eRec.ListFaceStatus, 0);
      if pos<>fail then
        eDiff:=Difference([1..n+1],[pos]);
        iOrbitSimpl:=eRec.iOrbitSimpl;
        EXTsimp:=DSPA.ListOrbitSimplices[iOrbitSimpl].eSimp*eRec.eBigMat;
        EXTface:=EXTsimp{eDiff};
        iOrbitPoint:=DSPA.ListOrbitSimplices[iOrbitSimpl].ListOrbitRepresentative[pos];
        eSingleOrbitPoint:=DSPA.ListOrbitSimplices[iOrbitSimpl].ListOrbitPoint[iOrbitPoint];
        ePerm:=RepresentativeAction(DSPA.ListOrbitSimplices[iOrbitSimpl].PermGrp, eSingleOrbitPoint.iPoint, pos, OnPoints);
        eMatr:=Image(DSPA.ListOrbitSimplices[iOrbitSimpl].phi, ePerm);
        ListPossibilities:=[];
        for eListAdjacent in eSingleOrbitPoint.TotalListAdjacent
        do
          eBigMat:=eListAdjacent.eBigMat * eMatr * eRec.eBigMat;
          EXTadjSimp:=DSPA.ListOrbitSimplices[eListAdjacent.iOrbitSimpl].eSimp*eBigMat;
          eSimplex:=rec(iOrbitSimpl:=eListAdjacent.iOrbitSimpl, EXT:=EXTadjSimp, ListFaceStatus:=ListWithIdenticalEntries(n+1,0), eBigMat:=eBigMat);
          if IsSubset(Set(eSimplex.EXT), Set(EXTface))=false then
            Error("We fail the facedness condition");
          fi;
          eTest:=TestInsertionSimplex(eCand, eSimplex);
          if eTest=true then
            Add(ListPossibilities, TRIG_AppendSimplex(eCand, eSimplex));
          fi;
        od;
        return ListPossibilities;
      fi;
    od;
  end;
  #
  # This is the iterative code:
  # ---We insert the simplices one by one in the structure
  # ---The ones which cannot be extended are inserted in the list
  #    ---of full tilings if they do tile the space
  #    ---of maximal unextendible ones if they cannot be extended but
  #       do not define tilings.
  # ---The full list of candidates is stored are stored all along the
  #    That is we first do all the packing with 2 tiles, then the ones with 3 tiles
  #    then 4 and so on.
  #    That is no tree search is done but symmetry are used to diminish
  #    the size of the search.
  ListFullStructure:=[];
  ListMaximal:=[];
  nbIter:=0;
  while(true)
  do
    nbIter:=nbIter+1;
    Print("iter=", nbIter, " |ListCand|=", Length(ListCand), "  |ListFullStructure|=", Length(ListFullStructure), " |ListMaximal|=", Length(ListMaximal), "\n");
    NewListCand:=[];
    FuncInsertCand:=function(eNewCand)
      local fNewCand, eListSimplices, eListSimplicesCan, fListSimplices, test;
      eListSimplices:=List(eNewCand, x->x.EXT);
      eListSimplicesCan:=TRIG_CanonicalizeExpression(eListSimplices);
      for fNewCand in NewListCand
      do
        fListSimplices:=List(fNewCand, x->x.EXT);
        test:=TRIG_IsEquivalentTriangulationCanonic(fListSimplices, eListSimplicesCan);
        if test<>false then
          return;
        fi;
      od;
      Add(NewListCand, eNewCand);
    end;
    for eCand in ListCand
    do
      if IsFullStructure(eCand) then
        Add(ListFullStructure, eCand);
      else
        TheListCand:=GetCandidatesExtension(eCand);
        if Length(TheListCand)=0 then
          Add(ListMaximal, eCand);
        else
          for eNewCand in TheListCand
          do
            FuncInsertCand(eNewCand);
          od;
        fi;
      fi;
    od;
    if Length(NewListCand)=0 then
      break;
    fi;
    ListCand:=ShallowCopy(NewListCand);
  od;
  Print("End of TRIG_EnumerationFixedDimension\n");
  Print("|ListFullStructure|=", Length(ListFullStructure), " |ListMaximal|=", Length(ListMaximal), "\n");
  return rec(ListFullStructure:=ListFullStructure, ListMaximal:=ListMaximal);
end;



TRIG_GetCtypeHedgehobConfiguration:=function(ListTrig)
  local ListVect, nbTrig, n, iTrig, eTrig, i, j, eDiff;
  ListVect:=[];
  nbTrig:=Length(ListTrig);
  n:=Length(ListTrig[1])-1;
  for iTrig in [1..nbTrig]
  do
    eTrig:=ListTrig[iTrig];
    for i in [1..n+1]
    do
      for j in [i+1..n+1]
      do
        eDiff:=eTrig[i]{[2..n+1]} - eTrig[j]{[2..n+1]};
        Add(ListVect, eDiff);
        Add(ListVect, -eDiff);
      od;
    od;
  od;
  return Set(ListVect);
end;
